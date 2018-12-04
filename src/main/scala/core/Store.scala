import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

abstract class Store[Addr : Address, Abs : JoinLattice] {
  /** Gets all the keys of the store */
  def keys: Iterable[Addr]
  /** Checks if a predicate is true for all elements of the store */
  def forall(p: ((Addr, Abs)) => Boolean): Boolean
  /** Looks up a value in the store */
  def lookup(a: Addr): Option[Abs]
  def lookupMF(a: Addr): MayFail[Abs] = lookup(a) match {
    case Some(a) => a
    case None => UnboundAddress(a.toString)
  }
  /** Looks up a  value in the store, or return bottom if it's not there */
  def lookupBot(a: Addr): Abs
  /** Add a new entry in the store */
  def extend(a: Addr, v: Abs): Store[Addr, Abs]
  /** Update an entry in the store */
  def update(a: Addr, v: Abs): Store[Addr, Abs]
  /** Tries to update an address if it's already mapped into the store. Otherwise, extend the store */
  def updateOrExtend(a: Addr, v: Abs): Store[Addr, Abs]
  /** Joins two stores together */
  def join(that: Store[Addr, Abs]): Store[Addr, Abs]
  /** Checks whether this store subsumes another store */
  def subsumes(that: Store[Addr, Abs]): Boolean
  /** Returns a store containing items that differ between the two stores */
  def diff(that: Store[Addr, Abs]): Store[Addr, Abs]
  /** Returns a delta of the changes made on this store. None if the store doesn't support store deltas */
  def delta: Option[Map[Addr, Abs]] = None
  /** Add a delta to the store. This clears the current delta */
  def addDelta(delta: Map[Addr, Abs]): Store[Addr, Abs] = throw new Exception("Store doesn't support deltas")
  /** Returns the cardinality of each lattice element of this store */
  def cardinalities(withPrimitives: Boolean = false): Map[Addr, Cardinality] =
    keys
      .filter(a => withPrimitives || !Address[Addr].isPrimitive(a))
      .foldLeft(Map[Addr, Cardinality]())((acc, a) => lookup(a) match {
        case Some(v) => acc + (a -> JoinLattice[Abs].cardinality(v))
        case None => acc /* should not happen */
      })
}

/** Basic store with no fancy feature, just a map from addresses to values */
case class BasicStore[Addr : Address, Abs : JoinLattice](content: Map[Addr, Abs], hc: Int = 0) extends Store[Addr, Abs] {
  override def toString = content.filterKeys(a => !Address[Addr].isPrimitive(a)).toString
  def keys = content.keys
  def forall(p: ((Addr, Abs)) => Boolean) = content.forall({ case (a, v) => p(a, v) })
  def lookup(a: Addr) = content.get(a)
  def lookupBot(a: Addr) = content.get(a).getOrElse(JoinLattice[Abs].bottom)
  def extend(a: Addr, v: Abs) = content.get(a) match {
    case None => this.copy(content = content + (a -> v), hc = hc + v.hashCode())
    case Some(v2) =>
      val updatedVal = JoinLattice[Abs].join(v2, v)
      val updatedHC = hc - v2.hashCode() + updatedVal.hashCode()
      this.copy(content = content + (a -> updatedVal), hc = updatedHC)
  }
  def update(a: Addr, v: Abs) = extend(a, v)
  def updateOrExtend(a: Addr, v: Abs) = extend(a, v)
  def join(that: Store[Addr, Abs]) = ???
  def subsumes(that: Store[Addr, Abs]) =
    that.forall((binding: (Addr, Abs)) => JoinLattice[Abs].subsumes(lookupBot(binding._1), binding._2))
  def diff(that: Store[Addr, Abs]) = ???
  override def hashCode = hc
}

case class RefCountingStore[Addr:Address, Abs:JoinLattice]
  (content: Map[Addr,(Abs,Set[Addr])],
   in: Map[Addr,(Int,Set[Addr])] = Map[Addr,(Int,Set[Addr])]().withDefaultValue(0,Set[Addr]()),
   ds: DisjointSet[Addr] = DisjointSet[Addr](),
   hc: Int = 0)
extends Store[Addr,Abs] {

  type AddrRefs = (Int,Set[Addr])
  type AddrCount = Map[Addr,AddrRefs]
  type AddrQueue = scala.collection.mutable.Queue[Addr]

  def keys = content.keys
  def forall(p: ((Addr,Abs)) => Boolean) = content.forall(n => p(n._1,n._2._1))
  def lookup(a: Addr) = content.get(a).map(_._1)
  def lookupBot(a: Addr) = lookup(a).getOrElse(JoinLattice[Abs].bottom)

  private def incRootRef(a: Addr, currentIn: AddrCount, currentDS: DisjointSet[Addr]) = {
    val cls = currentDS.find(a)
    val (counts,refs) = currentIn(cls)
    currentIn + (cls -> (counts+1,refs))
  }

  private def incEdgeRef(from: Addr, to: Addr, currentIn: AddrCount, currentDS: DisjointSet[Addr]) = {
    val cls = currentDS.find(to)
    val (counts,refs) = currentIn(cls)
    currentIn + (cls -> (counts,refs+from))
  }

  def incRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] =
    this.copy(in = addrs.foldLeft(in)((acc,ref) => incRootRef(ref,acc,this.ds)))

  private def deallocRef(update: AddrRefs => AddrRefs, to: Addr, currentIn: AddrCount, toDealloc: AddrQueue): AddrCount = {
    val cls = ds.find(to)
    val current = currentIn(cls)
    val updated@(count, refs) = update(current)
    if (count == 0 && refs.isEmpty) {
      toDealloc.enqueue(cls)
      currentIn
    } else {
      currentIn + (cls -> updated)
    }
  }

  private def deallocRootRef(target: Addr, currentIn: AddrCount, toDealloc: AddrQueue): AddrCount
    = deallocRef({ case (counts,refs) => (counts-1,refs) }, target, currentIn, toDealloc)

  private def deallocEdgeRef(from: Addr, to: Addr, currentIn: AddrCount, toDealloc: AddrQueue): AddrCount
    = deallocRef({ case (counts,refs) => (counts,refs-from) }, to, currentIn, toDealloc)


  private def deallocSCC(cls: Addr, currentIn: AddrCount, toDealloc: AddrQueue, toDelete: AddrQueue): AddrCount = {

    // Optimize deallocSCC for SCC components with a single node
    // (since in practice, most of the times this will be the case)
    if (ds.singleton(cls)) {
      toDelete.enqueue(cls)
      val succs = content(cls)._2
      val updatedIn = succs.foldLeft(currentIn)((acc,ref) => deallocEdgeRef(cls,ref,acc,toDealloc))
      return updatedIn
    }

    // In the more general, but also rare case the |SCC\ > 1:
    // - All internal edges traversed and added to toDelete as well
    // - All external edges are deallocated using ``deallocRef``
    var updatedIn = currentIn
    var marked = scala.collection.mutable.Set[Addr](cls)
    var addrs = scala.collection.mutable.Queue[Addr](cls)
    while (addrs.nonEmpty) {
      val addr = addrs.dequeue
      toDelete.enqueue(addr)
      val succs = content(addr)._2
      val (internalSuccs,externalSuccs) = succs.partition(ds.find(_) == cls)
      internalSuccs.filter(marked.add(_)) foreach { addrs.enqueue(_) }
      externalSuccs foreach { succ => updatedIn = deallocEdgeRef(addr,succ,updatedIn,toDealloc) }
    }
    updatedIn
  }

  def decRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] = {

    val toDelete = scala.collection.mutable.Queue[Addr]()
    val toDealloc = scala.collection.mutable.Queue[Addr]()
    val deallocated = scala.collection.mutable.Set[Addr]()

    // For every addr in addrs:
    // - decrement the reference count of the corresponding scc
    // - if the SCC can be deallocated, enqueue it in toDealloc
    var updatedIn = addrs.foldLeft(this.in)((acc,ref) => deallocRootRef(ref,acc,toDealloc))

    // Deallocate a SCC in every iteration
    while (toDealloc.nonEmpty) {
      val cls = toDealloc.dequeue
      if (deallocated.add(cls)) {
        updatedIn = deallocSCC(cls, updatedIn, toDealloc, toDelete)
      }
    }

    val updatedHc = toDelete.foldLeft(this.hc)((acc,ref) => acc - content(ref)._1.hashCode())
    RefCountingStore(content -- toDelete, updatedIn -- toDelete, ds -- toDelete, updatedHc)
  }

  def extend(adr: Addr, v: Abs): RefCountingStore[Addr,Abs] = content.get(adr) match {
    case None =>
      val vrefs = JoinLattice[Abs].references(v)
      val updatedContent = this.content + (adr -> (v,vrefs))
      val updatedIn = vrefs.foldLeft(this.in)((acc,ref) => incEdgeRef(adr,ref,acc,this.ds))
      val updatedHc = this.hc + v.hashCode()
      this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
    case Some((u,_)) if JoinLattice[Abs].subsumes(u,v) =>
      this
    case Some((u,urefs)) =>
      val vrefs = JoinLattice[Abs].references(v)
      val updatedVal = JoinLattice[Abs].join(u,v)
      val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
      val ((updatedDs,updatedIn), updatedRefs) = vrefs.foldLeft(((this.ds, this.in), urefs))((acc,ref) => {
        if (urefs.contains(ref)) { acc } else { (detectCycle(adr,ref,acc._1), acc._2 + ref) }
      })
      val updatedContent = this.content + (adr -> (updatedVal, updatedRefs))
      RefCountingStore(updatedContent, updatedIn, updatedDs, updatedHc)
  }

  private def detectCycle(from: Addr, to: Addr, current: (DisjointSet[Addr],AddrCount)): (DisjointSet[Addr],AddrCount) = {

    // Optimization for a common case (trivial self-loops)
    if (from == to) {
      return current
    }

    val (currentDs, currentIn) = current
    var updatedDs = currentDs
    var incomingRoots = 0
    var incomingRefs = Set[Addr]()
    var visited = Set[Addr]()

    val target = currentDs.find(to)
    def reachable(current: Addr): Boolean = {
      val cls = currentDs.find(current)
      if (cls == target) {
        true
      } else if (visited(cls)) {
        updatedDs.equiv(cls, target)
      } else {
        visited = visited + cls
        val (count,refs) = currentIn(cls)
        val (canReach, cantReach) = refs.partition(reachable)
        if (canReach.nonEmpty) {  // current node can reach target
          updatedDs = updatedDs.merge(cls, target)
          incomingRefs = incomingRefs ++ cantReach
          incomingRoots = incomingRoots + count
          true
        } else {                  // current node can't reach target
          false
        }
      }
    }

    if (reachable(from)) {
      val updatedCls = updatedDs.find(target)
      val (extraCount,extraRefs) = currentIn(target)
      val updatedCounts = incomingRoots + extraCount
      val updatedRefs = incomingRefs ++ extraRefs
      val updatedIn = currentIn + (updatedCls -> (updatedCounts, updatedRefs))
      (updatedDs, updatedIn)
    } else {
      (currentDs, incEdgeRef(from,to,currentIn,currentDs))
    }
  }

  def update(a: Addr, v: Abs): RefCountingStore[Addr,Abs] = extend(a,v)
  def updateOrExtend(a: Addr, v: Abs): RefCountingStore[Addr,Abs] = extend(a,v)

  /* TODO */

  def join(that: Store[Addr,Abs]) = throw new Exception("NYI: RefCountingStore.join(Store[Addr,Abs])")
  def subsumes(that: Store[Addr,Abs]) = throw new Exception("NYI: RefCountingStore.subsumes(Store[Addr,Abs])")
  def diff(that: Store[Addr,Abs]) = throw new Exception("NYI: RefCountingStore.diff(Store[Addr,Abs])")

  /* PERFORMANCE OPTIMIZATION */

  override def equals(that: Any): Boolean = that match {
    case store: RefCountingStore[Addr,Abs] => this.hc == store.hc && this.content == store.content
    case _ => false
  }

  override def hashCode = hc

  /* DEBUGGING */

  private def transclo(addrs: Set[Addr]): Set[Addr] = {
    var transclo = Set[Addr]()
    var todo = addrs.toList
    while (todo.nonEmpty) {
      val next = todo.head
      todo = todo.tail
      if(!transclo.contains(next)) {
        transclo += next
        todo ++= content(next)._2
      }
    }
    transclo
  }

  private def transclo(adr: Addr): Set[Addr] = transclo(Set(adr))

  def garbage(roots: Set[Addr]): Set[Addr] = {
    val marked = transclo(roots)
    val unmarked = content--marked
    unmarked.keys.toSet
  }
}

/* WARNING: For efficiency, we currently assume that: refs(join(u,v)) = refs(u) U refs(v), although this assumption can easily be avoided */
case class GCStore[Addr : Address, Abs : JoinLattice]
  (content: Map[Addr,Abs],
   refs: Map[Addr,Set[Addr]] = Map[Addr,Set[Addr]]().withDefaultValue(Set()))
  extends Store[Addr,Abs] {

    def keys = content.keys
    def forall(p: ((Addr,Abs)) => Boolean) = content.forall(p)
    def lookup(a: Addr) = content.get(a)
    def lookupBot(a: Addr) = content.get(a).getOrElse(JoinLattice[Abs].bottom)

    def update(a: Addr, v: Abs) = extend(a,v)
    def updateOrExtend(a: Addr, v: Abs) = extend(a,v)

    private def mark(adr: Addr, marked: Set[Addr]): Set[Addr] =
      if (marked.contains(adr)) {
        marked
      } else {
        refs(adr).foldLeft(marked + adr)((acc,ref) => mark(ref,acc))
      }

    private def sweep(marked: Set[Addr]): GCStore[Addr,Abs] = {
      val updatedContent = content.filterKeysStrict(marked)
      val updatedRefs = refs.filterKeysStrict(marked).withDefaultValue(Set())
      GCStore(updatedContent,updatedRefs)
    }

    def collect(roots: Set[Addr]): GCStore[Addr,Abs] = {
      val marked = roots.foldLeft(Set[Addr]())((acc,ref) => mark(ref,acc))
      sweep(marked)
    }

    def extend(adr: Addr, v: Abs) = {
      val updatedAdrRefs = refs(adr) ++ JoinLattice[Abs].references(v)
      val updatedValue = if (content.contains(adr)) { JoinLattice[Abs].join(content(adr),v) } else { v }
      GCStore(content + (adr -> updatedValue), refs + (adr -> updatedAdrRefs))
    }

    /* TODO */

    def join(that: Store[Addr,Abs]) = throw new Exception("NYI: GCStore.join(Store[Addr,Abs])")
    def subsumes(that: Store[Addr,Abs]) = throw new Exception("NYI: GCStore.subsumes(Store[Addr,Abs])")
    def diff(that: Store[Addr,Abs]) = throw new Exception("NYI: GCStore.diff(Store[Addr,Abs])")

    /* PERFORMANCE OPTIMIZATION */

    override def equals(that: Any): Boolean = that match {
      case store: GCStore[Addr,Abs] => this.content == store.content
      case _ => false
    }

    lazy val storedHashCode = content.hashCode
    override def hashCode = storedHashCode
}

/** Store that combines a default read-only store with a writable store */
case class CombinedStore[Addr : Address, Abs : JoinLattice](ro: Store[Addr, Abs], w: Store[Addr, Abs]) extends Store[Addr, Abs] {
  def keys = ro.keys.toSet ++ w.keys.toSet
  def forall(p: ((Addr, Abs)) => Boolean) = keys.forall(a => lookup(a) match {
    case Some(v) => p((a, v))
    case None => throw new Exception(s"shouldn't happen: an existing key is not bound in the store (key: $a, store: $this)")
  })
  def lookup(a: Addr) = w.lookup(a).orElse(ro.lookup(a))
  def lookupBot(a: Addr) = w.lookup(a).getOrElse(ro.lookupBot(a))
  def extend(a: Addr, v: Abs) = this.copy(w = w.extend(a, v))
  def update(a: Addr, v: Abs) = updateOrExtend(a, v)
  def updateOrExtend(a: Addr, v: Abs) = this.copy(w = w.updateOrExtend(a, v))
  def join(that: Store[Addr, Abs]) = throw new Exception("CombinedStore does not support join")
  def subsumes(that: Store[Addr, Abs]) =
    that.forall((binding: (Addr, Abs)) => JoinLattice[Abs].subsumes(lookupBot(binding._1), binding._2))
  def diff(that: Store[Addr, Abs]) = throw new Exception("CombinedStore does not support diff")
}

/** A store that supports store deltas. Many operations are not implemented because they are not needed. */
case class DeltaStore[Addr : Address, Abs : JoinLattice](content: Map[Addr, Abs], d: Map[Addr, Abs]) extends Store[Addr, Abs] {
  def this() = this(Map(), Map())
  override def toString = content.filterKeys(a => !Address[Addr].isPrimitive(a)).toString
  def keys = content.keys
  def forall(p: ((Addr, Abs)) => Boolean) = content.forall({ case (a, v) => p(a, v) })
  def lookup(a: Addr) = d.get(a).orElse(content.get(a)) /* information in the delta should always be as broad as the information in the store itself */
  def lookupBot(a: Addr) = d.get(a).orElse(content.get(a)).getOrElse(JoinLattice[Abs].bottom)
  def extend(a: Addr, v: Abs) = d.get(a) match {
    case Some(v2) => this.copy(d = d + (a -> JoinLattice[Abs].join(v2, v)))
    case None => content.get(a) match {
      case None => this.copy(d = d + (a -> v))
      case Some(v2) if v2 == v || JoinLattice[Abs].subsumes(v2, v) => this
      case Some(v2) => this.copy(d = d + (a -> JoinLattice[Abs].join(v2, v)))
    }
  }
  def update(a: Addr, v: Abs) = extend(a, v)
  def updateOrExtend(a: Addr, v: Abs) = extend(a, v)
  def join(that: Store[Addr, Abs]) = if (that.isInstanceOf[DeltaStore[Addr, Abs]]) {
    throw new Exception("DeltaStore does not support join")
  } else {
    throw new Exception(s"Incompatible stores: ${this.getClass.getSimpleName} and ${that.getClass.getSimpleName}")
  }
  def subsumes(that: Store[Addr, Abs]) = throw new Exception("DeltaStore does not support subsumes")
  def diff(that: Store[Addr, Abs]) = throw new Exception("DeltaStore does not support diff")
  override def delta = Some(d)
  override def addDelta(delta: Map[Addr, Abs]) = this.copy(content = content |+| delta, d = Map())
}

case class CountingStore[Addr : Address, Abs : JoinLattice](content: Map[Addr, (Count, Abs)]) extends Store[Addr, Abs] {
  override def toString = content.filterKeys(a => !Address[Addr].isPrimitive(a)).toString
  def keys = content.keys
  def forall(p: ((Addr, Abs)) => Boolean) = content.forall({ case (a, (_, v)) => p(a, v) })
  def lookup(a: Addr) = content.get(a).map(_._2)
  def lookupBot(a: Addr) = content.get(a).map(_._2).getOrElse(JoinLattice[Abs].bottom)
  def extend(a: Addr, v: Abs) = content.get(a) match {
    case None => this.copy(content = content + (a -> (CountOne, v)))
    case Some((n, v2)) => this.copy(content = content + (a -> (n.inc, JoinLattice[Abs].join(v2, v))))
  }
  def update(a: Addr, v: Abs) = content.get(a) match {
    case None => throw new RuntimeException("Updating store at an adress not used")
    case Some((CountOne, _)) => this.copy(content = content + (a -> (CountOne, v)))
    case _ => extend(a, v)
  }
  def updateOrExtend(a: Addr, v: Abs) = content.get(a) match {
    case None => extend(a, v)
    case Some(_) => update(a, v)
  }
  def join(that: Store[Addr, Abs]) =
    if (that.isInstanceOf[CountingStore[Addr, Abs]]) {
      this.copy(content = content |+| that.asInstanceOf[CountingStore[Addr, Abs]].content)
    } else {
      throw new Exception(s"Incompatible stores: ${this.getClass.getSimpleName} and ${that.getClass.getSimpleName}")
    }
  def subsumes(that: Store[Addr, Abs]) =
    that.forall((binding: (Addr, Abs)) => JoinLattice[Abs].subsumes(lookupBot(binding._1), binding._2))
  def diff(that: Store[Addr, Abs]) =
    if (that.isInstanceOf[CountingStore[Addr, Abs]]) {
      val other = that.asInstanceOf[CountingStore[Addr, Abs]]
      this.copy(content = content.filter({ case (a, (n, v)) => other.content.get(a) match {
        case Some((n2, v2)) => n != n2 && v != v2
        case None => true
      }}))
    } else {
      this.copy(content = content.filter({ case (a, v) => that.lookupBot(a) != v}))
    }
}

object Store {
  def empty[Addr : Address, Abs : JoinLattice]: Store[Addr, Abs] = empty[Addr, Abs](JoinLattice[Abs].counting)
  def empty[Addr : Address, Abs : JoinLattice](counting: Boolean): Store[Addr, Abs] = if (counting) {
    CountingStore(Map())
  } else {
    BasicStore(Map())
  }
  def initial[Addr : Address, Abs : JoinLattice](values: Iterable[(Addr, Abs)]): Store[Addr, Abs] = if (JoinLattice[Abs].counting) {
    CountingStore(values.map({ case (a, v) => (a, (CountOne, v)) }).toMap)
  } else {
    BasicStore(values.toMap)
  }
  def refCountStore[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): RefCountingStore[Addr,Abs] = {
    val content = values.toMap.map({ case (k,v) => (k,(v,JoinLattice[Abs].references(v))) })
    new RefCountingStore[Addr,Abs](content)
  }
  def gcStore[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): GCStore[Addr,Abs] = new GCStore[Addr,Abs](values.toMap)

  implicit def monoid[Addr : Address, Abs : JoinLattice]: Monoid[Store[Addr, Abs]] =
    new Monoid[Store[Addr, Abs]] {
      def append(s1: Store[Addr, Abs], s2: => Store[Addr, Abs]): Store[Addr, Abs] = s1.join(s2)
      def zero: Store[Addr, Abs] = empty[Addr, Abs]
    }
}
