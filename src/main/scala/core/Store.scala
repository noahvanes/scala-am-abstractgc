import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict

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

/* WARNING: For efficiency, we currently assume that: refs(join(u,v)) = refs(u) U refs(v), although this assumption can easily be avoided */
case class RefCountingStore[Addr : Address, Abs : JoinLattice](content: Map[Addr,Abs],
                                                               counts: Map[Addr,Int] = Map[Addr,Int]().withDefaultValue(0),
                                                               refs: Map[Addr,Set[Addr]] = Map[Addr,Set[Addr]]().withDefaultValue(Set()),
                                                               hc: Int = 0) extends Store[Addr,Abs] {

    def keys = content.keys
    def forall(p: ((Addr,Abs)) => Boolean) = content.forall(p)
    def lookup(a: Addr) = content.get(a)
    def lookupBot(a: Addr) = content.get(a).getOrElse(JoinLattice[Abs].bottom)

    def incRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] =
      this.copy(counts = addrs.foldLeft(counts)((acc,ref) => acc + (ref -> (acc(ref) + 1))))

    def decRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] = {
      val (updatedCounts,deleted) = addrs.foldLeft((counts,List[Addr]()))((acc,ref) => decRefUpdate(ref,acc._1,acc._2))
      val updatedHC = deleted.foldLeft(hc)((acc,ref) => acc - content(ref).hashCode())
      this.copy(content=content--deleted, counts=updatedCounts--deleted, refs=refs--deleted, hc=updatedHC)
    }

    def decRefUpdate(adr: Addr, counts: Map[Addr,Int], deleted: List[Addr]): (Map[Addr,Int],List[Addr]) = {
      val newCount = counts(adr) - 1
      if (newCount == 0) {
        refs(adr).foldLeft((counts, adr :: deleted))((acc,ref) => decRefUpdate(ref,acc._1,acc._2))
      } else {
        (counts + (adr -> newCount), deleted)
      }
    }

    def extend(adr: Addr, v: Abs): RefCountingStore[Addr,Abs] = content.get(adr) match {
      case None => {
        val vRefs = JoinLattice[Abs].references(v) - adr
        RefCountingStore(content+(adr->v), vRefs.foldLeft(counts)((acc,ref)=>acc+(ref->(counts(ref)+1))), refs+(adr->vRefs), hc+v.hashCode())
      }
      case Some(u) if JoinLattice[Abs].subsumes(u,v) =>
        this
      case Some(u) => {
        val uRefs = refs(adr)
        val vRefs = JoinLattice[Abs].references(v) - adr
        val updatedVal = JoinLattice[Abs].join(u,v)
        val updatedContent = content + (adr -> updatedVal)
        val updatedHC = hc - u.hashCode() + updatedVal.hashCode()
        val (updatedCounts,updatedAdrRefs) = vRefs.foldLeft((counts,uRefs))((acc,ref) => {
          if (uRefs.contains(ref)) { acc } else { (acc._1 + (ref->(counts(ref)+1)), acc._2 + ref) }
        })
        RefCountingStore(updatedContent, updatedCounts, refs + (adr->updatedAdrRefs), updatedHC)
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
      while (!todo.isEmpty) {
        val next = todo.head
        todo = todo.tail
        if(!transclo.contains(next)) {
          transclo += next
          todo ++= refs(next)
        }
      }
      return transclo
    }

    private def transclo(adr: Addr): Set[Addr] = transclo(Set(adr))

    def garbage(roots: Set[Addr]): Set[Addr] = {
      val marked = transclo(roots)
      val unmarked = content--marked
      unmarked.keys.toSet
    }

    def reachable(from: Addr, to: Addr): Boolean = transclo(from).contains(to)

    def calcCounts(external: Map[Addr,Int]): Map[Addr,Int] = {
      var counts = external
      refs.foreach(p => {
        val addrs = p._2
        addrs.foreach(addr => {
          counts = counts.updated(addr, counts(addr) + 1)
        })
      })
      return counts
    }

    def toFile(path: String, roots: Set[Addr]) = {
      val store = this
      implicit val addrNode = new GraphNode[Addr,Unit] {
        override def label(adr: Addr): String = s"$adr"
        override def tooltip(adr: Addr): String = s"${store.counts(adr)}"
        override def color(adr: Addr): Color = if (roots.contains(adr)) { Colors.Green } else { Colors.White }
      }
      val initG = content.keys.foldLeft(Graph.empty[Addr,Unit,Unit])((acc,adr) => if (Address[Addr].isPrimitive(adr)) { acc } else { acc.addNode(adr) })
      val fullG = content.keys.foldLeft(initG)((acc,adr) => acc.addEdges(refs(adr).map(succ => (adr,(),succ))))
      GraphDOTOutput.toFile(fullG,())(path)
    }

    def toPng(path: String, roots: Set[Addr]): Unit = {
      import sys.process._
    import java.io.File
      val tempFile = "temp.dot"
      toFile(tempFile, roots)
      s"dot -Tpng ${tempFile} -o ${path}".!
      new File(tempFile).delete()
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
  def refCountStore[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): RefCountingStore[Addr,Abs] = new RefCountingStore[Addr,Abs](values.toMap)
  def gcStore[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): GCStore[Addr,Abs] = new GCStore[Addr,Abs](values.toMap)

  implicit def monoid[Addr : Address, Abs : JoinLattice]: Monoid[Store[Addr, Abs]] =
    new Monoid[Store[Addr, Abs]] {
      def append(s1: Store[Addr, Abs], s2: => Store[Addr, Abs]): Store[Addr, Abs] = s1.join(s2)
      def zero: Store[Addr, Abs] = empty[Addr, Abs]
    }
}
