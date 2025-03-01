import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet
import core.Tarjan

case class RefCountingStore[Addr:Address, Abs:JoinLattice]
  (content: Map[Addr,(Abs,Count,Set[Addr])],
        in: Map[Addr,(Int,Set[Addr])] = Map[Addr,(Int,Set[Addr])]().withDefaultValue(0,Set[Addr]()),
        ds: DisjointSet[Addr] = DisjointSet[Addr](),
  rootRefs: Map[Addr, Int] = Map[Addr, Int]().withDefaultValue(0),
   toCheck: Set[Addr] = Set[Addr](),
        hc: Int = 0)
extends Store[Addr,Abs] {

  type AddrRefs  = (Int, Set[Addr])
  type AddrCount = Map[Addr, AddrRefs]
  type RootRefs  = Map[Addr, Int]

  def keys = content.keys
  def forall(p: ((Addr,Abs)) => Boolean) = content.forall(n => p(n._1,n._2._1))
  def lookup(a: Addr) = content.get(a).map(_._1)
  def lookupBot(a: Addr) = lookup(a).getOrElse(JoinLattice[Abs].bottom)

  private def incRootRef(a: Addr, currentIn: AddrCount, currentDS: DisjointSet[Addr], n: Int = 1) = {
    val cls = currentDS.find(a)
    val (counts, refs) = currentIn(cls)
    currentIn + (cls -> (counts + n, refs))
  }

  private def incEdgeRef(from: Addr, to: Addr, currentIn: AddrCount, currentDS: DisjointSet[Addr]) = {
    val cls = currentDS.find(to)
    val (counts, refs) = currentIn(cls)
    currentIn + (cls -> (counts, refs + from))
  }

  def incRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] = Main.timeGC {
    val (updatedIn, updatedRoots) = addrs.foldLeft((this.in, this.rootRefs)) {
      case ((accIn, accRefs), ref) => (incRootRef(ref, accIn, this.ds), accRefs + (ref -> (accRefs(ref) + 1))) 
    }
    this.copy(in = updatedIn, rootRefs = updatedRoots)
  }

  private def decRef(update: AddrRefs => AddrRefs, cls: Addr, currentIn: AddrCount): (Boolean, AddrCount) = {
    val current = currentIn(cls)
    val updated@(count, refs) = update(current)
    if (count == 0 && refs.isEmpty) {
      (true, currentIn - cls)
    } else {
      (false, currentIn + (cls -> updated))
    }
  }

  private def decRootRef(target: Addr, currentIn: AddrCount): (Boolean, AddrCount)
    = decRef({ case (counts,refs) => (counts-1,refs) }, target, currentIn)

  private def decEdgeRef(from: Addr, to: Addr, currentIn: AddrCount): (Boolean, AddrCount)
    = decRef({ case (counts,refs) => (counts,refs-from) }, to, currentIn)

  private def decRootRefs(addrs: Iterable[Addr], currentIn: AddrCount, currentRoots: RootRefs, currentToCheck: Set[Addr]): (AddrCount, RootRefs, Set[Addr]) =
      addrs.foldLeft((currentIn, currentRoots, currentToCheck)) { 
        case ((accIn, accRoots, accToCheck), addr) =>
            val cls = ds.find(addr)
            val (isGarbage, accIn2) = decRootRef(cls, accIn)
            (accIn2, remRootRef(addr, accRoots), if (isGarbage) (accToCheck + cls) else accToCheck)
      }

  private def decEdgeRefs(from: Addr, addrs: Iterable[Addr], currentIn: AddrCount, currentToCheck: Set[Addr]): (AddrCount, Set[Addr]) =
    addrs.foldLeft((currentIn, currentToCheck)) { 
        case ((accIn, accToCheck), addr) =>
            val cls = ds.find(addr)
            val (isGarbage, accIn2) = decEdgeRef(from, cls, accIn)
            (accIn2, if (isGarbage) (accToCheck + cls) else accToCheck)
    }

  private def remRootRef(addr: Addr, currentRefs: RootRefs): RootRefs = {
    val updated = currentRefs(addr) - 1
    if (updated == 0) {
      currentRefs - addr 
    } else {
      currentRefs + (addr -> updated)
    }
  }

  def decRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] = Main.timeGC {
    val (updatedIn, updatedRoots, updatedToCheck) = decRootRefs(addrs, this.in, this.rootRefs, this.toCheck)
    this.copy(in = updatedIn, rootRefs = updatedRoots, toCheck = updatedToCheck)
  }

  def collect(): RefCountingStore[Addr,Abs] = Main.timeGC {
    var toDealloc       = toCheck.map(ds.find).filterNot(in.contains).toList 
    var updatedContent  = this.content 
    var updatedIn       = this.in 
    var updatedHc       = this.hc 
    var updatedDs       = this.ds 
    while (toDealloc.nonEmpty) {
        val scc = toDealloc.head
        toDealloc = toDealloc.tail 
        // DEALLOC THE SCC 
        val addrs = updatedDs.allOf(scc)
        addrs.foreach { addr => 
          val (vlu, _, succs) = updatedContent(addr)
          updatedContent = updatedContent - addr 
          updatedHc = updatedHc - vlu.hashCode()
          val sccs = succs.map(ds.find) - scc 
          updatedIn = sccs.foldLeft(updatedIn) { 
            (accIn, cls) =>
              val (isGarbage, accIn2) = decEdgeRef(addr, cls, accIn)
              if (isGarbage) { toDealloc = cls :: toDealloc }
              accIn2
          }
        }
        updatedDs = updatedDs -- addrs  
    }
    RefCountingStore(updatedContent, updatedIn, updatedDs, rootRefs, Set.empty, updatedHc)
  }

  def extend(adr: Addr, v: Abs): RefCountingStore[Addr,Abs] = content.get(adr) match {
      case None =>
        val vrefs = JoinLattice[Abs].references(v)
        val updatedContent = this.content + (adr -> (v, CountOne, vrefs))
        val updatedIn = vrefs.foldLeft(this.in)((acc, ref) => {
          if (ref == adr) { acc } else Main.timeGC { incEdgeRef(adr, ref, acc, this.ds) }
        })
        val updatedHc = this.hc + v.hashCode()
        this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
      case Some((u, count, urefs)) if JoinLattice[Abs].subsumes(u, v) =>
          if (count == CountInfinity) {
              this
          } else {
              this.copy(content = content + (adr -> (u, CountInfinity, urefs))) 
          }
      case Some((u, _, urefs)) =>
        val vrefs = JoinLattice[Abs].references(v)
        val updatedVal = JoinLattice[Abs].join(u, v)
        val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
        val ((updatedDs, updatedIn), updatedRefs) = vrefs.foldLeft(((this.ds, this.in), urefs)) { 
          (acc, ref) =>
            if (urefs.contains(ref)) { acc } else { (Main.timeGC { detectCycle(adr, ref, acc._1) }, acc._2 + ref) }
        }
        val updatedContent = this.content + (adr -> (updatedVal, CountInfinity, updatedRefs))
        RefCountingStore(updatedContent, updatedIn, updatedDs, rootRefs, toCheck, updatedHc)
  }

  def update(adr: Addr, v: Abs): RefCountingStore[Addr,Abs] =
    content.get(adr) match {
        case None => 
            throw new RuntimeException("Updating store at an adress not used")
        case Some((u, CountOne, urefs)) => // STRONG UPDATE 
            val vrefs = JoinLattice[Abs].references(v)
            val updatedHc = this.hc - u.hashCode() + v.hashCode()
            val updatedContent = this.content + (adr -> (v, CountOne, vrefs))
            Main.timeGC {
              val removedRefs = urefs -- vrefs 
              val addedRefs   = vrefs -- urefs
              // updating DS and IN
              lazy val scc = ds.find(adr)
              lazy val addrs = ds.allOf(scc).toSet
              var updatedDs = this.ds
              var updatedIn = this.in
              var updatedToCheck = this.toCheck
              // 1) removed references
              val (internalRemRefs, externalRemRefs) = removedRefs.partition(updatedDs.find(_) == scc)
              //// 1a) external
              val updatedRem = decEdgeRefs(adr, externalRemRefs, updatedIn, updatedToCheck)
              updatedIn      = updatedRem._1
              updatedToCheck = updatedRem._2
              //// 1b) check removed references inside the SCC
              if (internalRemRefs.nonEmpty && addrs.size > 1) {
                updatedDs = updatedDs -- addrs
                updatedDs = Tarjan(addrs, ref => updatedContent(ref)._3.filter(addrs), updatedDs) 
                if (updatedToCheck.contains(scc)) {
                  updatedToCheck -= scc
                  updatedToCheck ++= addrs.map(updatedDs.find)
                }
                // external refs ...
                val (_, sccRefs) = updatedIn(scc)
                updatedIn -= scc
                sccRefs.foreach { ref =>   // ... from other addresses
                  updatedContent(ref)._3
                                    .filter(addrs)
                                    .foreach { a => updatedIn = incEdgeRef(ref, a, updatedIn, updatedDs) }
                }
                addrs.foreach { addr =>   // ... from the roots
                  rootRefs.get(addr).foreach { count => 
                    updatedIn = incRootRef(addr, updatedIn, updatedDs, count)
                  }
                }
                // internal refs
                addrs.foreach { addr =>
                  val addrCls = updatedDs.find(addr)
                  updatedContent(addr)._3.filter(addrs).filter(updatedDs.find(_) != addrCls).foreach { ref => 
                    updatedIn = incEdgeRef(addr, ref, updatedIn, updatedDs)
                  }
                }
                // remove addresses that end up with no references anymore
                addrs.map(updatedDs.find).foreach { cls => 
                  if (!updatedIn.contains(cls)) { updatedToCheck += cls }
                }
              }
              // 3) add new references 
              addedRefs.foreach { to => 
                val updatedAdd = detectCycle(adr, to, (updatedDs, updatedIn))
                updatedDs      = updatedAdd._1
                updatedIn      = updatedAdd._2  
              }
              RefCountingStore(updatedContent, updatedIn, updatedDs, rootRefs, updatedToCheck, updatedHc)
            }
        case Some((u, _, urefs)) => // WEAK UPDATE
            val vrefs = JoinLattice[Abs].references(v)
            val updatedVal = JoinLattice[Abs].join(u, v)
            val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
            val ((updatedDs, updatedIn), updatedRefs) = vrefs.foldLeft(((this.ds, this.in), urefs)) { 
              (acc, ref) =>
                if (urefs.contains(ref)) { acc } else { (Main.timeGC { detectCycle(adr, ref, acc._1) }, acc._2 + ref) }
            }
            val updatedContent = this.content + (adr -> (updatedVal, CountInfinity, updatedRefs))
            RefCountingStore(updatedContent, updatedIn, updatedDs, rootRefs, toCheck, updatedHc) 
    }

  def updateOrExtend(a: Addr, v: Abs): RefCountingStore[Addr,Abs] = 
    content.get(a) match {
      case None    => extend(a, v)
      case Some(_) => update(a, v)
    }

  private def detectCycle(from: Addr, to: Addr, current: (DisjointSet[Addr],AddrCount)): (DisjointSet[Addr],AddrCount) = {

    // Optimization for a common case (trivial self-loops)
    if (from == to) {
      return current
    }

    val (currentDs, currentIn) = current 
    val initialTarget = currentDs.find(to)
    val (roots, refs) = currentIn(initialTarget)

    var updatedDs     = currentDs
    var updatedIn     = currentIn
    var target        = initialTarget
    var incomingRoots = roots
    var incomingRefs  = refs
    var visited       = Set[Addr]()

    def reachable(current: Addr): Boolean = {
      val cls = updatedDs.find(current)
      if (cls == target) {
        true
      } else if (visited(cls)) {
        false
      } else {
        visited = visited + cls
        val (count, refs) = updatedIn(cls)
        val (canReach, cantReach) = refs.partition(reachable)
        if (canReach.nonEmpty) {  // current node can reach target
          updatedIn     = updatedIn - cls
          incomingRefs  = incomingRefs ++ cantReach
          incomingRoots = incomingRoots + count
          updatedDs     = updatedDs.union(cls, target)
          target        = updatedDs.find(to)
          true
        } else {                  // current node can't reach target
          false
        }
      }
    }

    if (reachable(from)) {
      updatedIn = updatedIn - initialTarget 
      updatedIn = updatedIn + (target -> (incomingRoots, incomingRefs))
      (updatedDs, updatedIn)
    } else {
      (updatedDs, incEdgeRef(from,to,updatedIn,updatedDs))
    }
  }

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

  /* --- DEBUGGING --- */

  private def transclo(addrs: Set[Addr]): Set[Addr] = {
    var transclo = Set[Addr]()
    var todo = addrs.toList
    while (todo.nonEmpty) {
      val next = todo.head
      todo = todo.tail
      if(!transclo.contains(next)) {
        transclo += next
        todo ++= content(next)._3
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

  def calcCounts(): AddrCount = {
    var calculatedIn = rootRefs.foldLeft(Map[Addr, (Int, Set[Addr])]().withDefaultValue((0,Set[Addr]()))) {
      case (acc, (adr, count)) => 
        val cls = ds.find(adr)
        val (curCount, curRefs) = acc(cls)
        acc + (cls -> ((curCount + count, curRefs)))
    }
    content.foreach { case (adr,(_,_,refs)) =>
      refs.foreach { ref =>
        val cls = ds.find(ref)
        if (!ds.equiv(cls,adr)) {
          val (counts, rr) = calculatedIn(cls)
          calculatedIn = calculatedIn + (cls -> (counts, rr + adr))
        }
      }
    }
    calculatedIn
  }

  def calculatedDS() =
    Tarjan[Addr](content.keys, ref => content.get(ref).map(_._3).getOrElse(Set.empty))

  def checkDS() =
    assert(calculatedDS().allSets() == ds.allSets())

  def checkOnlyRoots() =
    in.keySet.foreach { adr => 
      if (ds.find(adr) != adr) {
        throw new RuntimeException(s"Address $adr is not a root address and has references registered")
      }
    }

  def checkNotContainSelf() = {
    in.foreach { case (adr,(_,refs)) => 
      refs.foreach { ref =>
        if (ds.find(ref) == adr) {
          throw new Exception(s"Address $adr has a reference $ref of the same SCC")
        }
      }
    }
  }

  def checkContent() =
    content.foreach { case (adr, (v, _, refs)) =>
      assert(JoinLattice[Abs].references(v) == refs)
    }

  def checkIn() = {
    val calc = calcCounts()
    if (calc != in) {
      println(Differ.calcDiff(calc,in))
      throw new RuntimeException("failed!")
    }
  }

  def checkNoEmptyRefs() = 
    content.foreach { case (adr, (v, _, refs)) =>
      refs.foreach { ref =>
        if (!content.contains(ref)) {
          throw new RuntimeException(s"Address $ref has no binding but is referenced from $adr (value: $v)")
        }
      }
    }

  private def checkHashCode() =
    if (this.content.values.map(_._1.hashCode).sum != this.hc) {
      throw new RuntimeException("Hashcode mismatch")
    }

  private def checkToCheck() =
    content.keys.foreach { adr => 
      println(s"checking $adr")
      val cls = ds.find(adr)
      if (!adr.isInstanceOf[ClassicalAddress.PrimitiveAddress] && !in.contains(cls) && !toCheck.exists(k => ds.find(k) == cls)) {
        throw new RuntimeException(s"Address $adr (SCC: $cls) has no incoming references and is not in $toCheck")
      }
    }

  //checkNoEmptyRefs()
  //checkToCheck()
  //checkHashCode()
  //checkContent()
  //checkNotContainSelf()
  //checkDS()
  //checkOnlyRoots()
  //checkIn()
}

object Differ {
  def calcDiff[K,V](map1: Map[K,V], map2: Map[K,V]): Map[K,(Option[V],Option[V])] = {
    val allKeys = map1.keySet ++ map2.keySet
    allKeys.foldLeft(Map[K,(Option[V],Option[V])]()) {
      (acc, k) =>
        if (map1.get(k) != map2.get(k)) {
          acc + (k -> ((map1.get(k), map2.get(k))))
        } else {
          acc
        }
    }
  }
}