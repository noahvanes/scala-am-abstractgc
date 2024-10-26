import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

case class RefCountingStore[Addr:Address, Abs:JoinLattice]
  (content: Map[Addr,(Abs,Set[Addr])],
        in: Map[Addr,(Int,Set[Addr])] = Map[Addr,(Int,Set[Addr])]().withDefaultValue(0,Set[Addr]()),
        ds: DisjointSet[Addr] = DisjointSet[Addr](),
   toCheck: Set[Addr] = Set[Addr](),
        hc: Int = 0)
extends Store[Addr,Abs] {

  type AddrRefs = (Int,Set[Addr])
  type AddrCount = Map[Addr,AddrRefs]

  def keys = content.keys
  def forall(p: ((Addr,Abs)) => Boolean) = content.forall(n => p(n._1,n._2._1))
  def lookup(a: Addr) = content.get(a).map(_._1)
  def lookupBot(a: Addr) = lookup(a).getOrElse(JoinLattice[Abs].bottom)

  private def incRootRef(a: Addr, currentIn: AddrCount) = {
    val cls = ds.find(a)
    val (counts, refs) = currentIn(cls)
    currentIn + (cls -> (counts + 1, refs))
  }

  private def incEdgeRef(from: Addr, to: Addr, currentIn: AddrCount, currentDS: DisjointSet[Addr]) = {
    val cls = currentDS.find(to)
    val (counts, refs) = currentIn(cls)
    currentIn + (cls -> (counts, refs + from))
  }

  def incRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] =
    this.copy(in = addrs.foldLeft(in)((acc,ref) => incRootRef(ref, acc)))

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

  def collect(): RefCountingStore[Addr,Abs] = {
    var toDealloc       = toCheck.filterNot(scc => in.contains(scc)).toList 
    var updatedContent  = this.content 
    var updatedIn       = this.in 
    var updatedDs       = this.ds 
    var updatedHc       = this.hc 
    while (toDealloc.nonEmpty) {
        val scc = toDealloc.head
        toDealloc = toDealloc.tail 
        // DEALLOC THE SCC 
        val addrs = updatedDs.allOf(scc)
        addrs.foreach { addr => 
          val (vlu, succs) = updatedContent(addr)
          updatedContent = updatedContent - addr 
          updatedHc = updatedHc - vlu.hashCode() 
          updatedIn = succs.toList.filterNot(updatedDs.find(_) == scc).foldLeft(updatedIn) { 
            (accIn, succ) =>
              val cls = updatedDs.find(succ)
              val (isGarbage, accIn2) = decEdgeRef(addr, cls, accIn)
              if (isGarbage) { toDealloc = cls :: toDealloc }
              accIn2
          }
        }  
        updatedDs = updatedDs -- addrs
    }
    RefCountingStore(updatedContent, updatedIn, updatedDs, Set.empty, updatedHc)
  }

  private def decRefs(addrs: Iterable[Addr], currentIn: AddrCount, currentToCheck: Set[Addr]): (AddrCount, Set[Addr]) =
    addrs.foldLeft((currentIn, currentToCheck)) { 
        case ((accIn, accToCheck), addr) =>
            val cls = ds.find(addr)
            val (isGarbage, accIn2) = decRootRef(cls, accIn)
            (accIn2, if (isGarbage) (accToCheck + cls) else accToCheck)
    }

  def decRefs(addrs: Iterable[Addr]): RefCountingStore[Addr,Abs] = {
    val (updatedIn, updatedToCheck) = decRefs(addrs, this.in, this.toCheck)
    this.copy(in = updatedIn, toCheck = updatedToCheck)
  }

  def extend(adr: Addr, v: Abs): RefCountingStore[Addr,Abs] = content.get(adr) match {
      case None =>
        val vrefs = JoinLattice[Abs].references(v)
        val updatedContent = this.content + (adr -> (v, vrefs))
        val updatedIn = vrefs.foldLeft(this.in)((acc, ref) => {
          if (ref == adr) { acc } else { incEdgeRef(adr, ref, acc, this.ds) }
        })
        val updatedHc = this.hc + v.hashCode()
        this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
      case Some((u, _)) if JoinLattice[Abs].subsumes(u, v) =>
        this
      case Some((u, urefs)) =>
        val vrefs = JoinLattice[Abs].references(v)
        val updatedVal = JoinLattice[Abs].join(u, v)
        val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
        val ((updatedDs, updatedIn), updatedRefs) = vrefs.foldLeft(((this.ds, this.in), urefs))((acc, ref) => {
          if (urefs.contains(ref)) { acc } else { (detectCycle(adr, ref, acc._1), acc._2 + ref) }
        })
        val updatedContent = this.content + (adr -> (updatedVal, updatedRefs))
        RefCountingStore(updatedContent, updatedIn, updatedDs, toCheck, updatedHc)
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

  /* --- DEBUGGING --- */

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

  def calcCounts(rootCounts: Map[Addr,Int]): AddrCount = {
    var calculatedIn = rootCounts.map(p => (p._1,(p._2,Set[Addr]()))).withDefaultValue((0,Set[Addr]()))
    content foreach { case (adr,(_,refs)) =>
      refs foreach { ref =>
        val cls = ds.find(ref)
        if (!ds.equiv(cls,adr)) {
          val (counts, rr) = calculatedIn(cls)
          calculatedIn = calculatedIn + (cls -> (counts, rr + adr))
        }
      }
    }
    calculatedIn
  }
}