import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

case class RefCountingStoreVanilla[Addr:Address, Abs:JoinLattice]
  (content: Map[Addr,(Abs,Set[Addr])],
        in: Map[Addr,(Int,Set[Addr])] = Map[Addr,(Int,Set[Addr])]().withDefaultValue(0,Set[Addr]()),
        hc: Int = 0)
  extends Store[Addr,Abs] {

  type AddrRefs = (Int, Set[Addr])
  type AddrCount = Map[Addr, AddrRefs]
  type AddrQueue = scala.collection.mutable.Queue[Addr]

  def keys = content.keys
  def forall(p: ((Addr,Abs)) => Boolean) = content.forall(n => p(n._1,n._2._1))
  def lookup(a: Addr) = content.get(a).map(_._1)
  def lookupBot(a: Addr) = lookup(a).getOrElse(JoinLattice[Abs].bottom)

  private def incRootRef(a: Addr, currentIn: AddrCount) = {
    val (counts, refs) = currentIn(a)
    currentIn + (a -> (counts + 1, refs))
  }

  private def incEdgeRef(from: Addr, to: Addr, currentIn: AddrCount) = {
      val (counts, refs) = currentIn(to)
      currentIn + (to -> (counts, refs + from))
  }

  def incRefs(addrs: Iterable[Addr]): RefCountingStoreVanilla[Addr,Abs] =
    this.copy(in = addrs.foldLeft(in)((acc,ref) => incRootRef(ref,acc)))

  private def deallocRef(update: AddrRefs => AddrRefs, to: Addr, currentIn: AddrCount, toDealloc: AddrQueue): AddrCount = {
    val current = currentIn(to)
    val updated@(count, refs) = update(current)
    if (count == 0 && refs.isEmpty) {
      toDealloc.enqueue(to)
      currentIn
    } else {
      currentIn + (to -> updated)
    }
  }

  private def deallocRootRef(target: Addr, currentIn: AddrCount, toDealloc: AddrQueue): AddrCount
     = deallocRef({ case (counts,refs) => (counts-1,refs) }, target, currentIn, toDealloc)

  private def deallocEdgeRef(from: Addr, to: Addr, currentIn: AddrCount, toDealloc: AddrQueue): AddrCount
     = deallocRef({ case (counts,refs) => (counts,refs-from) }, to, currentIn, toDealloc)


  private def dealloc(addr: Addr, currentIn: AddrCount, toDealloc: AddrQueue, toDelete: AddrQueue): AddrCount = {
    toDelete.enqueue(addr)
    val succs = content(addr)._2
    succs.foldLeft(currentIn)((acc,ref) => deallocEdgeRef(addr,ref,acc,toDealloc))
  }

  def decRefs(addrs: Iterable[Addr]): RefCountingStoreVanilla[Addr,Abs] = {
    val toDelete = scala.collection.mutable.Queue[Addr]()
    val toDealloc = scala.collection.mutable.Queue[Addr]()
    var updatedIn = addrs.foldLeft(this.in)((acc, ref) => deallocRootRef(ref, acc, toDealloc))
    while (toDealloc.nonEmpty) {
      updatedIn = dealloc(toDealloc.dequeue, updatedIn, toDealloc, toDelete)
    }
    val updatedHc = toDelete.foldLeft(this.hc)((acc, ref) => acc - content(ref)._1.hashCode())
    RefCountingStoreVanilla(content -- toDelete, updatedIn -- toDelete, updatedHc)
  }

  def extend(adr: Addr, v: Abs): RefCountingStoreVanilla[Addr,Abs] = content.get(adr) match {
    case None =>
      val vrefs = JoinLattice[Abs].references(v)
      val updatedContent = this.content + (adr -> (v, vrefs))
      val updatedIn = vrefs.foldLeft(this.in)((acc, ref) => incEdgeRef(adr, ref, acc))
      val updatedHc = this.hc + v.hashCode()
      this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
    case Some((u, _)) if JoinLattice[Abs].subsumes(u, v) =>
      this
    case Some((u, urefs)) =>
      val vrefs = JoinLattice[Abs].references(v)
      val updatedVal = JoinLattice[Abs].join(u, v)
      val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
      val (updatedIn, updatedRefs) = vrefs.foldLeft((this.in, urefs))((acc, ref) => {
        if (urefs.contains(ref)) { acc } else { (incEdgeRef(adr, ref, acc._1), acc._2 + ref) }
      })
      val updatedContent = this.content + (adr -> (updatedVal, updatedRefs))
      RefCountingStoreVanilla(updatedContent, updatedIn, updatedHc)
  }

  def update(a: Addr, v: Abs): RefCountingStoreVanilla[Addr,Abs] = extend(a,v)
  def updateOrExtend(a: Addr, v: Abs): RefCountingStoreVanilla[Addr,Abs] = extend(a,v)

  /* TODO */

  def join(that: Store[Addr,Abs]) = throw new Exception("NYI: RefCountingStore.join(Store[Addr,Abs])")
  def subsumes(that: Store[Addr,Abs]) = throw new Exception("NYI: RefCountingStore.subsumes(Store[Addr,Abs])")
  def diff(that: Store[Addr,Abs]) = throw new Exception("NYI: RefCountingStore.diff(Store[Addr,Abs])")

  /* PERFORMANCE OPTIMIZATION */

  override def equals(that: Any): Boolean = that match {
    case store: RefCountingStoreVanilla[Addr,Abs] => this.hc == store.hc && this.content == store.content
    case _ => false
  }

  override def hashCode = hc

}