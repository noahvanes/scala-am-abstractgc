import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

case class RefCountingStoreVanilla[Addr:Address, Abs:JoinLattice]
  (content: Map[Addr,(Abs,Set[Addr])],
        in: Map[Addr,Int] = Map[Addr,Int]().withDefaultValue(0),
   toCheck: Set[Addr] = Set.empty[Addr], 
        hc: Int = 0)
  extends Store[Addr,Abs] {

  type AddrCount = Map[Addr, Int]

  def keys = content.keys
  def forall(p: ((Addr,Abs)) => Boolean) = content.forall(n => p(n._1,n._2._1))
  def lookup(a: Addr) = content.get(a).map(_._1)
  def lookupBot(a: Addr) = lookup(a).getOrElse(JoinLattice[Abs].bottom)

  private def incRef(a: Addr, currentIn: AddrCount) = 
    currentIn + (a -> (currentIn(a) + 1))

  def incRefs(addrs: Iterable[Addr]): RefCountingStoreVanilla[Addr,Abs] =
    this.copy(in = addrs.foldLeft(in)((acc,ref) => incRef(ref,acc)))

  private def decRef(to: Addr, currentIn: AddrCount): (Boolean, AddrCount) = {
    val updated = currentIn(to) - 1
    if (updated == 0) {
      (true, currentIn - to)
    } else {
      (false, currentIn + (to -> updated))
    }
  }

  def decRefs(addrs: Iterable[Addr]): RefCountingStoreVanilla[Addr,Abs] = {
    val (updatedIn, updatedToCheck) = 
        addrs.foldLeft((this.in, this.toCheck)) { 
            case ((accIn, accToCheck), addr) =>
                val (isGarbage, accIn2) = decRef(addr, accIn)
                (accIn2, if (isGarbage) (accToCheck + addr) else accToCheck)
        }
    this.copy(in = updatedIn, toCheck = updatedToCheck)
  }

  def collect(): RefCountingStoreVanilla[Addr,Abs] = {
    var toDealloc       = toCheck.toList.filterNot(addr => in.contains(addr))
    var updatedContent  = this.content 
    var updatedIn       = this.in 
    var updatedHc       = this.hc 
    while (toDealloc.nonEmpty) {
        val addr = toDealloc.head
        toDealloc = toDealloc.tail 
        val (vlu, succs) = updatedContent(addr)
        updatedContent = updatedContent - addr 
        updatedHc = updatedHc - vlu.hashCode()
        updatedIn = succs.foldLeft(updatedIn) { (accIn, succ) => 
            val (isGarbage, accIn2) = decRef(succ, accIn)
            if (isGarbage) { toDealloc = succ :: toDealloc }
            accIn2
        }
    }
    RefCountingStoreVanilla(updatedContent, updatedIn, Set.empty, updatedHc)
  }

  def extend(adr: Addr, v: Abs): RefCountingStoreVanilla[Addr,Abs] = content.get(adr) match {
    case None =>
      val vrefs = JoinLattice[Abs].references(v)
      val updatedContent = this.content + (adr -> (v, vrefs))
      val updatedIn = vrefs.foldLeft(this.in)((acc, ref) => incRef(ref, acc))
      val updatedHc = this.hc + v.hashCode()
      this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
    case Some((u, _)) if JoinLattice[Abs].subsumes(u, v) =>
      this
    case Some((u, urefs)) =>
      val vrefs = JoinLattice[Abs].references(v)
      val updatedVal = JoinLattice[Abs].join(u, v)
      val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
      val (updatedIn, updatedRefs) = vrefs.foldLeft((this.in, urefs)) { (acc, ref) => 
        if (urefs.contains(ref)) { acc } else { (incRef(ref, acc._1), acc._2 + ref) }
      }
      val updatedContent = this.content + (adr -> (updatedVal, updatedRefs))
      this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
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