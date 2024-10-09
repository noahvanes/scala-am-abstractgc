import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

case class RefCountingStoreVanilla[Addr:Address, Abs:JoinLattice]
  (content: Map[Addr,(Abs,Count,Set[Addr])],
        in: Map[Addr,(Int,Set[Addr])] = Map[Addr,(Int,Set[Addr])]().withDefaultValue(0,Set[Addr]()),
   toCheck: Set[Addr] = Set.empty[Addr], 
        hc: Int = 0)
  extends Store[Addr,Abs] {

  type AddrRefs = (Int, Set[Addr])
  type AddrCount = Map[Addr, AddrRefs]

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

  private def decRef(update: AddrRefs => AddrRefs, to: Addr, currentIn: AddrCount): (Boolean, AddrCount) = {
    val current = currentIn(to)
    val updated@(count, refs) = update(current)
    if (count == 0 && refs.isEmpty) {
      (true, currentIn - to)
    } else {
      (false, currentIn + (to -> updated))
    }
  }

  private def decRootRef(target: Addr, currentIn: AddrCount): (Boolean, AddrCount)
     = decRef({ case (counts,refs) => (counts-1,refs) }, target, currentIn)

  private def decEdgeRef(from: Addr, to: Addr, currentIn: AddrCount): (Boolean, AddrCount)
     = decRef({ case (counts,refs) => (counts,refs-from) }, to, currentIn)

  private def decRefs(addrs: Iterable[Addr], currentIn: AddrCount, currentToCheck: Set[Addr]): (AddrCount, Set[Addr]) =
    addrs.foldLeft((currentIn, currentToCheck)) { 
        case ((accIn, accToCheck), addr) =>
            val (isGarbage, accIn2) = decRootRef(addr, accIn)
            (accIn2, if (isGarbage) (accToCheck + addr) else accToCheck)
    }

  def decRefs(addrs: Iterable[Addr]): RefCountingStoreVanilla[Addr,Abs] = {
    val (updatedIn, updatedToCheck) = decRefs(addrs, this.in, this.toCheck)
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
        val (vlu, _, succs) = updatedContent(addr)
        updatedContent = updatedContent - addr 
        updatedHc = updatedHc - vlu.hashCode()
        updatedIn = succs.foldLeft(updatedIn) { (accIn, succ) => 
            val (isGarbage, accIn2) = decEdgeRef(addr, succ, accIn)
            if (isGarbage) { toDealloc = succ :: toDealloc }
            accIn2
        }
    }
    RefCountingStoreVanilla(updatedContent, updatedIn, Set.empty, updatedHc)
  }

  def extend(adr: Addr, v: Abs): RefCountingStoreVanilla[Addr,Abs] = 
    content.get(adr) match {
        case None =>
            val vrefs = JoinLattice[Abs].references(v)
            val updatedContent = this.content + (adr -> (v, CountOne, vrefs))
            val updatedIn = vrefs.foldLeft(this.in)((acc, ref) => incEdgeRef(adr, ref, acc))
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
            val (updatedIn, updatedRefs) = vrefs.foldLeft((this.in, urefs))((acc, ref) => {
                if (urefs.contains(ref)) { acc } else { (incEdgeRef(adr, ref, acc._1), acc._2 + ref) }
            })
            val updatedContent = this.content + (adr -> (updatedVal, CountInfinity, updatedRefs))
            this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)
    }

  def update(adr: Addr, v: Abs): RefCountingStoreVanilla[Addr,Abs] =
    content.get(adr) match {
        case None => 
            throw new RuntimeException("Updating store at an adress not used")
        case Some((u, CountOne, urefs)) => // STRONG UPDATE
            val vrefs = JoinLattice[Abs].references(v)
            val updatedHc = this.hc - u.hashCode() + v.hashCode()
            val (updatedIn, updatedToCheck) = decRefs(urefs -- vrefs, this.in, this.toCheck)
            val updatedIn2 = vrefs.foldLeft(updatedIn) { (acc, ref) => 
                if (urefs.contains(ref)) { acc } else { incEdgeRef(adr, ref, acc) }    
            }
            val updatedContent = this.content + (adr -> (v, CountOne, vrefs))
            this.copy(content = updatedContent, in = updatedIn2, toCheck = updatedToCheck, hc = updatedHc)
        case Some((u, CountInfinity, urefs)) => // WEAK UPDATE
            val vrefs = JoinLattice[Abs].references(v)
            val updatedVal = JoinLattice[Abs].join(u, v)
            val updatedHc = this.hc - u.hashCode() + updatedVal.hashCode()
            val (updatedIn, updatedRefs) = vrefs.foldLeft((this.in, urefs))((acc, ref) => {
                if (urefs.contains(ref)) { acc } else { (incEdgeRef(adr, ref, acc._1), acc._2 + ref) }
            })
            val updatedContent = this.content + (adr -> (updatedVal, CountInfinity, updatedRefs))
            this.copy(content = updatedContent, in = updatedIn, hc = updatedHc)    
    }
  
  def updateOrExtend(a: Addr, v: Abs) = content.get(a) match {
    case None    => extend(a, v)
    case Some(_) => update(a, v)
  }
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