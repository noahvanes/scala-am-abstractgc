import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

class StoreJoinException extends Exception

case class GCStoreAlt[Addr : Address, Abs : JoinLattice]
  (content: Map[Addr,(Abs, Count)],
   refs: Map[Addr,Set[Addr]] = Map[Addr,Set[Addr]]().withDefaultValue(Set()),
   marked: Boolean = false)
  extends Store[Addr,Abs] {

  def keys = content.keys
  def forall(p: ((Addr,Abs)) => Boolean) = content.mapValues(_._1).forall(p)
  def lookup(a: Addr) = content.get(a).map(_._1)
  def lookupBot(a: Addr) = lookup(a).getOrElse(JoinLattice[Abs].bottom)

  def extend(a: Addr, v: Abs) = content.get(a) match {
    case None                     => GCStoreAlt(content + (a -> (v, CountOne)),                         refs + (a -> JoinLattice[Abs].references(v)))
    case Some(_) if marked        => throw new StoreJoinException()
    case Some((v2, n))            => GCStoreAlt(content + (a -> (JoinLattice[Abs].join(v2, v), n.inc)), refs + (a -> (refs(a) ++ JoinLattice[Abs].references(v))))
  }
  def update(a: Addr, v: Abs) = content.get(a) match {
    case None                      => throw new RuntimeException("Updating store at an adress not used")
    case Some((_, CountOne))       => GCStoreAlt(content + (a -> (v, CountOne)),                                 refs + (a -> JoinLattice[Abs].references(v)))
    case Some((v2, CountInfinity)) => GCStoreAlt(content + (a -> (JoinLattice[Abs].join(v2, v), CountInfinity)), refs + (a -> (refs(a) ++ JoinLattice[Abs].references(v))))
  }
  def updateOrExtend(a: Addr, v: Abs) = content.get(a) match {
    case None    => extend(a, v)
    case Some(_) => update(a, v)
  }

  private def mark(adr: Addr, marked: Set[Addr]): Set[Addr] =
    if (marked.contains(adr)) {
      marked
    } else {
      refs(adr).foldLeft(marked + adr)((acc,ref) => mark(ref,acc))
    }

  private def sweep(marked: Set[Addr]): GCStoreAlt[Addr,Abs] = {
    val updatedContent = content.filterKeysStrict(marked)
    val updatedRefs = refs.filterKeysStrict(marked).withDefaultValue(Set())
    GCStoreAlt(updatedContent,updatedRefs,false)
  }

  def collect(roots: Set[Addr]): GCStoreAlt[Addr,Abs] = Main.timeGC {
    val marked = roots.foldLeft(Set[Addr]())((acc, ref) => mark(ref, acc))
    sweep(marked)
  }

  /* TODO */

  def join(that: Store[Addr,Abs]) = throw new Exception("NYI: GCStore.join(Store[Addr,Abs])")
  def subsumes(that: Store[Addr,Abs]) = throw new Exception("NYI: GCStore.subsumes(Store[Addr,Abs])")
  def diff(that: Store[Addr,Abs]) = throw new Exception("NYI: GCStore.diff(Store[Addr,Abs])")

  /* PERFORMANCE OPTIMIZATION */

  override def equals(that: Any): Boolean = that match {
    case store: GCStoreAlt[Addr,Abs] => this.storedHashCode == store.storedHashCode && this.content == store.content
    case _ => false
  }

  val storedHashCode = content.hashCode
  override def hashCode = storedHashCode
}