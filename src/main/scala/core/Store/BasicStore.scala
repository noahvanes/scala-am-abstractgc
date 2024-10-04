import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

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