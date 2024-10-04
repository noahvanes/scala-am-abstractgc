import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

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