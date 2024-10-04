import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict

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