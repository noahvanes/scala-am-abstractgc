import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

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
