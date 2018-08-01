trait Address[A] {
  def name: String
  def isPrimitive(x: A): Boolean
  def primitive(name: String): A
  def variable[Time : Timestamp, Abs : JoinLattice](id: Identifier, value: Abs, t: Time): A
  def cell[Exp : Expression, Time : Timestamp](exp: Exp, t: Time): A
  def botAddress: A = primitive("__bottom__")
  def allocationSite[Exp : Expression](a: A): Option[Either[Position, Position]]
}

object Address {
  def apply[A : Address]: Address[A] = implicitly
}

trait AddressWrapper {
  type A
  val isAddress: Address[A]
}

object ClassicalAddress extends AddressWrapper {
  trait A
  case class VariableAddress[Time : Timestamp](id: Identifier, t: Time) extends A {
    override def toString = s"@$id-$t"
  }
  case class PrimitiveAddress(name: String) extends A {
    override def toString = s"@$name"
  }
  case class CellAddress[Exp : Expression, Time : Timestamp](exp: Exp, t: Time) extends A {
    override def toString = s"@$exp-$t"
  }

  implicit val isAddress = new Address[A] {
    def name = "Classical"
    def isPrimitive(x: A) = x match {
      case PrimitiveAddress(_) => true
      case _ => false
    }
    def primitive(name: String) = PrimitiveAddress(name)
    def variable[Time : Timestamp, Abs : JoinLattice](id: Identifier, value: Abs, t: Time) = VariableAddress(id, t)
    def cell[Exp : Expression, Time : Timestamp](exp: Exp, t: Time) = CellAddress(exp, t)
    def allocationSite[Exp : Expression](a: A) = a match {
      case PrimitiveAddress(_) => None
      case VariableAddress(id, _) => Some(Left(id.pos))
      case CellAddress(exp: Exp @unchecked, _) => Some(Right(Expression[Exp].pos(exp)))
    }
  }
}

object ValueSensitiveAddress extends AddressWrapper {
  trait A
  case class VariableAddress[Time : Timestamp, Abs : JoinLattice](id: Identifier, value: Abs, t: Time) extends A {
    override def toString = s"@($id,$value)"
  }
  case class PrimitiveAddress(name: String) extends A {
    override def toString = s"@$name"
  }
  case class CellAddress[Exp : Expression, Time : Timestamp](exp: Exp, t: Time) extends A {
    override def toString = s"@$exp"
  }

  implicit val isAddress = new Address[A] {
    def name = "ValueSensitive"
    def isPrimitive(x: A) = x match {
      case PrimitiveAddress(_) => true
      case _ => false
    }
    def primitive(name: String) = PrimitiveAddress(name)
    def variable[Time : Timestamp, Abs : JoinLattice](id: Identifier, value: Abs, t: Time) = {
      /* To ensure finiteness, value should be a primitive value that doesn't contain addresses (i.e., no cons cell etc.) */
      VariableAddress(id, if (JoinLattice[Abs].isPrimitiveValue(value)) value else JoinLattice[Abs].bottom, t)
    }
    def cell[Exp : Expression, Time : Timestamp](exp: Exp, t: Time) = CellAddress(exp, t)
    def allocationSite[Exp : Expression](a: A) = a match {
      case PrimitiveAddress(_) => None
      case VariableAddress(id, _, _) => Some(Left(id.pos))
      case CellAddress(exp: Exp @unchecked, _) => Some(Right(Expression[Exp].pos(exp)))
    }
  }
}

object AdaptiveAddress extends AddressWrapper {

  val THRESHOLD = 10
  var config : Map[Identifier,AllocationStrategy] = null

  def init() = {
    config = Map().withDefaultValue(ConcreteAllocation(0))
  }
  def reset() = {
    config = config.filter({case (k,v) => v match {
      case ConcreteAllocation(_) => false
      case MonovariantAllocation => true
    }})
  }

  trait A
  case class ConcreteVariableAddress(id: Identifier, addr: Int) extends A {
    override def toString = s"@($id,$addr)"
  }
  case class MonovariantVariableAddress(id: Identifier) extends A {
    override def toString = s"@($id)"
  }
  case class PrimitiveAddress(name: String) extends A {
    override def toString = s"@$name"
  }
  case class CellAddress[Exp : Expression, Time : Timestamp](exp: Exp, t: Time) extends A {
    override def toString = s"@$exp"
  }
  //adaptive allocation strategy
  trait AllocationStrategy
  case class ConcreteAllocation(n: Int) extends AllocationStrategy
  case object MonovariantAllocation extends AllocationStrategy

  case class AddrOverflow(vrb: Identifier) extends Exception(s"Too many addresses allocated for $vrb")

  implicit val isAddress = new Address[A] {
    def name = "AdaptiveAddress"
    def isPrimitive(x: A) = x match {
      case PrimitiveAddress(_) => true
      case _ => false
    }
    def primitive(name: String) = PrimitiveAddress(name)
    def variable[Time : Timestamp, Abs : JoinLattice](id: Identifier, value: Abs, t: Time) = config(id) match {
      case ConcreteAllocation(n) if n > THRESHOLD => {
        config += (id -> MonovariantAllocation)
        throw AddrOverflow(id)
      }
      case ConcreteAllocation(n) => {
        config += (id -> ConcreteAllocation(n+1))
        ConcreteVariableAddress(id,n)
      }
      case MonovariantAllocation => MonovariantVariableAddress(id)
    }
    def cell[Exp : Expression, Time : Timestamp](exp: Exp, t: Time) = CellAddress(exp, t)
    def allocationSite[Exp : Expression](a: A) = a match {
      case PrimitiveAddress(_) => None
      case ConcreteVariableAddress(id, _) => Some(Left(id.pos))
      case MonovariantVariableAddress(id) => Some(Left(id.pos))
      case CellAddress(exp: Exp @unchecked, _) => Some(Right(Expression[Exp].pos(exp)))
    }
  }
}
