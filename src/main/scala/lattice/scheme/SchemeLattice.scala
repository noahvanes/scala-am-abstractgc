/** A lattice for Scheme should support the following operations */
trait SchemeLattice[L] extends JoinLattice[L] {
  /** Can this value be considered true for conditionals? */
  def isTrue(x: L): Boolean
  /** Can this value be considered false for conditionals? */
  def isFalse(x: L): Boolean
  /** Performs a unary operation on the abstract value x */
  def unaryOp(op: SchemeOps.UnaryOperator)(x: L): L
  /** Performs a binary operation on abstract values x and y */
  def binaryOp(op: SchemeOps.BinaryOperator)(x: L, y: L): L
  /** Conjunction */
  def and(x: L, y: => L): L
  /** Disjunction */
  def or(x: L, y: => L): L
  /** Extract closures contained in this value */
  def getClosures[Exp : Expression, Addr : Address](x: L): Set[(Exp, Environment[Addr])]
  /** Extract primitives contained in this value */
  def getPrimitives[Addr : Address, Abs : JoinLattice](x: L): Set[Primitive[Addr, Abs]]


  /** Injection of an integer */
  def inject(x: Int): L
  /** Injection of a float */
  def inject(x: Float): L
  /** Injection of a string */
  def inject(x: String): L
  /** Injection of a boolean */
  def inject(x: Boolean): L
  /** Injection of a character */
  def inject(x: Char): L
  /** Injection of a primitive function */
  def inject[Addr : Address, Abs : JoinLattice](x: Primitive[Addr, Abs]): L
  /** Injection of a closure */
  def inject[Exp : Expression, Addr : Address](x: (Exp, Environment[Addr])): L
  /** Injection of a symbol */
  def injectSymbol(x: String): L
  /** Creates a cons cell */
  def cons[Addr : Address](car: Addr, cdr: Addr): L
  /** Nil value */
  def nil: L
}

/** A lattice for Concurrent Scheme */
trait ConcurrentSchemeLattice[L] extends SchemeLattice[L] {
  /** Extract thread ids contained in this value */
  def getTids[TID : ThreadIdentifier](x: L): Set[TID]
  /** Extract lock addresses contained in this value */
  def getLocks[Addr : Address](x: L): Set[Addr]

  /** Inject a thread id */
  def injectTid[TID : ThreadIdentifier](tid: TID): L
  /** Creates a lock wrapper (that contains the address of the lock) */
  def lock[Addr : Address](addr: Addr): L
  /** The locked value */
  def lockedValue: L
  /** The unlocked value */
  def unlockedValue: L
}

/** Internals of a lattice for Scheme, used by the primitives' definitions */
trait SchemeLatticeInternals[L] extends SchemeLattice[L] {
  /** Injects an error */
  def error(x: L): L
  /** Takes the car of a cons cell */
  def car[Addr : Address](x: L): Set[Addr]
  /** Takes the cdr of a cons cell */
  def cdr[Addr : Address](x: L): Set[Addr]
  /** Get a value from a vector. Returns either an error or the addresses where to look for the values */
  def vectorRef[Addr : Address](vector: L, index: L): Set[Either[L, Addr]]
  /** Changes a value inside a vector. The address given is an address where the
   * value can be stored if needed.  Returns the vector value, as well as the
   * addresses to update in the store. The value stored is not passed to
   * vectorSet, but will be stored in the returned addresses. */
  def vectorSet[Addr : Address](vector: L, index: L, addr: Addr): (L, Set[Addr])
  /** Extract vector addresses contained in this value */
  def getVectors[Addr : Address](x: L): Set[Addr]
  def vector[Addr : Address](addr: Addr, size: L, init: Addr): (L, L)
}