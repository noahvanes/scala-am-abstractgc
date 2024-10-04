import scalaz._
import scalaz.Scalaz._
import scalaz.Semigroup
import Util.MapStrict
import core.DisjointSet

abstract class Store[Addr : Address, Abs : JoinLattice] {
  /** Gets all the keys of the store */
  def keys: Iterable[Addr]
  /** Checks if a predicate is true for all elements of the store */
  def forall(p: ((Addr, Abs)) => Boolean): Boolean
  /** Looks up a value in the store */
  def lookup(a: Addr): Option[Abs]
  def lookupMF(a: Addr): MayFail[Abs] = lookup(a) match {
    case Some(a) => a
    case None => UnboundAddress(a.toString)
  }
  /** Looks up a  value in the store, or return bottom if it's not there */
  def lookupBot(a: Addr): Abs
  /** Add a new entry in the store */
  def extend(a: Addr, v: Abs): Store[Addr, Abs]
  /** Update an entry in the store */
  def update(a: Addr, v: Abs): Store[Addr, Abs]
  /** Tries to update an address if it's already mapped into the store. Otherwise, extend the store */
  def updateOrExtend(a: Addr, v: Abs): Store[Addr, Abs]
  /** Joins two stores together */
  def join(that: Store[Addr, Abs]): Store[Addr, Abs]
  /** Checks whether this store subsumes another store */
  def subsumes(that: Store[Addr, Abs]): Boolean
  /** Returns a store containing items that differ between the two stores */
  def diff(that: Store[Addr, Abs]): Store[Addr, Abs]
  /** Returns a delta of the changes made on this store. None if the store doesn't support store deltas */
  def delta: Option[Map[Addr, Abs]] = None
  /** Add a delta to the store. This clears the current delta */
  def addDelta(delta: Map[Addr, Abs]): Store[Addr, Abs] = throw new Exception("Store doesn't support deltas")
  /** Returns the cardinality of each lattice element of this store */
  def cardinalities(withPrimitives: Boolean = false): Map[Addr, Cardinality] =
    keys
      .filter(a => withPrimitives || !Address[Addr].isPrimitive(a))
      .foldLeft(Map[Addr, Cardinality]())((acc, a) => lookup(a) match {
        case Some(v) => acc + (a -> JoinLattice[Abs].cardinality(v))
        case None => acc /* should not happen */
      })
}

object Store {
  def empty[Addr : Address, Abs : JoinLattice]: Store[Addr, Abs] = empty[Addr, Abs](JoinLattice[Abs].counting)
  def empty[Addr : Address, Abs : JoinLattice](counting: Boolean): Store[Addr, Abs] = if (counting) {
    CountingStore(Map())
  } else {
    BasicStore(Map())
  }
  def initial[Addr : Address, Abs : JoinLattice](values: Iterable[(Addr, Abs)]): Store[Addr, Abs] = if (JoinLattice[Abs].counting) {
    CountingStore(values.map({ case (a, v) => (a, (CountOne, v)) }).toMap)
  } else {
    BasicStore(values.toMap)
  }
  def refCountStore[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): RefCountingStore[Addr,Abs] = {
    val content = values.toMap.map({ case (k,v) => (k,(v,JoinLattice[Abs].references(v))) })
    new RefCountingStore[Addr,Abs](content)
  }
  def refCountStoreVanilla[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): RefCountingStoreVanilla[Addr,Abs] = {
    val content = values.toMap.map({ case (k,v) => (k,(v,JoinLattice[Abs].references(v))) })
    new RefCountingStoreVanilla[Addr,Abs](content)
  }
  def gcStore[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): GCStore[Addr,Abs] = new GCStore[Addr,Abs](values.toMap.mapValues(v => (v, CountOne)).toMap)
  def gcStoreAlt[Addr:Address,Abs:JoinLattice](values: Iterable[(Addr,Abs)]): GCStoreAlt[Addr,Abs] = new GCStoreAlt[Addr,Abs](values.toMap.mapValues(v => (v, CountOne)).toMap)

  implicit def monoid[Addr : Address, Abs : JoinLattice]: Monoid[Store[Addr, Abs]] =
    new Monoid[Store[Addr, Abs]] {
      def append(s1: Store[Addr, Abs], s2: => Store[Addr, Abs]): Store[Addr, Abs] = s1.join(s2)
      def zero: Store[Addr, Abs] = empty[Addr, Abs]
    }
}