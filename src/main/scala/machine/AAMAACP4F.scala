import scalaz._
import scalaz.Scalaz._

trait KAllocStrategy
case object AAMKAlloc extends KAllocStrategy
case object AACKAlloc extends KAllocStrategy
case object P4FKAlloc extends KAllocStrategy
/**
 * AAM/AAC/P4F techniques combined in a single machine abstraction
 */
class AAMAACP4F[Exp : Expression, Abs : JoinLattice, Addr : Address, Time : Timestamp](strategy: KAllocStrategy)
    extends EvalKontMachine[Exp, Abs, Addr, Time] {
  def name = s"AAMAACP4F($strategy)"

  trait KontAddr
  case class AAMKontAddress(e2: Exp, t: Time) extends KontAddr {
    override def toString = s"AAM($e2)"
  }
  case class AACKontAddress(e2: Exp, env2: Environment[Addr], control: Control, store: Store[Addr, Abs], t: Time) extends KontAddr {
    override def toString = s"AAC($e2)"
  }
  case class P4FKontAddress(e2: Exp, env2: Environment[Addr], t: Time) extends KontAddr {
    override def toString = s"P4F($e2)"
  }
  case object HaltKontAddress extends KontAddr {
    override def toString = "HaltKontAddress"
  }

  object KontAddr {
    implicit object KontAddrKontAddress extends KontAddress[KontAddr]
  }

  case class GlobalStore(val store: DeltaStore[Addr, Abs], delta: Map[Addr, Abs]) {
    def includeDelta(d: Option[Map[Addr, Abs]]): GlobalStore = d match {
      case Some(d) => this.copy(delta = delta |+| d)
      case None => throw new Exception("AAMGlobalStore should be used with a store that supports delta!")
    }
    def isUnchanged = delta.isEmpty
    def commit = if (isUnchanged) { this } else { this.copy(store = store.addDelta(delta), delta = Map()) }
  }

  def kalloc(state: State, e: Exp, env: Environment[Addr], store: Store[Addr, Abs], t: Time) = strategy match {
    case AAMKAlloc => AAMKontAddress(e, t)
    case AACKAlloc => AACKontAddress(e, env, state.control, store, t)
    case P4FKAlloc => P4FKontAddress(e, env, t)
  }

  implicit val stateWithKey = new WithKey[State] {
    type K = KontAddr
    def key(st: State) = st.a
  }

  case class State(control: Control, a: KontAddr, t: Time) {
    override def toString = control.toString
    def subsumes(that: State): Boolean = control.subsumes(that.control) && a == that.a && t == that.t

    private def integrate(a: KontAddr, actions: Set[Action[Exp, Abs, Addr]], store: GlobalStore, kstore: KontStore[KontAddr]): (Set[State], GlobalStore, KontStore[KontAddr]) =
      actions.foldLeft((Set[State](), store, kstore))((acc, action) => action match {
        case ActionReachedValue(v, store2, _) => (acc._1 + State(ControlKont(v), a, Timestamp[Time].tick(t)), acc._2.includeDelta(store2.delta), acc._3)
        case ActionPush(frame, e, env, store2, _) =>
          val next = kalloc(this, e, env, store2, t)
          (acc._1 + State(ControlEval(e, env), next, Timestamp[Time].tick(t)), acc._2.includeDelta(store2.delta), acc._3.extend(next, Kont(frame, a)))
        case ActionEval(e, env, store2, _) =>
          (acc._1 + State(ControlEval(e, env), a, Timestamp[Time].tick(t)), acc._2.includeDelta(store2.delta), acc._3)
        case ActionStepIn(fexp, _, e, env, store2, _, _) =>
          (acc._1 + State(ControlEval(e, env), a, Timestamp[Time].tick(t)), acc._2.includeDelta(store2.delta), acc._3)
        case ActionError(err) =>
          (acc._1 + State(ControlError(err), a, Timestamp[Time].tick(t)), acc._2, acc._3)
      })

    /**
     * Computes the set of states that follow the current state, and return the new store as well.
     */
    def step(sem: Semantics[Exp, Abs, Addr, Time], store: GlobalStore, kstore: KontStore[KontAddr]): (Set[State], GlobalStore, KontStore[KontAddr]) = control match {
      /* In a eval state, call the semantic's evaluation method */
      case ControlEval(e, env) => integrate(a, sem.stepEval(e, env, store.store, t), store, kstore)
      /* In a continuation state, call the semantic's continuation method */
      case ControlKont(v) => kstore.lookup(a).foldLeft((Set[State](), store, kstore))((acc, kont) => kont match {
        case Kont(frame, next) => integrate(next, sem.stepKont(v, frame, store.store, t), acc._2, acc._3) match {
          case (states, store2, kstore2) => (acc._1 ++ states, store2, kstore2)
        }
      })
      /* In an error state, the state is not able to make a step */
      case ControlError(_) => (Set(), store, kstore)
    }
    /**
     * Checks if the current state is a final state. It is the case if it
     * reached the end of the computation, or an error
     */
    def halted: Boolean = control match {
      case ControlEval(_, _) => false
      case ControlKont(v) => a == HaltKontAddress
      case ControlError(_) => true
    }
  }
  object State {
    def inject(exp: Exp, env: Iterable[(String, Addr)], store: Iterable[(Addr, Abs)]): (State, GlobalStore, KontStore[KontAddr]) =
      (State(ControlEval(exp, Environment.initial[Addr](env)), HaltKontAddress, Timestamp[Time].initial("")),
        GlobalStore(DeltaStore[Addr, Abs](store.toMap, Map()), Map()),
        TimestampedKontStore[KontAddr](Map(), 0))

    type Context = Set[State]
    implicit val graphNode = new GraphNode[State, Context] {
      override def label(s: State) = s.toString
      override def color(s: State, halted: Context) = s.control match {
        case _: ControlEval => Colors.White
        case _: ControlKont if s.halted => Colors.Green
        case _: ControlKont => Colors.Yellow
        case _: ControlError => Colors.Red
      }
    }
  }

  type G = Option[Graph[State, Unit, State.Context]]
  case class AAMAACP4FOutput(halted: Set[State], store: Store[Addr, Abs],
    numberOfStates: Int, time: Double, graph: G, timedOut: Boolean)
      extends Output {
    def finalValues = halted.flatMap(st => st.control match {
      case ControlKont(v) => Set[Abs](v)
      case _ => Set[Abs]()
    })
    def toFile(path: String)(output: GraphOutput) = graph match {
      case Some(g) => output.toFile(g, halted)(path)
      case None => println("Not generating graph because no graph was computed")
    }
  }

  /**
   * Evaluate a program represented by an expression, under the given
   * semantics. A graph can be generated if @genGraph is true, and a timeout
   * can be given.
   */
  def eval(exp: Exp, sem: Semantics[Exp, Abs, Addr, Time], genGraph: Boolean, timeout: Timeout): Output = {
    import scala.language.higherKinds
    /* @param todo is the worklist, @param visited is the set of visited states that
     * don't need to be revisited, @param halted the set of halted
     * states, @param graph the graph visited up to now, and @param
     * reallyVisited is the set of states that have been visited (but might
     * include states that have to be revisited, to account for changes in the
     * global store. The global store is composed of a global value store
     * (@param store) and a global continuation store (@param kstore). */
    /* Note: this loop is different from AAM's loop. AAM's loop explores the state
     * space in a state-by-state fashion, one state at a time. Here we explore
     * the state space using a frontier-based approach, where we explore all the
     * elements in the worklist at each iteration */
    @scala.annotation.tailrec
    def loop[VS[_]: VisitedSet](todo: Set[State], visited: VS[State], store: GlobalStore, kstore: KontStore[KontAddr],
      halted: Set[State], graph: G, reallyVisited: Set[State]): AAMAACP4FOutput =
      if (todo.isEmpty || timeout.reached) {
        /* Worklist is empty or we reached the timeout, we return what we have computed */
        AAMAACP4FOutput(halted, store.commit.store,
          reallyVisited.size, timeout.time, graph, timeout.reached)
      } else {
        /* For every element in the worklist, explore them and keep the updated store and kstore */
        val (edges, store2, kstore2) = todo.foldLeft(Set[(State, State)](), store, kstore)((acc, state) =>
          state.step(sem, acc._2, acc._3) match {
            case (next, store2, kstore2) =>
              (acc._1 ++ next.map(state2 => (state, state2)), store2, kstore2)
          })
        if (store2.isUnchanged && kstore.fastEq(kstore2)) {
          /* If the store and kstore have not changed, we can safely keep the visited
           * states, add the states from the worklist to these visited states
           * and proceed the computation with the new successors we
           * discovered */
          //assert(store2.commit.store == store2.store)
          loop(edges.map({ case (s1, s2) => s2 }).filter(s2 => !VisitedSet[VS].contains(visited, s2)),
            VisitedSet[VS].append(visited, todo),
            store2, kstore2,
            halted ++ todo.filter(_.halted),
            graph.map(_.addEdges(edges.map({ case (s1, s2) => (s1, (), s2) }))),
            reallyVisited ++ todo)
        } else {
          /* If the store or the kstore changed, we have to clean the set of visited
           * states. If we ever encounter a state we already visited, because
           * the store has been updated, we have to reexplore it. */
          //assert(!(!store2.isUnchanged && store2.commit.store == store2.store))
          loop(edges.map({ case (s1, s2) => s2 }),
            VisitedSet[VS].empty,
            store2.commit, kstore2,
            halted ++ todo.filter(_.halted),
            graph.map(_.addEdges(edges.map({ case (s1, s2) => (s1, (), s2) }))),
            reallyVisited ++ todo)
        }
      }

    val (state, store, kstore) = State.inject(exp, sem.initialEnv, sem.initialStore)
    loop(Set(state),
      VisitedSet.MapVisitedSet.empty,
      store, kstore, Set(), if (genGraph) { Some(Graph.empty) } else { None }, Set())
  }
}
