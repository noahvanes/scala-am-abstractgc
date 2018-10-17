/**
 * Implementation of a CESK machine following the AAM approach (Van Horn, David,
 * and Matthew Might. "Abstracting abstract machines." ACM Sigplan
 * Notices. Vol. 45. No. 9. ACM, 2010).
 *
 * A difference with the paper is that we separate the continuation store
 * (KontStore) from the value store (Store). That simplifies the implementation
 * of both stores, and the only change it induces is that we are not able to
 * support first-class continuation as easily (we don't support them at all, but
 * they could be added).
 *
 * Also, in the paper, a CESK state is made of 4 components: Control,
 * Environment, Store, and Kontinuation. Here, we include the environment in the
 * control component, and we distinguish "eval" states from "continuation"
 * states. An eval state has an attached environment, as an expression needs to
 * be evaluated within this environment, whereas a continuation state only
 * contains the value reached.
 */
class AAMRefCounting[Exp : Expression, Abs : JoinLattice, Addr : Address, Time : Timestamp]
    extends EvalKontMachine[Exp, Abs, Addr, Time] {
  def name = "AAMRefCounting"

  /**
   * The store used for continuations is a KontStore (defined in
   * Kontinuation.scala). It is parameterized by continuation addresses, that
   * are element of the KontAddress typeclass.
   */
  trait KontAddr
  case class NormalKontAddress(exp: Exp, time: Time) extends KontAddr {
    override def toString = s"NormalKontAddress($exp)"
    lazy val storedHashCode = (exp,time).hashCode
    override def hashCode = storedHashCode
  }
  case object HaltKontAddress extends KontAddr {
    override def toString = "HaltKontAddress"
    override def hashCode = 0
  }

  object KontAddr {
    implicit object KontAddrKontAddress extends KontAddress[KontAddr]
  }

  implicit val stateWithKey = new WithKey[State] {
    type K = KontAddr
    def key(st: State) = st.a
  }

  /**
   * A machine state is made of a control component, a value store, a
   * continuation store, and an address representing where the current
   * continuation lives.
   */
  case class State(control: Control, store: RefCountingStore[Addr, Abs], kstore: RefCountingKontStore[Addr,KontAddr], a: KontAddr, t: Time) {
    override def toString = control.toString

    lazy val storedHashCode = (control, store, kstore, a, t).hashCode()
    override def hashCode = storedHashCode

    /**
     * Checks whether a states subsumes another, i.e., if it is "bigger". This
     * is used to perform subsumption checking when exploring the state space,
     * in order to avoid exploring states for which another state that subsumes
     * them has already been explored.
     */
    def subsumes(that: State): Boolean = control.subsumes(that.control) && store.subsumes(that.store) && a == that.a && kstore.subsumes(that.kstore) && t == that.t

    /**
     * Integrates a set of actions (returned by the semantics, see
     * Semantics.scala), in order to generate a set of states that succeeds this
     * one.
     */
    private def integrate(adr: KontAddr, actions: Set[Action[Exp, Abs, Addr]]): Iterable[(State,Iterable[Addr])] =
      actions.toIterable.map({
        /* When a value is reached, we go to a continuation state */
        case ActionReachedValue(v, store : RefCountingStore[Addr, Abs], _) => (State(ControlKont(v), store, kstore, adr, Timestamp[Time].tick(t)), Iterable.empty)
        /* When a continuation needs to be pushed, push it in the continuation store */
        case ActionPush(frame, e, env, store : RefCountingStore[Addr, Abs], _) => {
          val next = NormalKontAddress(e, t)
          val (kstore1,addrs) = kstore.extendRC(next, Kont(frame,adr))
          (State(ControlEval(e, env), store, kstore1, next, Timestamp[Time].tick(t)),addrs)
        }
        /* When a value needs to be evaluated, we go to an eval state */
        case ActionEval(e, env, store : RefCountingStore[Addr, Abs], _) => (State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t)),Iterable.empty)
        /* When a function is stepped in, we also go to an eval state */
        case ActionStepIn(fexp, _, e, env, store : RefCountingStore[Addr, Abs], _, _) => (State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t, fexp)),Iterable.empty)
        /* When an error is reached, we go to an error state */
        case ActionError(err) => (State(ControlError(err), store : RefCountingStore[Addr, Abs], kstore, adr, Timestamp[Time].tick(t)),Iterable.empty)
      })

    /**
     * Computes the set of states that follow the current state
     */
    private def nextStates(sem: Semantics[Exp, Abs, Addr, Time]): Iterable[(State,Iterable[Addr])] = control match {
      /* In a eval state, call the semantic's evaluation method */
      case ControlEval(e, env) => integrate(a, sem.stepEval(e, env, store, t))
      /* In a continuation state, call the semantics' continuation method */
      case ControlKont(v) => kstore.lookup(a).toIterable.flatMap({
        case Kont(frame, next) => integrate(next, sem.stepKont(v, frame, store, t))
      })
      /* In an error state, the state is not able to make a step */
      case ControlError(_) => Iterable.empty
    }

    def step(sem: Semantics[Exp,Abs,Addr,Time]): Iterable[State] = nextStates(sem).map({
      case (State(control0,store0,kstore0,a0,t0),addrs) => {
        val (kstore1,decr) = kstore0.changeRoot(a,a0)
        val addedRefs = control0.references
        val removedRefs = control.references
        val store1 = store0.incRefs(addedRefs).incRefs(addrs).decRefs(removedRefs).decRefs(decr)
        State(control0,store1,kstore1,a0,t0)
      }
    })

    def stepAnalysis[L](analysis: Analysis[L, Exp, Abs, Addr, Time], current: L): L = ???

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
    def inject(exp: Exp, envBindings: Iterable[(String, Addr)], storeBindings: Iterable[(Addr, Abs)]) = {
      val control = ControlEval(exp, Environment.empty[Addr])
      val store = Store.refCountStore[Addr, Abs](storeBindings)
      val kstore = KontStore.refCountStore[Addr,KontAddr] //.incRef(HaltKontAddress)
      State(control, store, kstore, HaltKontAddress, Timestamp[Time].initial(""))
    }
    import scala.language.implicitConversions

    implicit val graphNode = new GraphNode[State, Unit] {
      override def label(s: State) = s.toString
      override def color(s: State) = s.control match {
        case _: ControlEval => Colors.White
        case _: ControlKont if s.halted => Colors.Green
        case _: ControlKont => Colors.Yellow
        case _: ControlError => Colors.Red
      }

      import org.json4s._
      import org.json4s.JsonDSL._
      import org.json4s.jackson.JsonMethods._
      import JSON._
      override def content(s: State) =
        ("control" -> s.control) ~ ("store" -> s.store) ~ ("kstore" -> s.kstore) ~ ("kont" -> s.a.toString) ~ ("time" -> s.t.toString)
    }
  }

  type G = Option[Graph[State, Unit, Unit]]
  case class AAMOutput(halted: Set[State], numberOfStates: Int, time: Double, graph: G, timedOut: Boolean)
      extends Output {
    def finalValues = halted.flatMap(st => st.control match {
      case ControlKont(v) => Set[Abs](v)
      case _ => Set[Abs]()
    })

    def toFile(path: String)(output: GraphOutput) = graph match {
      case Some(g) => output.toFile(g, ())(path)
      case None => println("Not generating graph because no graph was computed")
    }
  }

  /**
   * Performs the evaluation of an expression @param exp (more generally, a
   * program) under the given semantics @param sem. If @param graph is true, it
   * will compute and generate the graph corresponding to the execution of the
   * program (otherwise it will just visit every reachable state). A @param
   * timeout can also be given.
   */
   def eval(exp: Exp, sem: Semantics[Exp, Abs, Addr, Time], graph: Boolean, timeout: Timeout): Output = {
     val s0 = State.inject(exp, Iterable.empty, sem.initialStore)
     var worklist = scala.collection.mutable.MutableList[State](s0)
     val visited = scala.collection.mutable.Set[State]()
     while (!(timeout.reached || worklist.isEmpty)) {
       val s = worklist.head
       worklist = worklist.tail
       if (!visited.contains(s)) {
         visited += s
         if (!(s.halted)) {
           val succs = s.step(sem)
           worklist ++= succs
         }
       }
     }
     AAMOutput(Set(), visited.size, timeout.time, None, timeout.reached)
   }
}
