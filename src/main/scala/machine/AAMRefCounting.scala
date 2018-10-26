import java.util.UUID

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
  var count = 0

  trait KontAddr
  case class NormalKontAddress(exp: Exp, time: Time) extends KontAddr {
    override def toString = s"$exp"
    lazy val storedHashCode = (exp,time).hashCode
    override def hashCode = storedHashCode
  }
  case class CallAddress(fexp: Exp, time: Time) extends KontAddr {
    override def toString = s"Call($fexp)"
    lazy val storedHashCode = (fexp,time).hashCode
    override def hashCode = storedHashCode
  }
  case object HaltKontAddress extends KontAddr {
    override def toString = "HALT"
    override def hashCode = 0
  }
  object KontAddr {
    implicit object KontAddrKontAddress extends KontAddress[KontAddr]
  }

  case object ReturnFrame extends Frame {
    val refs = Set()
  }

  case class State(control: Control, store: RefCountingStore[Addr, Abs], kstore: RefCountingKontStore[Addr,KontAddr], a: KontAddr, t: Time) {
    override def toString = control.toString
    lazy val storedHashCode = (control, store, kstore, a, t).hashCode()
    override def hashCode = storedHashCode

    override def equals(that: Any): Boolean = that match {
      case s : State => this.storedHashCode == s.storedHashCode && this.control == s.control && this.store == s.store && this.kstore == s.kstore && this.a == s.a && this.t == s.t
      case _ => false
    }

    private def integrate(adr: KontAddr, actions: Set[Action[Exp, Abs, Addr]]): List[(State,Iterable[Addr])] =
      actions.toList.map({
        case ActionReachedValue(v, store : RefCountingStore[Addr, Abs], _) =>
          (State(ControlKont(v), store, kstore, adr, Timestamp[Time].tick(t)), Iterable.empty)
        case ActionPush(frame, e, env, store : RefCountingStore[Addr, Abs], _) =>
          val next = NormalKontAddress(e, t)
          val (kstore1,addrs) = kstore.extendRC(next, Kont(frame, adr))
          (State(ControlEval(e, env), store, kstore1, next, Timestamp[Time].tick(t)),addrs)
        case ActionEval(e, env, store : RefCountingStore[Addr, Abs], _) =>
          (State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t)), Iterable.empty)
        case ActionStepIn(fexp, _, e, env, store : RefCountingStore[Addr, Abs], _, _) =>
          val next = CallAddress(fexp, t)
          val kstore1 = kstore.extend(next, Kont(ReturnFrame, adr))
          (State(ControlEval(e, env), store, kstore1, next, Timestamp[Time].tick(t, fexp)), Iterable.empty)
        case ActionError(err) =>
          (State(ControlError(err), store : RefCountingStore[Addr, Abs], kstore, adr, Timestamp[Time].tick(t)), Iterable.empty)
      })

    private def nextStates(sem: Semantics[Exp, Abs, Addr, Time]): List[(State,Iterable[Addr])] = control match {
      case ControlEval(e, env) => integrate(a, sem.stepEval(e, env, store, t))
      case ControlKont(v) => kstore.lookup(a).toList.flatMap({
        case Kont(ReturnFrame, next) => List((State(ControlKont(v), store, kstore, next, t), Iterable.empty))
        case Kont(frame, next) => integrate(next, sem.stepKont(v, frame, store, t))
      })
      case ControlError(_) => List()
    }

    def step(sem: Semantics[Exp,Abs,Addr,Time]): List[State] = nextStates(sem).map({
      case (State(control0,store0,kstore0,a0,t0), addrs) => {
        val (kstore1,decr) = kstore0.changeRoot(a,a0)
        val addedRefs = control0.references -- control.references
        val removedRefs = control.references -- control0.references
        val store1 = store0.incRefs(addedRefs).incRefs(addrs).decRefs(removedRefs).decRefs(decr)
        /* DEBUGGING */
        if(!kstore.containsIsolatedCycle(a) && kstore1.containsIsolatedCycle(a0)) {
          count = count + 1
          println(s"$control -> $control0")
          kstore.toPng(s"/Users/nvanes/Desktop/data/${count}-A.png",a)
          kstore1.toPng(s"/Users/nvanes/Desktop/data/${count}-B.png",a0)
          throw new Exception("Should not happen!")
        }
        /* END DEBUGGING */
        State(control0,store1,kstore1,a0,t0)
      }
    })

    def stepAnalysis[L](analysis: Analysis[L, Exp, Abs, Addr, Time], current: L): L = ???

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

   def eval(exp: Exp, sem: Semantics[Exp, Abs, Addr, Time], graph: Boolean, timeout: Timeout): Output = {
     val s0 = State.inject(exp, Iterable.empty, sem.initialStore)
     val worklist = scala.collection.mutable.Queue[State](s0)
     val visited = scala.collection.mutable.Set[State]()
     while (!(timeout.reached || worklist.isEmpty)) {
       val s = worklist.dequeue
       if (visited.add(s) && !s.halted) {
         val succs = s.step(sem)
         succs.foreach { succ => worklist.enqueue(succ) }
       }
     }
     AAMOutput(Set(), visited.size, timeout.time, None, timeout.reached)
   }
}
