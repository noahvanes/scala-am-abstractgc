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
class AAMOriginal[Exp : Expression, Abs : JoinLattice, Addr : Address, Time : Timestamp]
    extends EvalKontMachine[Exp, Abs, Addr, Time] {
  def name = "AAMOriginal"

  trait KontAddr
  case class NormalKontAddress(exp: Exp, time: Time) extends KontAddr {
    override def toString = s"$exp"
    lazy val storedHashCode = (exp,time).hashCode
    override def hashCode = storedHashCode
  }
  case object HaltKontAddress extends KontAddr {
    override def toString = "HALT"
    override def hashCode = 0
  }

  object KontAddr {
    implicit object KontAddrKontAddress extends KontAddress[KontAddr]
  }

  case class State(control: Control, store: Store[Addr, Abs], kstore: KontStore[KontAddr], a: KontAddr, t: Time) {
    override def toString = control.toString

    lazy val storedHashCode = (control, store, kstore, a, t).hashCode()
    override def hashCode = storedHashCode

    override def equals(that: Any): Boolean = that match {
      case s : State => this.storedHashCode == s.storedHashCode && this.control == s.control && this.store == s.store && this.kstore == s.kstore && this.a == s.a && this.t == s.t
      case _ => false
    }

    def subsumes(that: State): Boolean = control.subsumes(that.control) && store.subsumes(that.store) && a == that.a && kstore.subsumes(that.kstore) && t == that.t

    private def integrate(adr: KontAddr, actions: Set[Action[Exp, Abs, Addr]]): List[State] =
      actions.toList.map({
        case ActionReachedValue(v, store, _) => State(ControlKont(v), store, kstore, adr, Timestamp[Time].tick(t))
        case ActionPush(frame, e, env, store, _) => {
          val next = NormalKontAddress(e, t)
          State(ControlEval(e, env), store, kstore.extend(next, Kont(frame, adr)), next, Timestamp[Time].tick(t))
        }
        case ActionEval(e, env, store, _) => State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t))
        case ActionStepIn(fexp, _, e, env, store, _, _) =>
          State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t, fexp))
        case ActionCall(fn, fexp, args, store, _) =>
          State(ControlCall(fn,fexp,args),store,kstore,adr,Timestamp[Time].tick(t))
        case ActionError(err) => State(ControlError(err), store, kstore, adr, Timestamp[Time].tick(t))
      })

    def step(sem: Semantics[Exp, Abs, Addr, Time]): List[State] = control match {
      case ControlEval(e, env) => integrate(a, sem.stepEval(e, env, store, t))
      case ControlCall(fn,fexp,args) => integrate(a, sem.stepCall(fn,fexp,args,store,t))
      case ControlKont(v) => kstore.lookup(a).toList.flatMap({
        case Kont(frame, next) => integrate(next, sem.stepKont(v, frame, store, t))
      })
      case ControlError(_) => List()
    }

    def stepAnalysis[L](analysis: Analysis[L, Exp, Abs, Addr, Time], current: L): L = ???

    def halted: Boolean = control match {
      case ControlEval(_, _) | ControlCall(_,_,_) => false
      case ControlKont(v) => a == HaltKontAddress
      case ControlError(_) => true
    }
  }
  object State {
    def inject(exp: Exp, env: Iterable[(String, Addr)], store: Iterable[(Addr, Abs)]) =
      State(ControlEval(exp, Environment.initial[Addr](env)),
        Store.initial[Addr, Abs](store), KontStore.empty[KontAddr], HaltKontAddress, Timestamp[Time].initial(""))
    import scala.language.implicitConversions

    implicit val graphNode = new GraphNode[State, Unit] {
      override def label(s: State) = s.toString
      override def color(s: State) = s.control match {
        case _: ControlEval => Colors.White
        case _: ControlKont if s.halted => Colors.Green
        case _: ControlKont => Colors.Yellow
        case _: ControlError => Colors.Red
      }
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
     var halted = Set[State]()
     while (!(timeout.reached || worklist.isEmpty)) {
       val s = worklist.dequeue
       if (visited.add(s)) {
         if (s.halted) {
           halted = halted + s
         } else {
           worklist ++= s.step(sem)
         }
       }
     }
     AAMOutput(halted, visited.size, timeout.time, None, timeout.reached)
   }
}
