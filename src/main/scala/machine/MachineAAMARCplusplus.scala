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
class MachineAAMARCplusplus[Exp : Expression, Abs : JoinLattice, Addr : Address, Time : Timestamp]
    extends EvalKontMachine[Exp, Abs, Addr, Time] {
  def name = "MachineAAMARCplusplus"

  var count = 0

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

  case class State(control: Control, store: RefCountingStore[Addr, Abs], kstore: RefCountingKontStore[Addr,KontAddr], adr: KontAddr, t: Time) {
    override def toString = control.toString
    lazy val storedHashCode = (control, store, kstore, adr, t).hashCode()
    override def hashCode = storedHashCode

    override def equals(that: Any): Boolean = that match {
      case s : State => this.storedHashCode == s.storedHashCode && this.control == s.control && this.store == s.store && this.kstore == s.kstore && this.adr == s.adr && this.t == s.t
      case _ => false
    }

    private def updateRefs(prevControl: Control, frmrefs: Iterable[Addr], stkrefs: Iterable[Addr]): State = {
      val addedRefs = control.references -- prevControl.references
      val removedRefs = prevControl.references -- control.references
      val updatedStore = store.incRefs(addedRefs).incRefs(stkrefs).decRefs(removedRefs).decRefs(frmrefs).collect()
      this.copy(store = updatedStore)
    }

    private def integrate(frmrefs: Iterable[Addr], actions: Set[Action[Exp, Abs, Addr]]): List[State] =
      actions.toList.map({
        case ActionReachedValue(v, store : RefCountingStore[Addr, Abs], _) =>
          State(ControlKont(v), store, kstore, adr, Timestamp[Time].tick(t)).updateRefs(control, frmrefs, Iterable.empty)
        case ActionPush(frame, e, env, store : RefCountingStore[Addr, Abs], _) =>
          val next = NormalKontAddress(e, t)
          val (kstore1,addrs) = kstore.push(next, frame)
          State(ControlEval(e, env), store, kstore1, next, Timestamp[Time].tick(t)).updateRefs(control, frmrefs, addrs)
        case ActionEval(e, env, store : RefCountingStore[Addr, Abs], _) =>
          State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t)).updateRefs(control, frmrefs, Iterable.empty)
        case ActionStepIn(fexp, _, e, env, store : RefCountingStore[Addr, Abs], _, _) =>
          State(ControlEval(e, env), store, kstore, adr, Timestamp[Time].tick(t, fexp)).updateRefs(control, frmrefs, Iterable.empty)
        case ActionCall(fn, fexp, args, store : RefCountingStore[Addr, Abs], _) =>
          State(ControlCall(fn,fexp,args), store, kstore, adr, Timestamp[Time].tick(t)).updateRefs(control, frmrefs, Iterable.empty)
        case ActionError(err) =>
          State(ControlError(err), store, kstore, adr, Timestamp[Time].tick(t)).updateRefs(control, frmrefs, Iterable.empty)
      })

    def step(sem: Semantics[Exp, Abs, Addr, Time]): List[State] = control match {
      case ControlEval(e, env) =>
        this.integrate(Iterable.empty, sem.stepEval(e, env, store, t))
      case ControlCall(fn,fexp,args) =>
        this.integrate(Iterable.empty, sem.stepCall(fn, fexp, args, store, t))
      case ControlKont(v) =>
        kstore.lookup(adr).toList.flatMap({
          case Kont(frame, next) =>
            val frmrefs = frame.references
            val (kstore1, decr) = kstore.pop(next)
            val store1 = store.incRefs(frmrefs).decRefs(decr).collect()
            val updatedState = this.copy(adr = next, kstore = kstore1, store = store1)
            updatedState.integrate(frmrefs, sem.stepKont(v, frame, store1, t))
        })
      case ControlError(_) => List()
    }

    /*
    def stepSafe(sem: Semantics[Exp,Abs,Addr,Time]): List[State] = {
      count = count + 1
      val succs = this.step(sem)
      succs.foreach(succ => {
        var counts = succ.kstore.calcCounts()
        succ.control.references.foreach(ref => counts = counts.updated(ref, counts(ref) + 1))
        val calculatedCounts = succ.store.calcCounts(counts)
        if (calculatedCounts != succ.store.in) {
          val current = this
          val time = count
          println()
          println(calculatedCounts)
          println(succ.store.in)
          //println(s"[$count] ${this.control} -> ${succ.control}")
          throw new Exception("Invalid reference counts")
        }
      })
      succs
    }

    def checkForGarbage(sem: Semantics[Exp,Abs,Addr,Time]): Unit = {
      val storeRoots = control.references ++ kstore.content.flatMap(p => p._2._3) ++ sem.initialEnv.map(_._2)
      if(kstore.garbage().nonEmpty) {
        throw new Exception("garbage in the kstore!")
      }
      if(store.garbage(storeRoots).nonEmpty) {
        throw new Exception(s"garbage in the store!: ${store.garbage(storeRoots)}")
      }
    }
    */


    def stepAnalysis[L](analysis: Analysis[L, Exp, Abs, Addr, Time], current: L): L = ???

    def halted: Boolean = control match {
      case ControlEval(_, _) | ControlCall(_,_,_) => false
      case ControlKont(v) => adr == HaltKontAddress
      case ControlError(_) => true
    }
  }

  object State {

    def inject(exp: Exp, envBindings: Iterable[(String, Addr)], storeBindings: Iterable[(Addr, Abs)]) = {
      val control = ControlEval(exp, Environment.empty[Addr])
      val store = Store.refCountStore[Addr, Abs](storeBindings)
      val kstore = KontStore.refCountStore[Addr,KontAddr](HaltKontAddress)
      State(control, store, kstore, HaltKontAddress, Timestamp[Time].initial(""))
    }

    import scala.language.implicitConversions
    implicit val graphNode = new GraphNode[State, Unit] {
      override def label(s: State) = " "
      override def color(s: State) = Colors.White
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
    val s0           = State.inject(exp, Iterable.empty, sem.initialStore)
    val worklist     = scala.collection.mutable.Queue[State](s0)
    val visited      = scala.collection.mutable.Set[State]()
    var halted       = Set[State]()
    var currentGraph = Graph.empty[State,Unit,Unit]
    while (!(timeout.reached || worklist.isEmpty)) {
      val s = worklist.dequeue
      if (visited.add(s)) {
        if (s.halted) {
          halted = halted + s
        } else {
          val succs = s.step(sem)
          worklist ++= succs
          if (graph) {
            currentGraph = currentGraph.addEdges(succs.map((s,(),_)))
          }
        }
      }
    }
    AAMOutput(halted, visited.size, timeout.time, if (graph) { Some(currentGraph) } else { None }, timeout.reached)
  }
}
