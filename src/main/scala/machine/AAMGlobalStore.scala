import scala.language.higherKinds


class AAMGlobalStore[Exp : Expression, Abs : JoinLattice, Time : Timestamp]
  extends EvalKontMachine[Exp,Abs,ClassicalAddress.A,Time] {

  type Addr = ClassicalAddress.A

  def name = "AAMGlobalStore"

  type G = Option[Graph[State, Unit, Unit]]
  type VStore = DeltaStore[Addr,Abs]
  type KStore = KontStore[KontAddr]

  /* KONTINUATION ADDRESSES */
  trait KontAddr
  case class NormalKontAddress(exp: Exp, env: Environment[Addr]) extends KontAddr {
    override def toString = s"NormalKontAddress($exp)"
  }
  case object HaltKontAddress extends KontAddr {
    override def toString = "HaltKontAddress"
  }
  object KontAddr {
    implicit object KontAddrKontAddress extends KontAddress[KontAddr]
  }

  /* (STORELESS) STATES */
  case class State(control: Control, next: KontAddr, ctx: Time) {
    override def toString = control.toString
    def integrate(next: KontAddr, vstore: VStore, actions: Set[Action[Exp,Abs,Addr]]): List[(State,VStore,Option[(KontAddr,Kont[KontAddr])])] = actions.toList.map({
      case ActionReachedValue(v, store : VStore, _) =>
        (State(ControlKont(v), next, Timestamp[Time].tick(ctx)), store, None)
      case ActionPush(frame, e, env, store : VStore, _) => {
        val kontAddr = NormalKontAddress(e,env)
        (State(ControlEval(e,env),kontAddr, Timestamp[Time].tick(ctx)), store, Some((kontAddr,Kont(frame,next))))
      }
      case ActionEval(e, env, store : VStore, _) =>
        (State(ControlEval(e,env),next,Timestamp[Time].tick(ctx)), store, None)
      case ActionStepIn(fexp, _, e, env, store : VStore, _, _) =>
        (State(ControlEval(e,env), next, Timestamp[Time].tick(ctx,fexp)), store, None)
      case ActionError(err) =>
        (State(ControlError(err), next, Timestamp[Time].tick(ctx)), vstore, None)
    })

    def step(sem: Semantics[Exp,Abs,Addr,Time], vstore: VStore, kstore: KStore): List[(State,VStore,Option[(KontAddr,Kont[KontAddr])])] = control match {
      case ControlEval(exp,env) => integrate(next, vstore, sem.stepEval(exp,env,vstore,ctx))
      case ControlKont(vlu) => kstore.lookup(next).toList.flatMap({
        case Kont(frm,adr) => integrate(adr, vstore, sem.stepKont(vlu,frm,vstore,ctx))
      })
      case ControlError(err) => List()
    }
    def halted = control match {
      case ControlEval(_,_) => false
      case ControlKont(_) => next == HaltKontAddress
      case ControlError(_) => true
    }
  }
  object State {
    import scala.language.implicitConversions
    implicit val graphNode = new GraphNode[State, Unit] {
      override def label(s: State) = s.toString
      override def color(s: State) = s.control match {
        case _: ControlEval => Colors.White
        case _: ControlKont if !s.halted => Colors.Yellow
        case _: ControlKont => Colors.Green
        case _: ControlError => Colors.Red
      }
    }
  }

  /* OUTPUT */
  case class AAMGlobalStoreOutput(history: List[(VStore,KStore,Set[State])], timeout: Timeout, graph: G) extends Output {
    def time = timeout.time
    def timedOut = timeout.reached
    def finalValues = history.foldLeft(Set[Abs]())((acc,gen) => gen._3.collect(state =>
      state.control match {
        case ControlKont(v) if state.next == HaltKontAddress => v
      }))
    def numberOfStates = history.foldLeft(0)((acc,gen) => acc + gen._3.size)
    def toFile(path: String)(output: GraphOutput) = graph match {
      case Some(g) => output.toFile(g, ())(path)
      case None => println("Not generating graph because no graph was computed")
    }
  }

  /* GLOBAL STORE AAM */
  def stepStates(states: List[State], sem: Semantics[Exp,Abs,Addr,Time], vstore: VStore, kstore: KStore): (List[(State,State)],Option[(VStore,KStore)]) = {
      val (newStates,newVStore,newKStore,changed) = states.foldLeft((List[(State,State)](),vstore,kstore,false))({ case ((prevStates,prevVStore,prevKStore,prevChanged),state) => {
        val succs = state.step(sem,vstore,kstore)
        val updatedStates = succs.map({ case (succ,_,_) => (state,succ) }) ++ prevStates
        val (updatedVStore,vchanged) = succs.foldLeft((prevVStore,false))({ case ((vs,ch),(_,newVS,_)) => {
          val dlt = newVS.delta.get
          if (dlt.isEmpty) { (vs, ch) } else { (vs.addDelta(dlt), true) }
        }})
        val (updatedKStore,kchanged) = succs.flatMap(_._3).foldLeft((prevKStore,false))({ case ((ks,ch),(adr,kon)) =>
                                              if(ks.lookup(adr).contains(kon)) { (ks, ch) } else { (ks.extend(adr,kon), true) }
                                            })
        val updatedChanged = prevChanged || vchanged || kchanged
        (updatedStates,updatedVStore,updatedKStore,updatedChanged)
      }})
      (newStates, if (changed) { Some((newVStore,newKStore)) } else { None })
  }

  /* ANALYSIS */
  private def addToFrontier(states: List[State], visited: Set[State]): (List[State],Set[State]) =
    states.foldLeft(List[State](),visited)({ case ((prevFrontier,prevVisited),succ) => {
      if (prevVisited.contains(succ)) {
        (prevFrontier,prevVisited)
      } else if (succ.halted) {
        (prevFrontier, prevVisited + succ)
      } else {
        (succ :: prevFrontier, prevVisited + succ)
      }
    }})

  def eval(exp: Exp, sem: Semantics[Exp,Abs,Addr,Time], graph: Boolean, timeout: Timeout): Output = {

    //AdaptiveAddress.init()

    @scala.annotation.tailrec
    def loop(frontier: List[State], vstore: VStore, kstore: KStore, visited: Set[State], history: List[(VStore,KStore,Set[State])], graph: G): AAMGlobalStoreOutput = {
      if (timeout.reached || frontier.isEmpty) {
        AAMGlobalStoreOutput((vstore,kstore,visited) :: history, timeout, graph)
      } else {
        val (newEdges,newStores) = stepStates(frontier,sem,vstore,kstore)
        val newGraph = graph.map(_.addEdges(newEdges.map({case (from,to) => (from,(),to)})))
        val newStates = newEdges.map(_._2)
        newStates.foreach(s => println((s.control,s.ctx,s.next)))
        if(newStores.isDefined) {
          val (newVStore,newKStore) = newStores.get
          val newHistory = (vstore,kstore,visited) :: history
          val (newFrontier,newVisited) = addToFrontier(newStates,Set())
          loop(newFrontier,newVStore,newKStore,newVisited,newHistory,newGraph)
        } else {
          val (newFrontier,newVisited) = addToFrontier(newStates,visited)
          loop(newFrontier,vstore,kstore,newVisited,history,newGraph)
        }
      }
    }

    val initialEnv = Environment.initial[Addr](sem.initialEnv)
    val initialSto = DeltaStore[Addr,Abs](sem.initialStore.toMap,Map())
    val initialStk = KontStore.empty[KontAddr]
    val initialSta = State(ControlEval(exp,initialEnv),HaltKontAddress,Timestamp[Time].initial(""))
    val initialGra : G = if (graph) { Some(Graph.empty) } else { None }

    def run(): Output = {
      try {
        val res = loop(List(initialSta),initialSto,initialStk,Set(initialSta),List(),initialGra)
        //println(AdaptiveAddress.config)
        res
      } catch {
        case AdaptiveAddress.AddrOverflow(id) => {
          //println(s"Switching to monovariant analysis for ${id}...")
          //AdaptiveAddress.reset()
          run()
        }
      }
    }

    run()
  }
}

object Main {

  import Util._

  val OUTPUT_DIR = "/Users/nvanes/Desktop/outputs/"

  val boundedInt = new BoundedInteger(5)
  val lattice: SchemeLattice = new MakeSchemeLattice[Type.S, Concrete.B, boundedInt.I, Type.F, Type.C, Type.Sym](false)
  implicit val isSchemeLattice: IsSchemeLattice[lattice.L] = lattice.isSchemeLattice
  val context = SCFA
  implicit val isTimestamp = context.isTimestamp
  val machine = new AAMGlobalStore[SchemeExp, lattice.L, context.T]
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, context.T](new SchemePrimitives[ClassicalAddress.A, lattice.L])

  def main(args: Array[String]) = {
    import java.io.File
    val dir = new File("test/")
    val files = dir.listFiles.map(_.getName).filter(_.endsWith(".scm")).toList
    //files.foreach(runBenchmark(_))
    runBenchmark("count")
  }

  def runBenchmark(name: String): Unit = {
    val location = "test/" + name + ".scm"
    replOrFile(Some(location), program => {
      println(s"Running benchmark: ${name.toUpperCase}")
      val result = machine.eval(sem.parse(program), sem, true, Timeout.start(None))
      println(s"States visited: ${result.numberOfStates}")
      result.toPng(OUTPUT_DIR + name + "-" + isTimestamp.name + ".png")
    })
  }
}
