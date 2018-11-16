
object Main {

  import Util._
  import scala.concurrent.duration.Duration

  val INPUT_DIR = "test/"
  val OUTPUT_DIR = "/Users/nvanes/Desktop/outputs/"
  val OUTPUT_PNG = false
  val RUNS = 1
  val TIMEOUT = Duration(10, "seconds")

  val bounded = new BoundedInteger(7)
  val lattice = new MakeSchemeLattice[Type.S, Concrete.B, bounded.I, Type.F, Type.C, Type.Sym](false)
  val address = ClassicalAddress
  val time = ZeroCFA
  implicit val isTimestamp = time.isTimestamp
  val sem = new SchemeSemantics[lattice.L, address.A, time.T](new SchemePrimitives[address.A, lattice.L])

  trait GCStrategy { def name: String }
  case object NoGC extends GCStrategy { def name = "NoGC" }
  case object RefCounting extends GCStrategy { def name = "RefCounting" }
  case object ClassicalGC extends GCStrategy { def name = "ClassicalGC" }

  def main(args: Array[String]): Unit = {
    val current = "primtest"
    //benchmark(current,NoGC)
    //benchmark(current,ClassicalGC)
    benchmark(current,RefCounting)
  }

  def benchmark(name: String, gcStrategy: GCStrategy): Unit = {
    val machine = gcStrategy match {
      case NoGC => new AAM[SchemeExp, lattice.L, address.A, time.T]
      case RefCounting => new AAMRefCounting[SchemeExp, lattice.L, address.A, time.T]
      case ClassicalGC => new AAMGC[SchemeExp, lattice.L, address.A, time.T]
    }
    val benchName = s"${name}-${time.isTimestamp.name}-${gcStrategy.name}"
    val file = INPUT_DIR + name + ".scm"
    replOrFile(Some(file), text => {
      val program = SchemeUtils.computeFreeVar(SchemeUtils.inline(sem.parse(text),sem.initialEnv.toMap))
      println(s">>> RUNNING BENCHMARK ${benchName}")
      var result: EvalKontMachine[SchemeExp,lattice.L,address.A,time.T]#Output = null
      val timings = (1 to RUNS).map( i => {
        print(".")
        val t0 = System.nanoTime()
        result = machine.eval(program,sem,OUTPUT_PNG,Timeout.start(TIMEOUT))
        val t1 = System.nanoTime()
        (t1-t0)/1000000
      })
      println()
      if (result.timedOut) {
        println(s"<< TIMEOUT after ${result.numberOfStates} states >>")
      } else {
        val bestTime = timings.min
        println(s"states: ${result.numberOfStates}")
        println(s"elapsed: ${bestTime}ms")
        println(s"rate: ${result.numberOfStates/bestTime} states/ms")
      }
      if (OUTPUT_PNG) { result.toPng(OUTPUT_DIR + benchName + ".png") }
      println(s"<<< FINISHED BENCHMARK ${benchName}")
    })
  }
}
