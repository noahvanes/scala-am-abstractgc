object Main {

  import Util._
  import scala.io.Source
  import scala.concurrent.duration.Duration
  import scala.language.existentials
  import java.io.{BufferedWriter, FileWriter}
  import scala.collection.JavaConversions._
  import au.com.bytecode.opencsv.CSVWriter
  import java.io.File

  /* GLOBAL CONFIGURATION */

  val BENCHMARK_DIR = "benchmarks"
  val OUTPUT_DIR = "output"

  /* MACHINE CONFIGURATIONS */

  abstract case class MachineConfiguration(lattice: SchemeLattice, timestamp: TimestampWrapper) {

    val machine: AbstractMachine[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]

    type Output = machine.Output
    implicit val isSchemeLattice: IsSchemeLattice[lattice.L] = lattice.isSchemeLattice
    implicit val isTimeStamp: Timestamp[timestamp.T] = timestamp.isTimestamp
    val primitives = new SchemePrimitives[ClassicalAddress.A, lattice.L]
    val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, timestamp.T](primitives)

    def run(program: SchemeExp, timeout: Timeout, graph: Boolean): Output = machine.eval(program,sem,graph,timeout)
  }

  trait DefaultAAM extends MachineConfiguration {
    val machine = new AAMOriginal[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait TracingGC extends MachineConfiguration {
    val machine = new AAMGC[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait TracingGCAlt extends MachineConfiguration {
    val machine = new AAMGCAlt[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait RefCounting extends MachineConfiguration {
    val machine = new AAMRefCounting[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait RefCountingKont extends MachineConfiguration {
    val machine = new AAMRefCountingKont[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait RefCountingVanilla extends MachineConfiguration {
    val machine = new AAMRefCountingVanilla[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }

  // some lattices
  private val concreteLattice = new MakeSchemeLattice[Concrete.S, Concrete.B, Concrete.I, Concrete.F, Concrete.C, Concrete.Sym](false)
  private val typeLattice = new MakeSchemeLattice[Type.S, Concrete.B, Type.I, Type.F, Type.C, Type.Sym](false)
  private val constantPropLattice = new MakeSchemeLattice[ConstantPropagation.S, Concrete.B, ConstantPropagation.I, ConstantPropagation.F, ConstantPropagation.C, ConstantPropagation.Sym](false)
  private def boundedIntLattice(bound: Int) = {
    val bounded = new BoundedInteger(bound)
    new MakeSchemeLattice[Type.S, Concrete.B, bounded.I, Type.F, Type.C, Type.Sym](false)
  }
  private def kPointsToLattice(k: Int) = {
    val kpts = new KPointsTo(k)
    new MakeSchemeLattice[kpts.S, Concrete.B, kpts.I, kpts.F, kpts.C, kpts.S](false)
  }

  /* BENCHMARKING */

  case class BenchmarkResult(name: String, machine: MachineConfiguration, states: Int, time: Option[Long])

  case class Benchmark(name: String, location: String) {

    assume({ val f = new File(location) ; f.exists() && f.isFile })

    override def toString = s"BENCMARK-$name"

    def loadSource(): String = {
      val data = Source.fromFile(location)
      try data.mkString finally data.close()
    }

    def run(machine: MachineConfiguration, graph: Boolean): BenchmarkResult = {

      // TODO: currently, our approach is only implemented for Scheme programs
      val source = loadSource()
      val program = SchemeUtils.computeFreeVar(SchemeUtils.inline(machine.sem.parse(source), machine.sem.initialEnv.toMap))

      print(s">> RUNNING BENCHMARK $name [${machine.machine.name}]")

      /* WARMUP RUNS */
      var warmupRun = 0
      var warmupTimeout = Timeout.start(Duration(2,"minutes"))
      while (warmupRun < 50) {
        print(".")
        machine.run(program, warmupTimeout, graph=false)
        warmupRun = warmupRun + 1
      }

      /* MAIN BENCHMARK */
      var currentRun = 0
      var currentTimeout = Timeout.start(Duration(30,"minutes"))
      var lastResult: machine.Output = null
      var ts = List[Long]()
      while (currentRun < 30) {
        print("*")
        val keep = lastResult
        val t0 = System.nanoTime()
        lastResult = machine.run(program, currentTimeout, graph=false)
        val t1 = System.nanoTime()
        if (lastResult.timedOut) {
          if (ts.isEmpty) {
            println(s"TIMEOUT (states: ${lastResult.numberOfStates})")
            return BenchmarkResult(name, machine, lastResult.numberOfStates, None)
          } else {
            val mean = ts.sum / ts.size
            println(s"(states: ${keep.numberOfStates}; elapsed: ${mean}ms)")
            return BenchmarkResult(name, machine, keep.numberOfStates, Some(mean))
          }
        }
        val t = (t1 - t0) / 1000000
        ts = t :: ts
        currentRun = currentRun + 1
      }
      /* FINAL RESULTS */
      val mean = ts.sum / ts.size
      println(s"(states: ${lastResult.numberOfStates} ; elapsed: ${mean}ms)")
      BenchmarkResult(name, machine, lastResult.numberOfStates, Some(mean))
    }
  }

  def run(benchmarks: List[Benchmark], machines: List[MachineConfiguration], graph: Boolean = false): List[BenchmarkResult]
    = benchmarks.flatMap(benchmark => machines.map(machine => benchmark.run(machine, graph)))

  def exportCSV(results: List[BenchmarkResult], filename: String): Unit = {
    val outputPath = s"$OUTPUT_DIR/$filename.csv"
    val outputFile = new BufferedWriter(new FileWriter(outputPath))
    val csvWriter = new CSVWriter(outputFile)
    var csvContents = List(Array("benchmark", "number of states", "time elapsed"))
    results foreach { b =>
      val name = s"${b.name}-${b.machine.machine.name}"
      val count = b.states.toString
      val time = if (b.time.isDefined) { b.time.get.toString } else { "timeout" }
      csvContents = Array(name, count, time) :: csvContents
    }
    csvWriter.writeAll(csvContents.reverse)
    csvWriter.close()
  }

  /* BENCHMARKS */

  private implicit def benchmarkToList(b: Benchmark): List[Benchmark] = List(b)
  private implicit def machineToList(m: MachineConfiguration): List[MachineConfiguration] = List(m)
  private def loadBenchmark(name: String, subfolder: String) = Benchmark(name, s"$BENCHMARK_DIR/$subfolder/$name.scm")

  // Gabriel benchmarks
  private def loadGabrielBenchmark(name: String) = loadBenchmark(name, "gabriel")
  private val boyer   = loadGabrielBenchmark("boyer")
  private val browse  = loadGabrielBenchmark("browse")
  private val cpstak  = loadGabrielBenchmark("cpstak")
  private val dderiv  = loadGabrielBenchmark("dderiv")
  private val deriv   = loadGabrielBenchmark("deriv")
  private val destruc = loadGabrielBenchmark("destruc")
  private val diviter = loadGabrielBenchmark("diviter")
  private val divrec  = loadGabrielBenchmark("divrec")
  private val puzzle  = loadGabrielBenchmark("puzzle")
  private val takl    = loadGabrielBenchmark("takl")
  private val triangl = loadGabrielBenchmark("triangl")
  private val gabrielBenchmarks = List(boyer, browse, cpstak, dderiv, deriv, destruc, diviter, divrec, puzzle, takl, triangl)

  // Other benchmarks
  private val primtest = loadBenchmark("primtest", "varia")
  private val collatz = loadBenchmark("collatz", "varia")
  private val gcipd = loadBenchmark("gcipd", "varia")
  private val rsa = loadBenchmark("rsa", "varia")
  private val nqueens = loadBenchmark("nqueens", "varia")
  private val scalaAMBenchmarks = List(primtest, collatz, gcipd, rsa, nqueens)

  private val allBenchmarks = gabrielBenchmarks ++ scalaAMBenchmarks

  /* MACHINES */

  private val lattice = typeLattice
  private val context = ZeroCFA

  val noGC = new MachineConfiguration(lattice, context) with DefaultAAM
  val tracingGC = new MachineConfiguration(lattice, context) with TracingGC
  val tracingGCAlt = new MachineConfiguration(lattice, context) with TracingGCAlt
  val refWithoutCD = new MachineConfiguration(lattice, context) with RefCountingVanilla
  val refWithKontCD = new MachineConfiguration(lattice, context) with RefCountingKont
  val refWithCD = new MachineConfiguration(lattice, context) with RefCounting

  val allMachines = List(noGC, tracingGC, tracingGCAlt, refWithoutCD, refWithKontCD, refWithCD)

  /* MAIN ENTRY POINT */

  def main(args: Array[String]): Unit = {
    val timestamp = System.currentTimeMillis()
    val results = run(allBenchmarks, allMachines)
    exportCSV(results, filename = s"results-$timestamp")
  }
}