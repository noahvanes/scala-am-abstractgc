object Main {

  import Util._
  import scala.io.Source
  import scala.concurrent.duration.Duration
  import scala.language.existentials
  import java.io.{BufferedWriter, FileWriter}
  import scala.collection.JavaConversions._
  import au.com.bytecode.opencsv.CSVWriter

  /* GLOBAL CONFIGURATION */

  val BENCHMARK_DIR = "/Users/nvanes/Desktop/benchmarks/"
  val OUTPUT_DIR = "/Users/nvanes/Desktop/outputs/"

  val DEFAULT_RUNS = 100    // used for JIT warmup runs and better (lower) variance
  val DEFAULT_TIMEOUT = 10  // timeout expressed in minutes

  /* MACHINE CONFIGURATIONS */

  abstract case class MachineConfiguration(lattice: SchemeLattice, timestamp: TimestampWrapper) {

    val machine: AbstractMachine[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]

    type Output = machine.Output
    implicit val isSchemeLattice: IsSchemeLattice[lattice.L] = lattice.isSchemeLattice
    implicit val isTimeStamp: Timestamp[timestamp.T] = timestamp.isTimestamp
    val primitives = new SchemePrimitives[ClassicalAddress.A, lattice.L]
    val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, timestamp.T](primitives)

    def run(program: SchemeExp, timeout: Int): Output = machine.eval(program,sem,false,Timeout.start(Duration(timeout,"minutes")))
  }

  trait DefaultAAM extends MachineConfiguration {
    val machine = new AAM[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait TracingGC extends MachineConfiguration {
    val machine = new AAMGC[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }
  trait RefCounting extends MachineConfiguration {
    val machine = new AAMRefCounting[SchemeExp,lattice.L,ClassicalAddress.A,timestamp.T]
  }

  // some lattices
  val typeLattice = new MakeSchemeLattice[Type.S, Concrete.B, Type.I, Type.F, Type.C, Type.Sym](false)
  val constantPropLattice = new MakeSchemeLattice[ConstantPropagation.S, Concrete.B, ConstantPropagation.I, ConstantPropagation.F, ConstantPropagation.C, ConstantPropagation.Sym](false)
  def boundedIntLattice(bound: Int) = {
    val bounded = new BoundedInteger(bound)
    new MakeSchemeLattice[Type.S, Concrete.B, bounded.I, Type.F, Type.C, Type.Sym](false)
  }
  def kPointsToLattice(k: Int) = {
    val kpts = new KPointsTo(k)
    new MakeSchemeLattice[kpts.S, Concrete.B, kpts.I, kpts.F, kpts.C, kpts.S](false)
  }

  // some timestamps
  val zeroCFA: TimestampWrapper = ZeroCFA
  val sCFA: TimestampWrapper = SCFA

  // some machine configurations
  val typeAnalysisClassical = new MachineConfiguration(typeLattice, zeroCFA) with DefaultAAM
  val typeAnalysisTracingGC = new MachineConfiguration(typeLattice, zeroCFA) with TracingGC
  val typeAnalysisRefCounting = new MachineConfiguration(typeLattice, zeroCFA) with RefCounting

  /* BENCHMARKING */

  case class BenchmarkResult(name: String, machine: MachineConfiguration, result: MachineConfiguration#Output, timings: Iterable[Long])

  case class Benchmark(name: String, location: String) {

    override def toString = s"BENCMARK-$name"

    def loadSource(): String = {
      val data = Source.fromFile(location)
      try data.mkString finally data.close()
    }

    def run(machine: MachineConfiguration, runs: Int, timeout: Int): BenchmarkResult = {
      val source = loadSource()
      val program = SchemeUtils.computeFreeVar(SchemeUtils.inline(machine.sem.parse(source), machine.sem.initialEnv.toMap))
      print(s">> RUNNING BENCHMARK $name [${machine.machine.name}]")
      var result: machine.Output = null
      val timings = (1 to runs) map { i =>
        print(".")
        val t0 = System.nanoTime()
        result = machine.run(program, timeout)
        val t1 = System.nanoTime()
        (t1 - t0) / 1000000
      }
      println()
      println(s"(results: ${result.finalValues})")
      BenchmarkResult(name, machine, result, timings)
    }
  }

  def run(benchmarks: List[Benchmark], machines: List[MachineConfiguration], runs: Int = DEFAULT_RUNS, timeout: Int = DEFAULT_TIMEOUT): List[BenchmarkResult]
    = benchmarks.flatMap(benchmark => machines.map(machine => benchmark.run(machine, runs, timeout)))

  def compareOn(benchmarks: List[Benchmark], lattice: SchemeLattice, context: TimestampWrapper, runs: Int = DEFAULT_RUNS, timeout: Int = DEFAULT_TIMEOUT, excludeOriginal: Boolean = true): List[BenchmarkResult] = {
    val machineWithoutGC = new MachineConfiguration(lattice, context) with DefaultAAM
    val machineWithTracingGC = new MachineConfiguration(lattice, context) with TracingGC
    val machineWithRefCounts = new MachineConfiguration(lattice, context) with RefCounting
    val machines = if (excludeOriginal) {
      List(machineWithTracingGC,machineWithRefCounts)
    } else {
      List(machineWithoutGC,machineWithTracingGC,machineWithRefCounts)
    }
    run(benchmarks,machines,runs,timeout)
  }

  def exportCSV(results: List[BenchmarkResult], filename: String): Unit = {
    val outputPath = s"$OUTPUT_DIR/$filename.csv"
    val outputFile = new BufferedWriter(new FileWriter(outputPath))
    val csvWriter = new CSVWriter(outputFile)
    var csvContents = List(Array("name", "timeout", "numberOfStates", "timeElapsed"))
    results foreach { case b =>
      val machine = s"${b.name}-${b.machine.machine.name}"
      val timeout = if (b.result.timedOut) { "1" } else { "0" }
      val count = b.result.numberOfStates.toString
      val time = b.timings.min.toString
      csvContents = Array(machine, timeout, count, time) :: csvContents
    }
    csvWriter.writeAll(csvContents.reverse)
    csvWriter.close()
  }

  /* BENCHMARK SUITES */

  private def loadBenchmark(name: String, subfolder: String) = Benchmark(name, s"$BENCHMARK_DIR/$subfolder/$name.scm")

  private val gabrielBenchmarks = List("cpstak") map { loadBenchmark(_,"gabriel") }
  private val simpleBenchmarks = List("primtest") map { loadBenchmark(_,"simple") }

  /* MAIN ENTRY POINT */

  def main(args: Array[String]): Unit = {
    val results = compareOn(simpleBenchmarks, typeLattice, zeroCFA, runs=100, timeout=1)
    exportCSV(results, filename = "simple-type-0CFA")
  }
}
