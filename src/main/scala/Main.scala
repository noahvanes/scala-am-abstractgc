object Main {

  /* -- IMPORTS -- */

  import Util._
  import scala.io.Source
  import scala.concurrent.duration.Duration
  import scala.language.existentials
  import java.io.{BufferedWriter, FileWriter}
  import scala.collection.JavaConversions._
  import au.com.bytecode.opencsv.CSVWriter
  import java.io.File

  /* -- CONFIGURATION -- */

  // configure output options for benchmarks
  private val OUTPUT_FILE   = "overhead-benchmarks"   // the name of the output file (which will be exported in CSV format)
  private val OUTPUT_GRAPH  = None                    // by default, no graph is generated
  // private val OUTPUT_GRAPH  = Some("graph-name")   // uncomment to generate an output graph (automatically exported as a dot-file to output/<graph-name>.dot)
                                                      // (NOTE: to avoid the impact of graph construction on performance, the graph will be generated after the actual benchmark measurements)


  // configure benchmark parameters
  private val MAX_WARMUP_RUNS    = 30     // maximum number of warmup runs per benchmark program
  private val MAX_WARMUP_TIME    = 60     // maximum total time spent on warmup (in seconds) per benchmark program
  private val NUMBER_OF_TRIALS   = 30     // number of trials/measurements per benchmark program
  private val MAX_TIME_PER_TRIAL = 60     // timeout per trial (in seconds)
                                          // NOTE: as memory usage increases throughout a trial, higher values of MAX_TIME_PER_TRIAL might cause out-of-memory exceptions

  // congifure context-sensitivity of the analysis
  private val CONTEXT_SENSITIVITY = zeroCFA       // use a context-insensitive analysis (i.e., 0-CFA) (<- used for the evaluation in the paper)
  //private val CONTEXT_SENSITIVITY = kCFA(1)     // uncomment to switch to a context-sensitive analysis using 1-CFA
  //private val CONTEXT_SENSITIVITY = kCFA(k)     // uncomment to switch to a context-sensitive analysis using k-CFA

  // configure abstract domain of the analysis
  private val ABSTRACT_DOMAIN = typeLattice                     // use a type lattice, which abstracts values using the set of all possible types (<- used for the evaluation in the paper)
  //private val ABSTRACT_DOMAIN = constantPropagationLattice    // uncomment to switch to a constant-propagation lattice, which is similar to a typeLattice but more precisely, in that for constant values it can keep track of the concrete value as well
  //private val ABSTRACT_DOMAIN = kPointsToLattice(k)           // uncomment to switch to a k-points-to lattice, which is a generalization of a constantPropagationLattice, in that it can keep track of up to k concrete values
  //private val ABSTRACT_DOMAIN = concreteLattice               // uncomment to switch to a concrete lattice, which abstracts values using the set of all possible concrete values (may not terminate)
  //private val ABSTRACT_DOMAIN = boundedIntegerLattice(b)      // uncomment to switch to a bounded-integer lattice, which is similar to a concreteLattice but only keeps concrete values for integers between [-b,b] (more likely to terminate)

  // configure which abstract interpreters / machines to compare in the benchmarks
  private val ABSTRACT_MACHINES = List(
  //  machineAAM,                 // uncomment to include an abstract interpreter without abstract GC (i.e., \rightarrow in the paper)
  //  machineAAMGC,               // uncomment to include an abstract interpreter with abstract tracing GC at every step (i.e., \rightarrow_{\Gamma} in the paper)
  //  machineAAMGC_gammaCFA,      // uncomment to include an abstract interpreter which performs abstract tracing GC at every join operation in the store (i.e., \rightarrow_{\GammaCFA} in the paper)
  //  machineAAMARC,              // uncomment to include an abstract interpreter which performs abstract reference counting without cycle detection (i.e., \rightarrow_{arc} in the paper)
  //  machineAAMARCplus,          // uncomment to include an abstract interpreter which performs abstract reference counting with only cycle detection in the kontinuation store (i.e., \rightarrow_{arc+} in the paper)
    machineAAMARCplusplus         // the abstract interpreter which performs abstract reference counting with full cycle detection (i.e., \rightarrow_{arc++} in the paper)
  )

  // configure which benchmarks to run (uncomment to include; using the same names as in the paper)
  private val BENCHMARK_PROGRAMS = List(
    // boyer,
    // browse,
    // cpstak,
    // dderiv,
    // deriv,
    // destruc,
    // diviter,
    // divrec,
    // puzzle,
    // takl,
    // triangl,
    // primtest,
    // collatz,
    // rsa,
    // gcipd,
    nqueens
  )

  /* -- SUPPORTING DEFINITIONS -- */

  // timestamp definitions
  private def zeroCFA = ZeroCFA
  private def kCFA(k: Int) = KCFA(k)

  // lattice definitions
  private def typeLattice: SchemeLattice                  = new MakeSchemeLattice[Type.S, Concrete.B, Type.I, Type.F, Type.C, Type.Sym](false)
  private def constantPropagationLattice: SchemeLattice   = new MakeSchemeLattice[ConstantPropagation.S, Concrete.B, ConstantPropagation.I, ConstantPropagation.F, ConstantPropagation.C, ConstantPropagation.Sym](false)
  private def kPointsToLattice(k: Int): SchemeLattice = {
    val kpts = new KPointsTo(k)
    new MakeSchemeLattice[kpts.S, Concrete.B, kpts.I, kpts.F, kpts.C, kpts.S](false)
  }
  private def concreteLattice: SchemeLattice              = new MakeSchemeLattice[Concrete.S, Concrete.B, Concrete.I, Concrete.F, Concrete.C, Concrete.Sym](false)
  private def boundedIntegerLattice(bound: Int): SchemeLattice = {
    val bounded = new BoundedInteger(bound)
    new MakeSchemeLattice[Type.S, Concrete.B, bounded.I, Type.F, Type.C, Type.Sym](false)
  }

  // machine definitions
  private def machineAAM = new AAMOriginal[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]
  private def machineAAMGC = new AAMGC[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]
  private def machineAAMGC_gammaCFA = new AAMGCAlt[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]
  private def machineAAMARC = new AAMRefCountingVanilla[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]
  private def machineAAMARCplus = new AAMRefCountingKont[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]
  private def machineAAMARCplusplus = new AAMRefCounting[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]

  // benchmark definitions
  private def loadBenchmark(name: String, subfolder: String) = Benchmark(name, s"$BENCHMARK_DIR/$subfolder/$name.scm")
  private def loadGabrielBenchmark(name: String) = loadBenchmark(name,"gabriel")
  private def loadScalaAMBenchmark(name: String) = loadBenchmark(name,"scala-am")
  private def boyer    = loadGabrielBenchmark("boyer")
  private def browse   = loadGabrielBenchmark("browse")
  private def cpstak   = loadGabrielBenchmark("cpstak")
  private def dderiv   = loadGabrielBenchmark("dderiv")
  private def deriv    = loadGabrielBenchmark("deriv")
  private def destruc  = loadGabrielBenchmark("destruc")
  private def diviter  = loadGabrielBenchmark("diviter")
  private def divrec   = loadGabrielBenchmark("divrec")
  private def puzzle   = loadGabrielBenchmark("puzzle")
  private def takl     = loadGabrielBenchmark("takl")
  private def triangl  = loadGabrielBenchmark("triangl")
  private def primtest = loadScalaAMBenchmark("primtest")
  private def collatz  = loadScalaAMBenchmark("collatz")
  private def rsa      = loadScalaAMBenchmark("rsa")
  private def gcipd    = loadScalaAMBenchmark("gcipd")
  private def nqueens  = loadScalaAMBenchmark("nqueens")

  /* -- PRE-CONFIGURED (should probably not be changed) -- */

  private val BENCHMARK_DIR = "benchmarks"            // the root folder where the source code for the benchmarks can be found
  private val OUTPUT_DIR    = "output"                // the root folder where the benchmark results are exported

  /* -- BENCHMARKING -- */

  // used to register time spent on GC
  private var GC_TIME: Long = 0
  def timeGC[A](block: => A): A = {
    val t0 = System.nanoTime()
    val res = block
    val t1 = System.nanoTime()
    Main.GC_TIME = Main.GC_TIME + (t1 - t0)
    res
  }

  // auxiliary definitions
  private type Machine = AbstractMachine[SchemeExp,ABSTRACT_DOMAIN.L,ClassicalAddress.A,CONTEXT_SENSITIVITY.T]
  private implicit def isSchemeLattice: IsSchemeLattice[ABSTRACT_DOMAIN.L] = ABSTRACT_DOMAIN.isSchemeLattice
  private implicit def isTimeStamp: Timestamp[CONTEXT_SENSITIVITY.T] = CONTEXT_SENSITIVITY.isTimestamp
  private def primitives = new SchemePrimitives[ClassicalAddress.A, ABSTRACT_DOMAIN.L]
  private def sem = new SchemeSemantics[ABSTRACT_DOMAIN.L, ClassicalAddress.A, CONTEXT_SENSITIVITY.T](primitives)

  // format for benchmarks
  case class Benchmark(name: String, location: String) {
    assume({ val f = new File(location); f.exists && f.isFile })
    def loadSource(): String = {
      val data = Source.fromFile(location)
      try data.mkString finally data.close()
    }
    def loadSchemeProgram(): SchemeExp = {
      val source = loadSource()
      val parsed = sem.parse(source)
      val optimized = SchemeUtils.inline(parsed,sem.initialEnv.toMap)
      SchemeUtils.computeFreeVar(optimized)
    }
  }

  // format for benchmark results
  case class BenchmarkResult(id: String, mean: Double, stddev: Double)

  // benchmarking function
  private def runBenchmark(benchmark: Benchmark, machine: Machine): BenchmarkResult = {
    val name = s"${benchmark.name}-${machine.name}"
    println(s">> RUNNING BENCHMARK $name")
    val program = benchmark.loadSchemeProgram()
    // warmup runs
    var warmupRun = 0
    val warmupTimeout = Timeout.start(Duration(MAX_WARMUP_TIME,"seconds"))
    while (warmupRun < MAX_WARMUP_RUNS && !warmupTimeout.reached) {
      print(".")
      GC_TIME = 0
      machine.eval(program,sem,false,warmupTimeout)
      warmupRun = warmupRun + 1
    }
    // actual measurements
    var trial = 0
    var overheads = List[Double]()
    while (trial < NUMBER_OF_TRIALS) {
      print("*")
      GC_TIME = 0
      val result = machine.eval(program,sem,false,Timeout.start(Duration(MAX_TIME_PER_TRIAL,"seconds")))
      overheads = (GC_TIME:Double)/(result.numberOfStates:Double) :: overheads
      trial = trial + 1
    }
    // optional: export a state graph
    if (OUTPUT_GRAPH.isDefined) {
      val result = machine.eval(program,sem,true,Timeout.start(Duration(MAX_TIME_PER_TRIAL,"seconds")))
      result.toFile(s"$OUTPUT_DIR/${OUTPUT_GRAPH.get}-$name.dot")(GraphDOTOutput)
    }
    // compute the benchmark result
    val mean = (overheads.sum:Double) / (overheads.size:Double)
    val stddev = Math.sqrt((overheads.map(r=>Math.pow(r-mean,2)).sum:Double)/((overheads.size-1):Double))
    println(s"\n=> MEAN: $mean | STDDEV: $stddev")
    BenchmarkResult(name,mean,stddev)
  }

  private def runBenchmarks(benchmarks: List[Benchmark], machines: List[Machine]): List[BenchmarkResult]
    = benchmarks.flatMap(benchmark => machines.map(machine => runBenchmark(benchmark,machine)))

  private def exportCSV(results: List[BenchmarkResult], filename: String): Unit = {
    val outputPath = s"$OUTPUT_DIR/$filename.csv"
    val outputFile = new BufferedWriter(new FileWriter(outputPath))
    val csvWriter = new CSVWriter(outputFile)
    var csvContents = List(Array("benchmark", "mean", "std"))
    results foreach { result =>
      csvContents = Array(result.id, result.mean.toString, result.stddev.toString) :: csvContents
    }
    csvWriter.writeAll(csvContents.reverse)
    csvWriter.close()
  }

  def main(args: Array[String]): Unit = {
    val results = runBenchmarks(BENCHMARK_PROGRAMS, ABSTRACT_MACHINES)
    exportCSV(results, OUTPUT_FILE)
  }
}
