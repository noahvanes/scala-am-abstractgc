object Main {
  def fileContent(path: String): String = {
    val f = scala.io.Source.fromFile(path)
    val content = f.getLines.mkString("\n")
    f.close()
    println(content)
    content
  }

  def main(args: Array[String]) {
    if (args.length != 1) {
      println("Scheme file expected as argument")
    } else {
      /* val exp = SExpParser.parse(fileContent(args(0)))
      println(exp)
      println(Scheme.compile(exp))
      println(Scheme.rename(Scheme.compile(exp)))
      println(ANF.compile(Scheme.rename(Scheme.compile(exp)))) */
      println(AAM.eval(ANF.compile(Scheme.rename(Scheme.compile(SExpParser.parse("(letrec ((x 1)) x)"))))))
    }
  }
}
