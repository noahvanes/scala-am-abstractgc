object Util {
  import scala.io.StdIn

  implicit class MapStrict[A,B](m: Map[A,B]) {
    def filterKeysStrict(keys: Set[A]): Map[A,B] =
      keys.foldLeft(Map[A,B]())((acc,key) => m.get(key) match {
        case Some(vlu) => acc + (key -> vlu)
        case None => acc
      })
  }

  def fileContent(file: String): Option[String] = {
    val f = scala.io.Source.fromFile(file)
    val content = f.getLines.mkString("\n")
    f.close()
    Option(content)
  }

  def withFileWriter(path: String)(body: java.io.Writer => Unit): Unit = {
    val f = new java.io.File(path)
    val bw = new java.io.BufferedWriter(new java.io.FileWriter(f))
    body(bw)
    bw.close()
  }

  def withStringWriter(body: java.io.Writer => Unit): String = {
    val w = new java.io.StringWriter()
    body(w)
    w.toString()
  }


  object Done extends Exception
  /** Either run cb on the content of the given file, or run a REPL, each line being sent to cb */
  def replOrFile[A](file: Option[String], cb: String => A): Unit = {
    lazy val reader = new jline.console.ConsoleReader()
    @scala.annotation.tailrec
    def loop(): Unit = Option(reader.readLine(">>> ")) match {
      case Some(program) if program.length == 0 =>
        loop()
      case Some(program) =>
        cb(program)
        loop()
      case None => ()
    }
    file match {
      case Some(file) =>
        runOnFile[A](file, cb)
        ()
      case None => loop()
    }
  }
  def runOnFile[A](file: String, cb: String => A): A = {
    fileContent(file) match {
        case Some(program) =>
          cb(program)
        case None => throw new RuntimeException(s"Input file doesn't exists ($file)")
      }
  }

  /* From http://stackoverflow.com/questions/7539831/scala-draw-table-to-console */
  object Tabulator {
    def format(table: Seq[Seq[Any]]): String = table match {
      case Seq() => ""
      case _ =>
        val sizes = for (row <- table) yield (for (cell <- row) yield Option(cell) match {
          case Some(content) => content.toString.length
          case None => 0
        })
        val colSizes = for (col <- sizes.transpose) yield col.max
        val rows = for (row <- table) yield formatRow(row, colSizes)
        formatRows(rowSeparator(colSizes), rows)
    }

    def formatRows(rowSeparator: String, rows: Seq[String]): String = (
      rowSeparator ::
        rows.head ::
        rowSeparator ::
        rows.tail.toList :::
        rowSeparator ::
        List()).mkString("\n")

    def formatRow(row: Seq[Any], colSizes: Seq[Int]): String = {
      val cells = (for ((item, size) <- row.zip(colSizes)) yield if (size == 0) "" else ("%" + size + "s").format(item))
      cells.mkString("|", "|", "|")
    }

    def rowSeparator(colSizes: Seq[Int]): String = colSizes map { "-" * _ } mkString("+", "+", "+")
  }
}

import scala.concurrent.duration.Duration
class Timeout(startingTime: Long, timeout: Option[Long]) {
  def reached: Boolean = timeout.map(System.nanoTime - startingTime > _).getOrElse(false)
  def time: Double = (System.nanoTime - startingTime) / Math.pow(10, 9)
}
object Timeout {
  def start(timeout: Option[Long]): Timeout = new Timeout(System.nanoTime, timeout)
  def start(timeout: Duration): Timeout = new Timeout(System.nanoTime, if (timeout.isFinite) { Some(timeout.toNanos) } else None)
  def none: Timeout = new Timeout(System.nanoTime, None)
}
