scalaVersion := (if (sys.props("java.specification.version") == "1.8") "2.12.3" else "2.11.11")
scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

logLevel := Level.Error 

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"
libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.0.6"
libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.15"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.0"
libraryDependencies += "com.typesafe.akka" %% "akka-actor" % (if (sys.props("java.specification.version") == "1.8") "2.5.4" else "2.3.16")
libraryDependencies += "jline" % "jline" % "2.14.5"
libraryDependencies += "org.json4s" %% "json4s-native" % "3.5.3"
libraryDependencies += "org.json4s" %% "json4s-jackson" % "3.5.3"

libraryDependencies += "au.com.bytecode" % "opencsv" % "2.4"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.3" % "test"
libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.13.5" % "test"

maxErrors := 5
mainClass in (Compile, run) := Some("Main")

addCompilerPlugin("org.psywerx.hairyfotr" %% "linter" % "0.1.17")
scalacOptions += "-P:linter:disable:UnusedParameter"

cancelable in Global := true
