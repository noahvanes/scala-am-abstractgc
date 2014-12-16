scalaVersion := "2.11.4"
scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "com.assembla.scala-incubator" %% "graph-core" % "1.9.1"
libraryDependencies += "com.assembla.scala-incubator" %% "graph-dot" % "1.9.0"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.2"