ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / scalaVersion := "3.7.1"

lazy val root = (project in file("."))
  .settings(
    name := "lambda-magma",
    
    libraryDependencies ++= Seq(
      // ScalaTest for unit testing
      "org.scalatest" %% "scalatest" % "3.2.17" % Test,
      
      // ScalaCheck for property-based testing
      "org.scalatestplus" %% "scalacheck-1-17" % "3.2.17.0" % Test,
      
      // Parser combinators
      "org.scala-lang.modules" %% "scala-parser-combinators" % "2.3.0"
    ),
    
    // Test configuration
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
    Test / parallelExecution := false,
    
    // Compiler options
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature", 
      "-unchecked",
    ),
    
    // Main class for running the REPL
    Compile / mainClass := Some("LambdaMagma.launch")
  )
