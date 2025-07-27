package LambdaMagma

import scala.io.StdIn.readLine
import scala.collection.mutable
import scala.util.Try
import java.io.{File, PrintWriter, FileNotFoundException}
import scala.io.Source
import BinTree._
import Expr._
import LambdaParser._

object REPL:
  
  private var env = mutable.Map.empty[String, BinTree[Expr[Int]]]

  def prettyPrint(tree: BinTree[Expr[Int]], names: List[String] = List.empty): String =
    case class Pretty(str: String, isAtomic: Boolean)

    given Magma[Pretty] with
      def op(left: Pretty, right: Pretty): Pretty =
        val leftStr = if left.isAtomic then left.str else s"(${left.str})"
        Pretty(s"$leftStr ${right.str}", isAtomic = false)

    readerCat(tree, names, identity, {
      case Left(Var(index)) =>
        val name = if index < names.length then names(index) else s"x$index"
        Pretty(name, isAtomic = true)
      case Right(Lambda(_, body)) =>
        val paramName = s"x${names.length}"
        val newNames = paramName :: names
        val inner = prettyPrint(body, newNames)
        Pretty(s"λ$paramName.$inner", isAtomic = true)
    }).str

  private def collectFreeVars(tree: BinTree[Expr[String]], env: List[String] = List.empty): Set[String] =
    given Magma[Set[String]] with
      def op(x: Set[String], y: Set[String]): Set[String] = x ++ y
    
    BinTree.fold(tree)({
      case Left(Var(name)) => 
        if env.contains(name) then Set.empty else Set(name)
      case Right(Lambda(Var(paramName), body)) => 
        collectFreeVars(body, paramName :: env)
    })

  private def resolveVariables(expr: BinTree[Expr[String]]): BinTree[Expr[String]] =
    given Magma[BinTree[Expr[String]]] = BinTree.binTreeMagma
    
    BinTree.fold(expr) {
      case Left(Var(name)) =>
        env.get(name) match
          case Some(dbExpr) => fromDeBruijnToNamed(dbExpr)
          case None => Leaf(Left(Var(name)))
      case Right(Lambda(param, body)) =>
        Leaf(Right(Lambda(param, resolveVariables(body))))
    }

  private def fromDeBruijnToNamed(expr: BinTree[Expr[Int]]): BinTree[Expr[String]] =
    given Magma[BinTree[Expr[String]]] = BinTree.binTreeMagma
    
    def convert(tree: BinTree[Expr[Int]], names: List[String] = List.empty): BinTree[Expr[String]] =
      BinTree.fold(tree) {
        case Left(Var(index)) =>
          val name = if index < names.length then names(index) else s"x$index"
          Leaf(Left(Var(name)))
        case Right(Lambda(_, body)) =>
          val paramName = s"x${names.length}"
          Leaf(Right(Lambda(Var(paramName), convert(body, paramName :: names))))
      }
    
    convert(expr)

  private def parseAndResolve(input: String): Either[String, BinTree[Expr[Int]]] =
    LambdaParser.parse(input).map { namedExpr =>
      val resolved = resolveVariables(namedExpr)
      val freeVars = collectFreeVars(resolved)
      Expr.toDeBruijn(resolved, List.empty, freeVars)
    }

  private def evalSteps(expr: BinTree[Expr[Int]]): List[BinTree[Expr[Int]]] =
    val steps = collection.mutable.ListBuffer.empty[BinTree[Expr[Int]]]
    var current = expr
    
    steps += current
    
    var changed = true
    while changed do
      val next = betaStep(current)
      changed = current != next
      if changed then
        current = next
        steps += current
    
    steps.toList

  private def saveEnvironment(filename: String): Unit =
    Try {
      val writer = new PrintWriter(new File(filename))
      try
        for (name, expr) <- env do
          writer.println(s"let $name = ${prettyPrint(expr)}")
        println(s"Environment saved to $filename")
      finally
        writer.close()
    }.recover {
      case e => println(s"Error saving environment: ${e.getMessage}")
    }

  private def loadEnvironment(filename: String): Unit =
    Try {
      val source = Source.fromFile(filename)
      try
        var loaded = 0
        
        for line <- source.getLines() do
          val trimmed = line.trim
          if trimmed.nonEmpty && !trimmed.startsWith("//") && trimmed.startsWith("let ") then
            val parts = trimmed.drop(4).split("=", 2)
            if parts.length == 2 then
              val varName = parts(0).trim
              val exprStr = parts(1).trim
              parseAndResolve(exprStr) match
                case Right(expr) =>
                  env(varName) = expr
                  loaded += 1
                case Left(err) =>
                  println(s"Parse error in line '$trimmed': $err")
            else
              println(s"Invalid line format: $trimmed")
        
        println(s"Loaded $loaded definitions from $filename")
        
      finally
        source.close()
    }.recover {
      case _: FileNotFoundException => println(s"File not found: $filename")
      case e => println(s"Error loading environment: ${e.getMessage}")
    }

  private def deleteVariable(name: String): Unit =
    if env.contains(name) then
      env.remove(name)
      println(s"Deleted variable: $name")
    else
      println(s"Variable not found: $name")

  private def showHelp(): Unit =
    println("Commands:")
    println("  let <name> = <expr>   Define a variable")
    println("  <expr>                Evaluate expression")
    println("  :env                  Show environment")
    println("  :save <filename>      Save environment to file")
    println("  :load <filename>      Load environment from file")
    println("  :delete <name>        Delete variable from environment")
    println("  :q                    Quit")
    println("Examples:")
    println("  let id = \\x.x")
    println("  let true = \\x.\\y.x")
    println("  let false = \\x.\\y.y")
    println("  id true")
    println("  :save stdlib.lc")
    println("  :load stdlib.lc")

  private def showEnvironment(): Unit =
    if env.isEmpty then 
      println("Environment is empty.")
    else
      for (k, v) <- env do 
        println(s"$k = ${prettyPrint(v)}")

  private def handleLetBinding(line: String): Unit =
    val parts = line.drop(4).split("=", 2)
    if parts.length == 2 then
      val varName = parts(0).trim
      val exprStr = parts(1).trim
      parseAndResolve(exprStr) match
        case Right(expr) =>
          env(varName) = expr
          println(s"$varName = ${prettyPrint(expr)}")
        case Left(err) =>
          println(s"Parse error: $err")
    else 
      println("Invalid let binding. Use: let <name> = <expr>")

  private def handleExpression(line: String): Unit =
    parseAndResolve(line) match
      case Left(err) =>
        println(s"Parse error: $err")
      case Right(expr) =>
        val steps = evalSteps(expr)
        if steps.length == 1 then
          println(s"${prettyPrint(steps.head)}")
        else
          steps.zipWithIndex.foreach { (step, i) =>
            println(s"[$i]: ${prettyPrint(step)}")
          }

  private def processCommand(line: String): Boolean = line.trim match
    case null | ":q" => 
      println("Goodbye!")
      false
    case ":help" => 
      showHelp()
      true
    case ":env" => 
      showEnvironment()
      true
    case cmd if cmd.startsWith(":save ") =>
      val filename = cmd.drop(6).trim
      if filename.nonEmpty then saveEnvironment(filename)
      else println("Usage: :save <filename>")
      true
    case cmd if cmd.startsWith(":load ") =>
      val filename = cmd.drop(6).trim
      if filename.nonEmpty then loadEnvironment(filename)
      else println("Usage: :load <filename>")
      true
    case cmd if cmd.startsWith(":delete ") =>
      val varName = cmd.drop(8).trim
      if varName.nonEmpty then deleteVariable(varName)
      else println("Usage: :delete <variable_name>")
      true
    case cmd if cmd.startsWith("let ") =>
      handleLetBinding(cmd)
      true
    case expr =>
      handleExpression(expr)
      true

  def runREPL(): Unit =
    println("Lambda Calculus REPL (Scala 3). Type :q to quit, :help for help.")
    var continue = true
    while continue do
      print("λ> ")
      Console.flush()
      val line = readLine()
      continue = processCommand(line)

@main def launch(): Unit = REPL.runREPL()
