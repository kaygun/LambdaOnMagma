package LambdaMagma

import scala.collection.mutable
import scala.io.StdIn.readLine
import scala.io.Source
import scala.util.{Try, Success, Failure}
import java.io.{File, PrintWriter, FileNotFoundException}
import Tree._
import Term._
import LambdaParser._

object LambdaREPL extends App:
  private val environment: mutable.Map[String, Tree[Term[String]]] = mutable.Map.empty

  // Pretty printing for both String and Int indexed terms
  private def pretty(tree: Tree[Term[String]]): String = tree match
    case Tree.Leaf(Var(name)) => name  // Remove Left() pattern
    case Tree.Leaf(Lambda(Var(param), body)) => s"λ$param.${pretty(body)}"  // Remove Right() pattern
    case Tree.Branch(left, right) => s"(${pretty(left)} ${pretty(right)})"

  // Resolve variables and collect free vars in one pass
  private def resolve(expr: Tree[Term[String]]): (Tree[Term[String]], Set[String]) =
    import Tree.*
    given Magma[Tree[Term[String]]] = Tree.treeMagma
    given Magma[(Tree[Term[String]], Set[String])] with
      def op(x: (Tree[Term[String]], Set[String]), y: (Tree[Term[String]], Set[String])): (Tree[Term[String]], Set[String]) = 
        (Tree.treeMagma.op(x._1, y._1), x._2 ++ y._2)
    
    def resolveHelper(tree: Tree[Term[String]], bound: Set[String]): (Tree[Term[String]], Set[String]) =
      fold(tree)({
        case Var(name) =>
          if bound.contains(name) then (Leaf(Var(name)), Set.empty)
          else environment.get(name) match
            case Some(definition) => resolveHelper(definition, bound)
            case None => (Leaf(Var(name)), Set(name))
        case Lambda(Var(param), body) =>
          val (resolvedBody, freeVars) = resolveHelper(body, bound + param)
          (Leaf(Lambda(Var(param), resolvedBody)), freeVars)
      })
    
    resolveHelper(expr, Set.empty)

  // Convert from De Bruijn back to named form
  private def fromDeBruijn(tree: Tree[Term[Int]], freeVars: List[String]): Tree[Term[String]] =
    import Tree.*
    given Magma[Tree[Term[String]]] = Tree.treeMagma
    
    def go(t: Tree[Term[Int]], depth: Int): Tree[Term[String]] =
      fold(t)({
        case Var(index) =>  // Remove Left() pattern
          val name = if index < depth then s"x${depth - 1 - index}"
                    else freeVars.lift(index - depth).getOrElse(s"free${index - depth}")
          Leaf(Var(name))  // Remove Left() wrapper
        case Lambda(_, body) =>  // Remove Right() pattern
          Leaf(Lambda(Var(s"x$depth"), go(body, depth + 1)))  // Remove Right() wrapper
      })
    
    go(tree, 0)



  // Step-by-step trace
  private def trace(exprStr: String): Unit =
    LambdaParser.parse(exprStr) match
      case Right(expr) =>
        val (resolved, freeVars) = resolve(expr)
        val freeVarList = freeVars.toList.sorted
        var current = Term.toDeBruijn(resolved, List.empty, freeVars)
        var stepCount = 0
        
        println(s"[$stepCount]: ${pretty(resolved)}")
        
        while stepCount < 400 do
          val next = Term.betaStep(current)
          stepCount += 1
          if next == current then
            return
          else
            current = next
            println(s"[$stepCount]: ${pretty(fromDeBruijn(current, freeVarList))}")
        
        println(s"${pretty(fromDeBruijn(Term.betaReduce(current), freeVarList))}")
      case Left(err) => println(err)

  // File operations with error handling
  private def handleHelp(): Unit =
    println("""Commands:
      |  let <n> = <expr>     - Define a variable
      |  :env                 - Show environment
      |  :clear               - Clear environment
      |  :save <file>         - Save environment to file
      |  :load <file>         - Load environment from file
      |  :step <expr>         - Show single step reduction
      |  :trace <expr>        - Show step-by-step evaluation
      |  :eta <expr>          - Apply eta reduction
      |  :help, :h            - Show this help
      |  :quit, :q            - Exit REPL
      |  <expr>               - Evaluate expression""".stripMargin)

  private def handleEnv(): Unit =
    if environment.isEmpty then println("Empty environment")
    else environment.toSeq.sortBy((kv: (String, Tree[Term[String]])) => kv._1).foreach((k, v) => println(s"$k = ${pretty(v)}"))

  private def handleClear(): Unit =
    environment.clear()
    println("Environment cleared")

  private def handleStep(exprStr: String): Unit =
    LambdaParser.parse(exprStr) match
      case Right(expr) =>
        val (resolved, freeVars) = resolve(expr)
        val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
        val stepped = Term.betaStep(deBruijn)
        
        if stepped == deBruijn then println(s"${pretty(resolved)} (already in normal form)")
        else println(s"${pretty(resolved)} → ${pretty(fromDeBruijn(stepped, freeVars.toList.sorted))}")
      case Left(err) => println(err)

  private def handleEta(exprStr: String): Unit =
    LambdaParser.parse(exprStr) match
      case Right(expr) =>
        val (resolved, freeVars) = resolve(expr)
        val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
        val etaReduced = Term.eta(deBruijn)
        val result = fromDeBruijn(etaReduced, freeVars.toList.sorted)
        println(s"η-reduction: ${pretty(resolved)} → ${pretty(result)}")
      case Left(err) => println(err)

  private def handleLet(name: String, exprStr: String): Unit =
    if name.nonEmpty && exprStr.nonEmpty then
      LambdaParser.parse(exprStr) match
        case Right(expr) =>
          environment(name) = expr
          println(s"$name = ${pretty(expr)}")
        case Left(err) => println(err)
    else println("Usage: let <n> = <expr>")

  private def handleAlphaEq(line: String): Unit =
    line.split("==", 2) match
      case Array(expr1Str, expr2Str) =>
        (LambdaParser.parse(expr1Str.trim), LambdaParser.parse(expr2Str.trim)) match
          case (Right(expr1), Right(expr2)) =>
            val (resolved1, freeVars1) = resolve(expr1)
            val (resolved2, freeVars2) = resolve(expr2)
            val allFreeVars = freeVars1 ++ freeVars2
            
            val db1 = Term.betaReduce(Term.toDeBruijn(resolved1, List.empty, allFreeVars))
            val db2 = Term.betaReduce(Term.toDeBruijn(resolved2, List.empty, allFreeVars))
            
            println(s"${pretty(resolved1)} == ${pretty(resolved2)}")
            println(db1 == db2)
              
          case (Left(err1), _) => println(s"Parse error in first expression: $err1")
          case (_, Left(err2)) => println(s"Parse error in second expression: $err2")
      case _ => println("Usage: <expr1> == <expr2>")

  private def handleEval(line: String): Unit =
    LambdaParser.parse(line) match
      case Right(expr) =>
        val (resolved, freeVars) = resolve(expr)
        val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
        val result = Term.betaReduce(deBruijn)
        println(pretty(fromDeBruijn(result, freeVars.toList.sorted)))
      case Left(err) => println(err)
  private def saveEnv(filename: String): Unit =
    Try {
      val out = new PrintWriter(File(filename))
      try environment.foreach { case (k, v) => out.println(s"let $k = ${pretty(v)}") }
      finally out.close()
    } match
      case Success(_) => println(s"Environment save successful: $filename")
      case Failure(e) => println(s"Error during save: ${e.getMessage}")

  private def loadEnv(filename: String): Unit =
    Try {
      for line <- Source.fromFile(filename).getLines do
        if line.trim.startsWith("let ") then
          line.trim.drop(4).split("=", 2).map(_.trim) match
            case Array(name, exprStr) if name.nonEmpty && exprStr.nonEmpty =>
              LambdaParser.parse(exprStr).toOption.foreach(expr => environment(name) = expr)
            case _ => println(s"Invalid line: $line")
    } match
      case Success(_) => println(s"Environment load successful: $filename")
      case Failure(e) => println(s"Error during load: ${e.getMessage}")

  // Main command processor
  private def processCommand(input: String): Boolean = input.trim match
    case ":q" | ":quit" => 
      println("Goodbye!")
      false
      
    case ":help" | ":h" => handleHelp(); true
    case ":env" => handleEnv(); true
    case ":clear" => handleClear(); true
    
    case line if line.startsWith(":step ") =>
      handleStep(line.stripPrefix(":step ").trim); true
    case line if line.startsWith(":trace ") => 
      trace(line.stripPrefix(":trace ").trim); true
    case line if line.startsWith(":save ") => 
      saveEnv(line.stripPrefix(":save ").trim); true
    case line if line.startsWith(":load ") => 
      loadEnv(line.stripPrefix(":load ").trim); true
    case line if line.startsWith(":eta ") =>
      handleEta(line.stripPrefix(":eta ").trim); true
      
    case line if line.startsWith("let ") =>
      line.drop(4).split("=", 2).map(_.trim) match
        case Array(name, exprStr) => handleLet(name, exprStr)
        case _ => println("Usage: let <n> = <expr>")
      true
      
    case line if line.contains("==") => handleAlphaEq(line); true
    case line if line.nonEmpty => handleEval(line); true
    case _ => true

  // Main REPL loop
  println("Lambda Calculus REPL")
  println("Type :help for commands, :q to quit")

  Iterator.continually(readLine("λ> "))
    .takeWhile(_ != null)
    .map(processCommand)
    .takeWhile(identity)
    .foreach(_ => ())
