package LambdaMagma

import scala.collection.mutable
import scala.io.StdIn.readLine
import scala.io.Source
import scala.util.{Try, Success, Failure}
import java.io.{File, PrintWriter, FileNotFoundException}
import BinTree._
import Term._
import LambdaParser._

object LambdaREPL extends App:
  private val environment: mutable.Map[String, BinTree[Term[String]]] = mutable.Map.empty
  private var normalizeResults: Boolean = true

  // Pretty printing for both String and Int indexed terms
  private def pretty(tree: BinTree[Term[String]]): String = tree match
    case BinTree.Leaf(Left(Var(name))) => name
    case BinTree.Leaf(Right(Lambda(Var(param), body))) => s"λ$param.${pretty(body)}"
    case BinTree.Branch(left, right) => s"(${pretty(left)} ${pretty(right)})"

  private def prettyDB(tree: BinTree[Term[Int]]): String = tree match
    case BinTree.Leaf(Left(Var(index))) => index.toString
    case BinTree.Leaf(Right(Lambda(_, body))) => s"λ.${prettyDB(body)}"
    case BinTree.Branch(left, right) => s"(${prettyDB(left)} ${prettyDB(right)})"

  // Resolve variables and collect free vars in one pass
  private def resolveAndGetFreeVars(expr: BinTree[Term[String]]): (BinTree[Term[String]], Set[String]) =
    import BinTree.*
    given Magma[BinTree[Term[String]]] = BinTree.binTreeMagma
    given Magma[(BinTree[Term[String]], Set[String])] with
      def op(x: (BinTree[Term[String]], Set[String]), y: (BinTree[Term[String]], Set[String])): (BinTree[Term[String]], Set[String]) = 
        (BinTree.binTreeMagma.op(x._1, y._1), x._2 ++ y._2)
    
    def go(tree: BinTree[Term[String]], bound: Set[String]): (BinTree[Term[String]], Set[String]) =
      fold(tree)({
        case Left(Var(name)) => 
          if bound.contains(name) then (Leaf(Left(Var(name))), Set.empty)
          else environment.get(name) match
            case Some(definition) => go(definition, bound)
            case None => (Leaf(Left(Var(name))), Set(name))
        case Right(Lambda(Var(param), body)) => 
          val (resolvedBody, freeVars) = go(body, bound + param)
          (Leaf(Right(Lambda(Var(param), resolvedBody))), freeVars)
      })
    
    go(expr, Set.empty)

  // Convert from De Bruijn back to named form
  private def fromDeBruijn(tree: BinTree[Term[Int]], freeVars: List[String]): BinTree[Term[String]] =
    import BinTree.*
    given Magma[BinTree[Term[String]]] = BinTree.binTreeMagma
    
    def go(t: BinTree[Term[Int]], depth: Int): BinTree[Term[String]] =
      fold(t)({
        case Left(Var(index)) =>
          val name = if index < depth then s"x${depth - 1 - index}"
                    else freeVars.lift(index - depth).getOrElse(s"free${index - depth}")
          Leaf(Left(Var(name)))
        case Right(Lambda(_, body)) =>
          Leaf(Right(Lambda(Var(s"x$depth"), go(body, depth + 1))))
      })
    
    go(tree, 0)



  // Step-by-step trace
  private def trace(exprStr: String): Unit =
    LambdaParser.parse(exprStr) match
      case Right(expr) =>
        val (resolved, freeVars) = resolveAndGetFreeVars(expr)
        val freeVarList = freeVars.toList.sorted
        var current = Term.toDeBruijn(resolved, List.empty, freeVars)
        var stepCount = 0
        
        println(s"[$stepCount]: ${pretty(resolved)}")
        
        while stepCount < 400 do
          val next = Term.betaStep(current)
          stepCount += 1
          if next == current then
            if normalizeResults then
              val normalized = Term.betaReduce(current)
              if normalized != current then
                println(s"[$stepCount]: ${pretty(fromDeBruijn(normalized, freeVarList))}")
            else
              println("(no more single steps available)")
            return
          else
            current = next
            println(s"[$stepCount]: ${pretty(fromDeBruijn(current, freeVarList))}")
        
        println(s"Stopped after 400 steps")
        if normalizeResults then
          println(s"Final: ${pretty(fromDeBruijn(Term.betaReduce(current), freeVarList))}")
      case Left(err) => println(err)

  // Alpha equivalence check
  private def alphaEq(line: String): Unit =
    line.split("==", 2) match
      case Array(expr1Str, expr2Str) =>
        (LambdaParser.parse(expr1Str.trim), LambdaParser.parse(expr2Str.trim)) match
          case (Right(expr1), Right(expr2)) =>
            val (resolved1, freeVars1) = resolveAndGetFreeVars(expr1)
            val (resolved2, freeVars2) = resolveAndGetFreeVars(expr2)
            val allFreeVars = freeVars1 ++ freeVars2
            
            val db1 = Term.betaReduce(Term.toDeBruijn(resolved1, List.empty, allFreeVars))
            val db2 = Term.betaReduce(Term.toDeBruijn(resolved2, List.empty, allFreeVars))
            
            println(s"${pretty(resolved1)} == ${pretty(resolved2)}")
            println(db1 == db2)
              
          case (Left(err1), _) => println(s"Parse error in first expression: $err1")
          case (_, Left(err2)) => println(s"Parse error in second expression: $err2")
      case _ => println("Usage: <expr1> == <expr2>")

  // File operations with error handling
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
      
    case ":help" | ":h" => 
      println("""Commands:
        |  let <n> = <expr>     - Define a variable
        |  :env                 - Show environment
        |  :clear               - Clear environment
        |  :save <file>         - Save environment to file
        |  :load <file>         - Load environment from file
        |  :normalize on|off    - Toggle normalization (default: on)
        |  :step <expr>         - Show single step reduction
        |  :trace <expr>        - Show step-by-step evaluation
        |  :eta <expr>          - Apply eta reduction
        |  :db <expr>           - Show De Bruijn representation
        |  :help, :h            - Show this help
        |  :quit, :q            - Exit REPL
        |  <expr>               - Evaluate expression""".stripMargin)
      true
      
    case ":env" => 
      if environment.isEmpty then println("Empty environment")
      else environment.toSeq.sortBy(_._1).foreach((k, v) => println(s"$k = ${pretty(v)}"))
      true
      
    case ":clear" => 
      environment.clear()
      println("Environment cleared")
      true
    
    case line if line.startsWith(":normalize ") =>
      line.stripPrefix(":normalize ").trim.toLowerCase match
        case "on" | "true" => 
          normalizeResults = true
          println("Normalization enabled - expressions will be fully reduced")
        case "off" | "false" => 
          normalizeResults = false
          println("Normalization disabled - expressions will use single-step evaluation only")
        case _ => println("Usage: :normalize on|off")
      true
      
    case line if line.startsWith(":step ") =>
      val exprStr = line.stripPrefix(":step ").trim
      LambdaParser.parse(exprStr) match
        case Right(expr) =>
          val (resolved, freeVars) = resolveAndGetFreeVars(expr)
          val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
          val stepped = Term.betaStep(deBruijn)
          
          if stepped == deBruijn then println(s"${pretty(resolved)} (already in normal form)")
          else println(s"${pretty(resolved)} → ${pretty(fromDeBruijn(stepped, freeVars.toList.sorted))}")
        case Left(err) => println(err)
      true
    case line if line.startsWith(":trace ") => trace(line.stripPrefix(":trace ").trim); true
    case line if line.startsWith(":save ") => saveEnv(line.stripPrefix(":save ").trim); true
    case line if line.startsWith(":load ") => loadEnv(line.stripPrefix(":load ").trim); true
    case line if line.contains("==") => alphaEq(line); true

    case line if line.startsWith(":eta ") =>
      val exprStr = line.stripPrefix(":eta ").trim
      LambdaParser.parse(exprStr) match
        case Right(expr) =>
          val (resolved, freeVars) = resolveAndGetFreeVars(expr)
          val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
          val etaReduced = Term.eta(deBruijn)
          val result = fromDeBruijn(etaReduced, freeVars.toList.sorted)
          println(s"η-reduction: ${pretty(resolved)} → ${pretty(result)}")
        case Left(err) => println(err)
      true

    case line if line.startsWith(":db ") =>
      val exprStr = line.stripPrefix(":db ").trim
      LambdaParser.parse(exprStr) match
        case Right(expr) =>
          val (resolved, freeVars) = resolveAndGetFreeVars(expr)
          val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
          println(s"Named: ${pretty(resolved)}")
          println(s"De Bruijn: ${prettyDB(deBruijn)}")
          println(s"Free vars: ${freeVars.toList.sorted.mkString(", ")}")
        case Left(err) => println(err)
      true
      
    case line if line.startsWith("let ") =>
      line.drop(4).split("=", 2).map(_.trim) match
        case Array(name, exprStr) if name.nonEmpty && exprStr.nonEmpty =>
          LambdaParser.parse(exprStr) match
            case Right(expr) =>
              environment(name) = expr
              println(s"$name = ${pretty(expr)}")
            case Left(err) => println(err)
        case _ => println("Usage: let <n> = <expr>")
      true
      
    case line if line.nonEmpty => 
      LambdaParser.parse(line) match
        case Right(expr) =>
          val (resolved, freeVars) = resolveAndGetFreeVars(expr)
          val deBruijn = Term.toDeBruijn(resolved, List.empty, freeVars)
          val result = if normalizeResults then Term.betaReduce(deBruijn) else Term.betaStep(deBruijn)
          println(pretty(fromDeBruijn(result, freeVars.toList.sorted)))
        case Left(err) => println(err)
      true
    case _ => true

  // Main REPL loop
  println("Lambda Calculus REPL")
  println("Type :help for commands, :q to quit")
  println(s"Normalization: ${if normalizeResults then "enabled" else "disabled"}")

  Iterator.continually(readLine("λ> "))
    .takeWhile(_ != null)
    .map(processCommand)
    .takeWhile(identity)
    .foreach(_ => ())
