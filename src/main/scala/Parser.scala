package LambdaMagma

import scala.util.parsing.combinator.JavaTokenParsers

object LambdaParser extends JavaTokenParsers:
  override val whiteSpace = """(\s|//.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r
  
  // Parse to named expressions
  def lambda: Parser[BinTree[Expr[String]]] = 
    (("\\" | "λ") ~> ident <~ ".") ~ expression ^^ {
      case param ~ body => Expr.l(param)(body)
    }
  
  def variable: Parser[BinTree[Expr[String]]] = 
    ident ^^ Expr.v
  
  def parenthesized: Parser[BinTree[Expr[String]]] = 
    "(" ~> expression <~ ")"
  
  def atom: Parser[BinTree[Expr[String]]] = 
    parenthesized | variable
  
  def application: Parser[BinTree[Expr[String]]] = 
    rep1(lambda | atom) ^^ { atoms =>
      atoms.tail.foldLeft(atoms.head)(BinTree.binTreeMagma.op)
    }
  
  def expression: Parser[BinTree[Expr[String]]] = 
    lambda | application
  
  def parse(input: String): Either[String, BinTree[Expr[String]]] =
    parseAll(expression, input) match
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(msg)
