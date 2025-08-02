package LambdaMagma
import Tree._

import scala.util.parsing.combinator.JavaTokenParsers

object LambdaParser extends JavaTokenParsers:
  override val whiteSpace = """(\s|//.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r
  
  // Parse to named expressions
  def lambda: Parser[Tree[Term[String]]] = 
    (("\\" | "λ") ~> ident <~ ".") ~ expression ^^ {
      case param ~ body => Leaf(Lambda(Var(param), body))
    }
  
  def variable: Parser[Tree[Term[String]]] = 
    ident ^^ { name => Leaf(Var(name)) }
  
  def parenthesized: Parser[Tree[Term[String]]] = 
    "(" ~> expression <~ ")"
  
  def atom: Parser[Tree[Term[String]]] = 
    parenthesized | variable
  
  def application: Parser[Tree[Term[String]]] = 
    rep1(lambda | atom) ^^ { atoms =>
      atoms.tail.foldLeft(atoms.head)(Tree.treeMagma.op)
    }
  
  def expression: Parser[Tree[Term[String]]] = 
    lambda | application
  
  def parse(input: String): Either[String, Tree[Term[String]]] =
    parseAll(expression, input) match
      case Success(result, _) => Right(result)
      case failure: NoSuccess => Left(failure.msg)
