package LambdaMagma

import scala.util.parsing.combinator.JavaTokenParsers

object LambdaParser extends JavaTokenParsers:
  override val whiteSpace = """(\s|//.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r
  
  // Parse to named expressions
  def lambda: Parser[BinTree[Term[String]]] = 
    (("\\" | "λ") ~> ident <~ ".") ~ expression ^^ {
      case param ~ body => Term.l(param)(body)
    }
  
  def variable: Parser[BinTree[Term[String]]] = 
    ident ^^ Term.v
  
  def parenthesized: Parser[BinTree[Term[String]]] = 
    "(" ~> expression <~ ")"
  
  def atom: Parser[BinTree[Term[String]]] = 
    parenthesized | variable
  
  def application: Parser[BinTree[Term[String]]] = 
    rep1(lambda | atom) ^^ { atoms =>
      atoms.tail.foldLeft(atoms.head)(BinTree.binTreeMagma.op)
    }
  
  def expression: Parser[BinTree[Term[String]]] = 
    lambda | application
  
  def parse(input: String): Either[String, BinTree[Term[String]]] =
    parseAll(expression, input) match
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(msg)
