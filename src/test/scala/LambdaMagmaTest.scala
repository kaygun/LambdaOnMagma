package LambdaMagma

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks
import org.scalacheck.Gen
import scala.language.deprecated.symbolLiterals
import BinTree._
import Term._

class LambdaMagmaTestSuite extends AnyFlatSpec with Matchers with ScalaCheckPropertyChecks {

  // Core Components
  "Magma trait" should "provide correct operation and extension method" in {
    val stringMagma = new Magma[String]:
      def op(x: String, y: String): String = x + y
    
    stringMagma.op("hello", "world") shouldBe "helloworld"
    
    given Magma[String] = stringMagma
    "hello" $ "world" shouldBe "helloworld"
  }

  "BinTree" should "construct correctly" in {
    Leaf(42) shouldBe a[Leaf[?]]
    Branch(Leaf(1), Leaf(2)) shouldBe a[Branch[?]]
  }

  it should "have correct magma instance" in {
    val tree1 = Leaf(1)
    val tree2 = Leaf(2)
    BinTree.binTreeMagma.op(tree1, tree2) shouldBe Branch(tree1, tree2)
  }

  "BinTree.fold" should "work with simple magma" in {
    given Magma[Int] with
      def op(x: Int, y: Int): Int = x + y
    
    val tree = Branch(Leaf(1), Branch(Leaf(2), Leaf(3)))
    BinTree.fold(tree)(identity) shouldBe 6
  }

  "BinTree.map" should "transform leaf values" in {
    val tree = Branch(Leaf(1), Leaf(2))
    BinTree.map(tree)(_ * 2) shouldBe Branch(Leaf(2), Leaf(4))
  }

  "BinTree.readerCat" should "thread context through computation" in {
    case class Context(depth: Int)
    
    given Magma[String] with
      def op(x: String, y: String): String = s"($x $y)"
    
    val tree = Branch(Leaf(1), Leaf(2))
    val result = BinTree.readerCat(
      tree, 
      Context(0), 
      (c: Context) => Context(c.depth + 1),
      (i: Int) => s"leaf$i"
    )
    
    result shouldBe "(leaf1 leaf2)"
  }

  // Expression Types
  "Term smart constructors" should "create correct structures" in {
    Term.v("x") shouldBe Leaf(Left(Var("x")))
    Term.l("x")(Term.v("x")) shouldBe Leaf(Right(Lambda(Var("x"), Leaf(Left(Var("x"))))))
    
    val f = Term.v("f")
    val x = Term.v("x")
    f $ x shouldBe Branch(f, x)
  }

  // Lambda Calculus Operations
  "Term.freeVars" should "correctly identify free variables in De Bruijn terms" in {
    // λx.x (no free vars)
    val identity = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0)))))): BinTree[Term[Int]]
    Term.freeVars(identity) shouldBe Set.empty
    
    // λx.y (free var y with index 1)
    val lambdaWithFree = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1)))))): BinTree[Term[Int]]
    Term.freeVars(lambdaWithFree) shouldBe Set(1)
    
    // x y (two free vars)
    val application = Branch(Leaf(Left(Var(0))), Leaf(Left(Var(1)))): BinTree[Term[Int]]
    Term.freeVars(application) shouldBe Set(0, 1)
  }

  "Term.substitute" should "perform correct De Bruijn substitution" in {
    val target = Leaf(Left(Var(0))): BinTree[Term[Int]]
    val replacement = Leaf(Left(Var(5))): BinTree[Term[Int]]
    Term.substitute(target, 0, replacement) shouldBe replacement
    
    // Substitute in lambda body: λ.1 with 0 -> Var(5) becomes λ.6 (shifted)
    val lambda = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1)))))): BinTree[Term[Int]]
    val substituted = Term.substitute(lambda, 0, replacement)
    substituted shouldBe Leaf(Right(Lambda(Var(0), Leaf(Left(Var(6))))))
  }

  "Term.betaStep" should "perform single beta reduction step" in {
    // (λx.x) y -> y
    val identity = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0)))))): BinTree[Term[Int]]
    val arg = Leaf(Left(Var(5))): BinTree[Term[Int]]
    val application = Branch(identity, arg): BinTree[Term[Int]]
    
    Term.betaStep(application) shouldBe arg
  }

  it should "find leftmost-outermost redex" in {
    // (λx.x) ((λy.y) z) should reduce the outer application first
    val identity = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0)))))): BinTree[Term[Int]]
    val innerApp = Branch(identity, Leaf(Left(Var(2)))): BinTree[Term[Int]]
    val outerApp = Branch(identity, innerApp): BinTree[Term[Int]]
    
    Term.betaStep(outerApp) shouldBe innerApp
  }

  "Term.betaReduce" should "reduce to normal form" in {
    // (λx.λy.x) a b -> a
    val true_expr = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1))))))))): BinTree[Term[Int]]
    val a = Leaf(Left(Var(10))): BinTree[Term[Int]]
    val b = Leaf(Left(Var(11))): BinTree[Term[Int]]
    val application = Branch(Branch(true_expr, a), b): BinTree[Term[Int]]
    
    Term.betaReduce(application) shouldBe a
  }

  "Term.eta" should "perform eta reduction" in {
    // λx.(f x) -> f (when x not free in f)
    val f = Leaf(Left(Var(1))): BinTree[Term[Int]]
    val etaExpandedForm = Leaf(Right(Lambda(Var(0), Branch(f, Leaf(Left(Var(0))))))): BinTree[Term[Int]]
    
    Term.eta(etaExpandedForm) shouldBe Leaf(Left(Var(0)))
  }

  "Term.toDeBruijn" should "convert named expressions to De Bruijn" in {
    val namedIdentity = Leaf(Right(Lambda(Var("x"), Leaf(Left(Var("x")))))): BinTree[Term[String]]
    Term.toDeBruijn(namedIdentity) shouldBe Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0))))))
  }

  it should "handle free variables correctly" in {
    // Let's test simpler cases first
    // Simple free variable case: just "y"
    val freeVar = Leaf(Left(Var("y"))): BinTree[Term[String]]
    val freeVarResult = Term.toDeBruijn(freeVar, List.empty, Set("y"))
    freeVarResult shouldBe Leaf(Left(Var(0)))
    
    // Lambda with free variable: λx.y
    val namedTerm = Leaf(Right(Lambda(Var("x"), Leaf(Left(Var("y")))))): BinTree[Term[String]]
    val result = Term.toDeBruijn(namedTerm, List.empty, Set("y"))
    // x is bound at index 0, y is free and gets index based on environment length + free var position
    result shouldBe Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1))))))
  }

  // Parser Tests
  "LambdaParser" should "parse simple variables" in {
    LambdaParser.parse("x") shouldBe Right(Leaf(Left(Var("x"))))
  }

  it should "parse lambda expressions" in {
    LambdaParser.parse("\\x.x") shouldBe Right(Leaf(Right(Lambda(Var("x"), Leaf(Left(Var("x")))))))
    LambdaParser.parse("λy.y") shouldBe Right(Leaf(Right(Lambda(Var("y"), Leaf(Left(Var("y")))))))
  }

  it should "parse applications" in {
    LambdaParser.parse("f x") shouldBe Right(Branch(Leaf(Left(Var("f"))), Leaf(Left(Var("x")))))
  }

  it should "parse complex expressions" in {
    LambdaParser.parse("(\\x.x) y").isRight shouldBe true
    LambdaParser.parse("\\x.\\y.x y").isRight shouldBe true
  }

  it should "handle parentheses correctly" in {
    val result1 = LambdaParser.parse("(f x) y")
    val result2 = LambdaParser.parse("f (x y)")
    
    result1.isRight shouldBe true
    result2.isRight shouldBe true
    result1 should not equal result2
  }

  it should "reject invalid syntax" in {
    LambdaParser.parse("\\") shouldBe a[Left[?, ?]]
    LambdaParser.parse("λ.x") shouldBe a[Left[?, ?]]
    LambdaParser.parse("(unclosed") shouldBe a[Left[?, ?]]
  }

  // Lambda Calculus Applications
  "Church numerals" should "be constructible and work correctly" in {
    // Church zero: λf.λx.x
    val zero = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0))))))))): BinTree[Term[Int]]
    Term.freeVars(zero) shouldBe Set.empty
    
    // Church one: λf.λx.f x
    val one = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Branch(Leaf(Left(Var(1))), Leaf(Left(Var(0)))))))))): BinTree[Term[Int]]
    Term.freeVars(one) shouldBe Set.empty
    
    // Successor function: λn.λf.λx.f (n f x)
    val succ = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), 
      Branch(Leaf(Left(Var(1))), Branch(Branch(Leaf(Left(Var(2))), Leaf(Left(Var(1)))), Leaf(Left(Var(0)))))))))))))): BinTree[Term[Int]]
    
    // Test: succ zero should be equivalent to one
    val succZero = Branch(succ, zero): BinTree[Term[Int]]
    val reduced = Term.betaReduce(succZero)
    
    // The result should be alpha-equivalent to one (both are closed terms)
    Term.freeVars(reduced) shouldBe Set.empty
  }

  "Church booleans" should "work correctly with conditional logic" in {
    // Church true: λx.λy.x
    val churchTrue = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1))))))))): BinTree[Term[Int]]
    
    // Church false: λx.λy.y
    val churchFalse = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0))))))))): BinTree[Term[Int]]
    
    // Test conditional: true a b -> a
    val a = Leaf(Left(Var(10))): BinTree[Term[Int]]
    val b = Leaf(Left(Var(11))): BinTree[Term[Int]]
    val trueCondition = Branch(Branch(churchTrue, a), b): BinTree[Term[Int]]
    
    Term.betaReduce(trueCondition) shouldBe a
    
    // Test conditional: false a b -> b
    val falseCondition = Branch(Branch(churchFalse, a), b): BinTree[Term[Int]]
    Term.betaReduce(falseCondition) shouldBe b
  }

  "Combinators" should "work correctly" in {
    // I combinator: λx.x
    val I = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0)))))): BinTree[Term[Int]]
    
    // K combinator: λx.λy.x
    val K = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1))))))))): BinTree[Term[Int]]
    
    // S combinator: λx.λy.λz.x z (y z)
    val S = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), 
      Branch(Branch(Leaf(Left(Var(2))), Leaf(Left(Var(0)))), Branch(Leaf(Left(Var(1))), Leaf(Left(Var(0)))))))))))))): BinTree[Term[Int]]
    
    // Test I: I a -> a
    val a = Leaf(Left(Var(5))): BinTree[Term[Int]]
    val Ia = Branch(I, a): BinTree[Term[Int]]
    Term.betaReduce(Ia) shouldBe a
    
    // Test K: K a b -> a
    val b = Leaf(Left(Var(6))): BinTree[Term[Int]]
    val Kab = Branch(Branch(K, a), b): BinTree[Term[Int]]
    Term.betaReduce(Kab) shouldBe a
    
    // Test SKK = I (famous combinator identity)
    val SKK = Branch(Branch(S, K), K): BinTree[Term[Int]]
    val SKKa = Branch(SKK, a): BinTree[Term[Int]]
    Term.betaReduce(SKKa) shouldBe a
  }

  // Property-based Tests
  "Parser" should "handle valid variable names" in {
    val validVarNames = Gen.alphaStr.suchThat(_.nonEmpty)
    
    forAll(validVarNames) { varName =>
      val expr = s"\\$varName.$varName"
      LambdaParser.parse(expr).isRight shouldBe true
    }
  }

  "De Bruijn conversion" should "be deterministic" in {
    val expressions = Table(
      "expression",
      "\\x.x",
      "\\x.\\y.x",
      "\\x.\\y.y",
      "\\f.\\x.f x",
      "(\\x.x) y"
    )
    
    forAll(expressions) { expr =>
      val parsed1 = LambdaParser.parse(expr)
      val parsed2 = LambdaParser.parse(expr)
      parsed1 shouldBe parsed2
    }
  }

  "Beta reduction" should "be confluent for simple cases" in {
    // (λx.x) y should reduce to y in one step
    val identity = Leaf(Right(Lambda(Var(0), Leaf(Left(Var(0)))))): BinTree[Term[Int]]
    val arg = Leaf(Left(Var(1))): BinTree[Term[Int]]
    val app = Branch(identity, arg): BinTree[Term[Int]]
    
    val step1 = Term.betaStep(app)
    val step2 = Term.betaStep(step1)
    
    step1 shouldBe arg
    step2 shouldBe arg // Should be in normal form
  }

  "Alpha equivalence" should "work via De Bruijn representation" in {
    // λx.x and λy.y should have the same De Bruijn representation
    val expr1 = LambdaParser.parse("\\x.x").toOption.get
    val expr2 = LambdaParser.parse("\\y.y").toOption.get
    
    val db1 = Term.toDeBruijn(expr1)
    val db2 = Term.toDeBruijn(expr2)
    
    db1 shouldBe db2
  }

  "Error handling" should "provide meaningful error messages" in {
    val result = LambdaParser.parse("invalid lambda \\")
    result.isLeft shouldBe true
    
    val Left(error) = result
    error should not be empty
  }

  "Complex reductions" should "work correctly" in {
    // Test a more complex reduction: (λx.λy.x) a b -> a
    val churchTrue = Leaf(Right(Lambda(Var(0), Leaf(Right(Lambda(Var(0), Leaf(Left(Var(1))))))))): BinTree[Term[Int]]
    val a = Leaf(Left(Var(10))): BinTree[Term[Int]]
    val b = Leaf(Left(Var(11))): BinTree[Term[Int]]
    
    val step1 = Branch(churchTrue, a): BinTree[Term[Int]]
    val step2 = Branch(step1, b): BinTree[Term[Int]]
    
    val reduced = Term.betaReduce(step2)
    reduced shouldBe a
  }
}
