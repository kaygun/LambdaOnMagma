package LambdaMagma

// New trait-based Term definition
sealed trait Term[A]

case class Var[A](index: A) extends Term[A]:
  override def toString: String = s"$index"

case class Lambda[A](param: Var[A], body: Tree[Term[A]]) extends Term[A]:
  override def toString: String = s"λ$param.$body"

object Term:
  import Tree._
  extension [A](fun: Tree[Term[A]]) 
    def $(arg: Tree[Term[A]]): Tree[Term[A]] = Branch(fun, arg)
  
  // Convert named expression to De Bruijn indices
  def toDeBruijn(tree: Tree[Term[String]], env: List[String] = List.empty, freeVars: Set[String] = Set.empty): Tree[Term[Int]] =
    given Magma[Tree[Term[Int]]] = Tree.treeMagma
    
    Tree.fold(tree)({
      case Var(name) =>  // Remove Left() pattern
        val index = env.indexOf(name)
        if index == -1 then
          // Free variable - assign index based on sorted free variables
          val sortedFreeVars = freeVars.toList.sorted
          val freeIndex = sortedFreeVars.indexOf(name) + env.length
          Leaf(Var(freeIndex))  // Remove Left() wrapper
        else
          Leaf(Var(index))  // Remove Left() wrapper
      case Lambda(Var(paramName), body) =>  // Remove Right() pattern
        Leaf(Lambda(Var(0), toDeBruijn(body, paramName :: env, freeVars)))  // Remove Right() wrapper
    })

  // Free variable computation for De Bruijn terms
  def freeVars(tree: Tree[Term[Int]], depth: Int = 0): Set[Int] =
    given Magma[Set[Int]] with
      def op(x: Set[Int], y: Set[Int]): Set[Int] = x ++ y
    
    fold(tree)({
      case Var(index) =>  // Remove Left() pattern
        if index >= depth then Set(index) else Set.empty
      case Lambda(_, body) =>  // Remove Right() pattern
        freeVars(body, depth + 1)
    })
  
  // Single-step beta reduction - leftmost-outermost strategy
  def betaStep(tree: Tree[Term[Int]]): Tree[Term[Int]] =
    def findAndReduce(t: Tree[Term[Int]]): Option[Tree[Term[Int]]] = t match
      case Branch(Leaf(Lambda(_, body)), arg) =>  // Remove Right() pattern
        Some(substitute(body, 0, arg))
      case Branch(left, right) =>
        findAndReduce(left).map(Branch(_, right))
          .orElse(findAndReduce(right).map(Branch(left, _)))
      case Leaf(Lambda(param, body)) =>  // Remove Right() pattern
        findAndReduce(body).map(newBody => Leaf(Lambda(param, newBody)))  // Remove Right() wrapper
      case _ => None

    findAndReduce(tree).getOrElse(tree)

  // Full beta reduction - reduces to normal form
  @annotation.tailrec
  def betaReduce(tree: Tree[Term[Int]]): Tree[Term[Int]] =
    val next = betaStep(tree)
    if next == tree then tree
    else betaReduce(next)

  // Helper function for De Bruijn index shifting
  private def shift(term: Tree[Term[Int]], cutoff: Int, amount: Int): Tree[Term[Int]] =
    given Magma[Tree[Term[Int]]] = Tree.treeMagma
    
    fold(term)({
      case Var(i) if i >= cutoff =>  // Remove Left() pattern
        Leaf(Var(i + amount))  // Remove Left() wrapper
      case Lambda(param, body) =>  // Remove Right() pattern
        Leaf(Lambda(param, shift(body, cutoff + 1, amount)))  // Remove Right() wrapper
      case other => 
        Leaf(other)
    })

  // De Bruijn substitution
  def substitute(
    tree: Tree[Term[Int]],
    index: Int,
    replacement: Tree[Term[Int]]
  ): Tree[Term[Int]] =
    given Magma[Tree[Term[Int]]] = Tree.treeMagma
    
    def go(term: Tree[Term[Int]], depth: Int): Tree[Term[Int]] =
      fold(term)({
        case Var(i) =>  // Remove Left() pattern
          if i == index + depth then
            shift(replacement, 0, depth)
          else if i > index + depth then
            Leaf(Var(i - 1))  // Remove Left() wrapper
          else
            Leaf(Var(i))  // Remove Left() wrapper
        case Lambda(param, body) =>  // Remove Right() pattern
          Leaf(Lambda(param, go(body, depth + 1)))  // Remove Right() wrapper
        // case other => Leaf(other)
      })
    
    go(tree, 0)

  // Eta reduction for De Bruijn terms
  def eta(tree: Tree[Term[Int]]): Tree[Term[Int]] =
    transform(tree)({
      case Leaf(Lambda(_, Branch(f, Leaf(Var(0)))))  // Remove Right() and Left() patterns
           if !freeVars(f).contains(0) =>
        // η-reduction: λx.(f x) → f (when x is not free in f)
        Some(shift(f, 0, -1))
      case _ => None
    })
