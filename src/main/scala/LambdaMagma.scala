package LambdaMagma

case class Var[A](index: A):
  override def toString: String = s"$index"

case class Lambda[A](param: Var[A], body: BinTree[Term[A]]):
  override def toString: String = s"λ$param.$body"

type Term[A] = Either[Var[A], Lambda[A]]

object Term:
  import BinTree._
  
  // Smart constructors for named expressions (used only in parser)
  def v(name: String): BinTree[Term[String]] = 
    Leaf(Left(Var(name)))
    
  def l(paramName: String)(body: BinTree[Term[String]]): BinTree[Term[String]] = 
    Leaf(Right(Lambda(Var(paramName), body)))
  
  extension [A](fun: BinTree[Term[A]]) 
    def $(arg: BinTree[Term[A]]): BinTree[Term[A]] = Branch(fun, arg)
  
  // Convert named expression to De Bruijn indices
  def toDeBruijn(tree: BinTree[Term[String]], env: List[String] = List.empty, freeVars: Set[String] = Set.empty): BinTree[Term[Int]] =
    given Magma[BinTree[Term[Int]]] = BinTree.binTreeMagma
    
    BinTree.fold(tree)({
      case Left(Var(name)) => 
        val index = env.indexOf(name)
        if index == -1 then
          // Free variable - assign index based on sorted free variables
          val sortedFreeVars = freeVars.toList.sorted
          val freeIndex = sortedFreeVars.indexOf(name) + env.length
          Leaf(Left(Var(freeIndex)))
        else
          Leaf(Left(Var(index)))
      case Right(Lambda(Var(paramName), body)) => 
        Leaf(Right(Lambda(Var(0), toDeBruijn(body, paramName :: env, freeVars))))
    })

  // Free variable computation for De Bruijn terms
  def freeVars(tree: BinTree[Term[Int]], depth: Int = 0): Set[Int] =
    given Magma[Set[Int]] with
      def op(x: Set[Int], y: Set[Int]): Set[Int] = x ++ y
    
    fold(tree)({
      case Left(Var(index)) => 
        if index >= depth then Set(index) else Set.empty
      case Right(Lambda(_, body)) => 
        freeVars(body, depth + 1)
    })
  
  // Single-step beta reduction - leftmost-outermost strategy
  def betaStep(tree: BinTree[Term[Int]]): BinTree[Term[Int]] =
    def findAndReduce(t: BinTree[Term[Int]]): Option[BinTree[Term[Int]]] = t match
      case Branch(Leaf(Right(Lambda(_, body))), arg) => 
        Some(substitute(body, 0, arg))
      case Branch(left, right) =>
        findAndReduce(left).map(Branch(_, right))
          .orElse(findAndReduce(right).map(Branch(left, _)))
      case Leaf(Right(Lambda(param, body))) =>
        findAndReduce(body).map(newBody => Leaf(Right(Lambda(param, newBody))))
      case _ => None

    findAndReduce(tree).getOrElse(tree)

  // Full beta reduction - reduces to normal form
  @annotation.tailrec
  def betaReduce(tree: BinTree[Term[Int]]): BinTree[Term[Int]] =
    val next = betaStep(tree)
    if next == tree then tree
    else betaReduce(next)

  // Helper function for De Bruijn index shifting
  private def shift(term: BinTree[Term[Int]], cutoff: Int, amount: Int): BinTree[Term[Int]] =
    given Magma[BinTree[Term[Int]]] = BinTree.binTreeMagma
    
    fold(term)({
      case Left(Var(i)) if i >= cutoff => 
        Leaf(Left(Var(i + amount)))
      case Right(Lambda(param, body)) =>
        Leaf(Right(Lambda(param, shift(body, cutoff + 1, amount))))
      case other => 
        Leaf(other)
    })

  // De Bruijn substitution
  def substitute(
    tree: BinTree[Term[Int]],
    index: Int,
    replacement: BinTree[Term[Int]]
  ): BinTree[Term[Int]] =
    given Magma[BinTree[Term[Int]]] = BinTree.binTreeMagma
    
    def go(term: BinTree[Term[Int]], depth: Int): BinTree[Term[Int]] =
      fold(term)({
        case Left(Var(i)) =>
          if i == index + depth then
            shift(replacement, 0, depth)
          else if i > index + depth then
            Leaf(Left(Var(i - 1)))
          else
            Leaf(Left(Var(i)))
        case Right(Lambda(param, body)) =>
          Leaf(Right(Lambda(param, go(body, depth + 1))))
        case other => 
          Leaf(other)
      })
    
    go(tree, 0)

  // Eta reduction for De Bruijn terms
  def eta(tree: BinTree[Term[Int]]): BinTree[Term[Int]] =
    transform(tree)({
      case Leaf(Right(Lambda(_, Branch(f, Leaf(Left(Var(0))))))) 
           if !freeVars(f).contains(0) =>
        // η-reduction: λx.(f x) → f (when x is not free in f)
        Some(shift(f, 0, -1))
      case _ => None
    })
