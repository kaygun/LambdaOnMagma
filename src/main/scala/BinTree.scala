package LambdaMagma

trait Magma[A]:
  def op(x: A, y: A): A
  extension (x: A) def $ (y: A): A = op(x, y)

enum BinTree[A]:
  case Leaf(value: A)
  case Branch(left: BinTree[A], right: BinTree[A])

object BinTree:
  import scala.Predef.identity

  given binTreeMagma[A]: Magma[BinTree[A]] with
    def op(x: BinTree[A], y: BinTree[A]): BinTree[A] = Branch(x, y)
  
  def leaf[A](value: A): BinTree[A] = Leaf(value)

  // A context-sensitive catamorphism over BinTree[A].
  // Threads an environment of type C downwards using succ.
  // If C = Unit (the default), `succ` defaults to identity.
  def readerCat[A, B, C](
    tree: BinTree[A],
    context: C,
    succ: C => C = identity,
    leafFn: A => B
  )(using monoid: Magma[B]): B =
    val context1 = succ(context)
    tree match
      case Leaf(v) => leafFn(v)
      case Branch(l,r) => 
        val l1 = readerCat(l, context1, succ, leafFn)
        val r1 = readerCat(r, context1, succ, leafFn)
        monoid.op(l1,r1)

  def map[A, B](tree: BinTree[A])(f: A => B): BinTree[B] =
    given Magma[BinTree[B]] = binTreeMagma
    readerCat(tree, (), identity, (a:A) => Leaf(f(a)))

  def fold[A, B](tree: BinTree[A])(f: A => B)(using monoid: Magma[B]): B =
    readerCat(tree, (), identity, f)

  def transform[A, C](
    tree: BinTree[A],
    context: C,
    succ: C => C,
    rule: (BinTree[A], C) => Option[BinTree[A]]
  ): BinTree[A] =
    given Magma[BinTree[A]] = binTreeMagma

    readerCat(tree, context, succ, (a: A) => Leaf(a)) match
      case result =>
        rule(result, context).getOrElse(result)

  def transform[A](tree: BinTree[A])(rule: BinTree[A] => Option[BinTree[A]]): BinTree[A] =
    transform(tree, (), _ => (), (t, _) => rule(t))
