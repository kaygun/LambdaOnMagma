package LambdaMagma

trait Magma[A]:
  def op(x: A, y: A): A
  extension (x: A) def $ (y: A): A = op(x, y)

enum Tree[A]:
  case Leaf(value: A)
  case Branch(left: Tree[A], right: Tree[A])

object Tree:
  import scala.Predef.identity

  given treeMagma[A]: Magma[Tree[A]] with
    def op(x: Tree[A], y: Tree[A]): Tree[A] = Branch(x, y)
  
  def leaf[A](value: A): Tree[A] = Leaf(value)

  // A context-sensitive catamorphism over Tree[A].
  // Threads an environment of type C downwards using succ.
  // If C = Unit (the default), `succ` defaults to identity.
  def readerCat[A, B, C](
    tree: Tree[A],
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

  def map[A, B](tree: Tree[A])(f: A => B): Tree[B] =
    given Magma[Tree[B]] = treeMagma
    readerCat(tree, (), identity, (a:A) => Leaf(f(a)))

  def fold[A, B](tree: Tree[A])(f: A => B)(using monoid: Magma[B]): B =
    readerCat(tree, (), identity, f)

  def transform[A, C](
    tree: Tree[A],
    context: C,
    succ: C => C,
    rule: (Tree[A], C) => Option[Tree[A]]
  ): Tree[A] =
    given Magma[Tree[A]] = treeMagma

    readerCat(tree, context, succ, (a: A) => Leaf(a)) match
      case result =>
        rule(result, context).getOrElse(result)

  def transform[A](tree: Tree[A])(rule: Tree[A] => Option[Tree[A]]): Tree[A] =
    transform(tree, (), _ => (), (t, _) => rule(t))

