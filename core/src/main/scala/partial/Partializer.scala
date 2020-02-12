package stainlessfit
package core
package partial

import trees._

object Partializer {
  val InitialFuel = 6

  private[this] var nextId_ : Int = 1000 // FIXME: Take this as an input
  def freshId(name: String): Identifier = {
    val thisId = nextId_
    nextId_ += 1
    Identifier(thisId, name)
  }
  def freshBoundId(): Identifier = freshId("bound")

  // type Type =
  //   NatType | BoolType | UnitType | SumType | PiType | SigmaType | IntersectionType |
  //   RefinementType | RecType | PolyForallType | BottomType | TopType

  // // A tree describing a computation-value
  // trait CVTree {
  //   type Self
  //   def flatMap(f: Tree => Self): Self
  // }

  // implicit class TreeHelpers(val tree: Tree) {
  //   def toPartial: PartialTree = PartialTree(tree)
  // }

  // // Partial computation values
  // case class PartialTree(tree: Tree) {
  //   type Self = PartialTree
  //   def flatMap(f: Tree => Self): Self = {

  //   }
  // }


  def NatMatch(scrut: Tree)(zero: Tree)(succ: Identifier => Tree): Tree = {
    val id = freshId("n")
    Match(scrut, zero, Bind(id, succ(id)))
  }

  def termWithBound(t: Tree): Tree = Lambda(Some(NatType), Bind(freshBoundId(), t))

  // `Partial T    := Nat -> PartialRes T`
  // `PartialRes T := PDiverged | PComputed T`
  def Partial(tpe: Tree): Tree = PiType(NatType, Bind(freshBoundId(), PartialRes(tpe)))
  def PartialRes(tpe: Tree): Tree = SumType(UnitType, tpe)
  def PDiverged: Tree = termWithBound(LeftTree(UnitLiteral))
  def PComputed(t: Tree): Tree = termWithBound(RightTree(t))
  def PMatch(scrut: Tree)(div: Tree)(comp: Identifier => Tree): Tree = {
    val id = freshId("v")
    EitherMatch(scrut, Bind(freshId("_"), div), Bind(id, comp(id)))
  }

  def bindPartial(t: Tree, boundId: Identifier)(f: Identifier => Tree): Tree =
    PMatch(App(t, Var(boundId)))(PDiverged)(f)

  // The actual partialization on programs

  def apply(t: Tree): Tree = {
    def apply0(t: Tree, boundId: Identifier): Tree = {
      // In a context `C` with depth bound `b: Nat \in C`
      t match {
        case Var(id) =>
          // [ x ]  :=  { x }
          PComputed(t)

        case App(t1, t2) =>
          // [ (t1 t2) ]  :=
          //   { f a | f <- [ t1 b' ], a <- [ t2 b' ], b = S(b') }
          NatMatch(Var(boundId))(PDiverged) { boundIdDec =>
            bindPartial(apply0(t1, boundId), boundIdDec) { f =>
              bindPartial(apply0(t2, boundId), boundIdDec) { a =>
                App(Var(f), Var(a))
              }
            }
          }

        case Lambda(tp, bind) =>
          // [ \x:T. t ]  :=  { \f:Nat. \x:T. [ t ] }
          PComputed(Lambda(tp.map(apply0(_, boundId)), apply0(bind, boundId)))

        case Bind(id, t) =>
          Bind(id, apply0(t, boundId))

        case UnitLiteral => PComputed(t)
        case NatLiteral(_) => PComputed(t)
        case BooleanLiteral(_) => PComputed(t)

        // TODO: Adapt the remaining cases

        // case IfThenElse(cond, t1, t2) =>
        //   IfThenElse(apply0(cond, boundId), apply0(t1, boundId), apply0(t2, boundId))
        // case Pair(t1, t2) => Pair(apply0(t1, boundId), apply0(t2, boundId))
        // case First(t) => First(apply0(t, boundId))
        // case Second(t) => Second(apply0(t, boundId))
        // case LeftTree(t) => LeftTree(apply0(t, boundId))
        // case RightTree(t) => RightTree(apply0(t, boundId))
        // case Because(t1, t2) => Because(apply0(t1, boundId), apply0(t2, boundId))
        // case ErasableLambda(tp, bind) => ErasableLambda(apply0(tp, boundId), apply0(bind, boundId))
        // case Fix(None, bind) => Fix(None, apply0(bind, boundId))
        // case Fix(Some(tp), bind) => Fix(Some(apply0(tp, boundId)), apply0(bind, boundId))
        // case LetIn(None, v1, bind) => LetIn(None, apply0(v1, boundId), apply0(bind, boundId))
        // case LetIn(Some(tp), v1, bind) => LetIn(Some(apply0(tp, boundId)), apply0(v1, boundId), apply0(bind, boundId))
        // // case MacroTypeDecl(tpe, bind) => MacroTypeDecl(apply0(tpe, boundId), apply0(bind, boundId))
        // // case MacroTypeInst(v1, args) =>
        // //   MacroTypeInst(
        // //     apply0(v1, boundId),
        // //     args.map(a => (a._1, apply0(a._2, boundId)))
        // //   )
        // case Match(t, t0, bind) => Match(apply0(t, boundId), apply0(t0, boundId), apply0(bind, boundId))
        // case EitherMatch(t, bind1, bind2) => EitherMatch(apply0(t, boundId), apply0(bind1, boundId), apply0(bind2, boundId))
        // case Primitive(op, args) => Primitive(op, args.map(apply0(_, boundId)))
        // case Inst(t1, t2) => Inst(apply0(t1, boundId), apply0(t2, boundId))
        // case Fold(tp, t) => Fold(apply0(tp, boundId), apply0(t, boundId))
        // case Unfold(t, bind) => Unfold(apply0(t, boundId), apply0(bind, boundId))
        // case UnfoldPositive(t, bind) => UnfoldPositive(apply0(t, boundId), apply0(bind, boundId))
        // case Abs(bind) => Abs(apply0(bind, boundId))
        // case TypeApp(abs, t) => TypeApp(apply0(abs, boundId), apply0(t, boundId))
        // case Error(_, _) => t

        case NatType => t
        case BoolType => t
        case UnitType => t
        case SumType(t1, t2) =>
          SumType(apply0(t1, boundId), apply0(t2, boundId))
        case PiType(t1, Bind(id, t2)) =>
          val t2_ = Partial(apply0(t2, boundId))
          PiType(apply0(t1, boundId), Bind(id, t2_))
        // case SigmaType(t1, bind) => SigmaType(apply0(t1, boundId), apply0(bind, boundId))
        // case IntersectionType(t1, bind) => IntersectionType(apply0(t1, boundId), apply0(bind, boundId))
        // case RefinementType(t1, bind) => RefinementType(apply0(t1, boundId), apply0(bind, boundId))
        // case RecType(n, bind) => RecType(apply0(n, boundId), apply0(bind, boundId))
        // case PolyForallType(bind) => PolyForallType(apply0(bind, boundId))

        case BottomType => BottomType
        case TopType => TopType

        case _ => throw new java.lang.Exception(s"Partializer is not implemented on $t (${t.getClass}).")
      }
    }

    val boundId0 = freshBoundId()
    val body0 = apply0(t, boundId0)
    App(Lambda(Some(NatType), Bind(boundId0, body0)), NatLiteral(InitialFuel))
  }

  // prop("typechecks when translated to Partial") {
  //   val program: Tree = ??? // some program
  //   val programP = translatePartial(program)
  //   typechecks(programP)
  // }
}
