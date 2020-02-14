package stainlessfit
package core
package partial

import trees._

object Partializer {
  val InitialFuel = 6 // FIXME: ...

  private[this] var nextId_ : Int = 1000 // FIXME: Take this as an input
  def freshId(name: String): Identifier = {
    val thisId = nextId_
    nextId_ += 1
    Identifier(thisId, name)
  }
  def freshBoundId(): Identifier = freshId("bound")

  def NatMatch(scrut: Tree)(zero: Tree)(succ: Identifier => Tree): Tree = {
    val id = freshId("n")
    Match(scrut, zero, Bind(id, succ(id)))
  }

  def termWithBound(t: Identifier => Tree): Tree = {
    val id = freshBoundId()
    Lambda(Some(NatType), Bind(id, t(id)))
  }

  // `Partial T    := Nat -> PartialRes T`
  // `PartialRes T := PDiverged | PComputed T`
  def Partial(tpe: Tree): Tree = PiType(NatType, Bind(freshBoundId(), PartialRes(tpe)))
  def PartialRes(tpe: Tree): Tree = SumType(UnitType, tpe)
  def PDiverged: Tree = termWithBound(_ => LeftTree(UnitLiteral))
  def PComputed(t: Tree): Tree = termWithBound(_ => RightTree(t))
  def PComputed(t: Identifier => Tree): Tree = termWithBound(id => RightTree(t(id)))
  def PMatch(scrut: Tree)(div: Tree)(comp: Identifier => Tree): Tree = {
    val id = freshId("v")
    EitherMatch(scrut, Bind(freshId("_"), div), Bind(id, comp(id)))
  }

  def bindPartial(t: Tree, boundId: Identifier)(f: Identifier => Tree): Tree =
    PMatch(App(t, Var(boundId)))(PDiverged)(f)

  // The actual partialization on programs

  def apply(t: Tree): Tree = {
    def apply0(t: Tree, boundId: Identifier)(implicit recIds: List[Identifier]): Tree = {
      // In a context `C` with depth bound `b: Nat \in C`
      t match {
        case Var(id) if id.name.head.isUpper =>
          // Don't rewrite type variables
          t

        case Var(id) if recIds.contains(id) =>
          Inst(t, Var(boundId))

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
          PComputed { newBound =>
            Lambda(tp.map(apply0(_, newBound)), apply0(bind, newBound))
          }

        case Bind(id, t) =>
          Bind(id, apply0(t, boundId))

        case UnitLiteral => PComputed(t)
        case NatLiteral(_) => PComputed(t)
        case BooleanLiteral(_) => PComputed(t)

        case LetIn(optTpe, v1, bind) =>
          // [ let x = v; t ]  :=  { let x = v'; [ t ] | v' <- v }
          // NOTE: Should we decrement the bound here?
          bindPartial(apply0(v1, boundId), boundId) { v1 =>
            LetIn(optTpe.map(apply0(_, boundId)), Var(v1), apply0(bind, boundId))
          }

        case Fix(Some(Bind(ignoredTpeBound, tpe)), Bind(ignoredBodyBound, Bind(f, body))) =>
          val newBody     = apply0(body, boundId)(f :: recIds)
          val newTpeBound = freshBoundId()
          val newTpe = Partial(apply0(tpe, newTpeBound))
          val newFix = Fix(
            Some(Bind(ignoredTpeBound, newTpe)),
            Bind(ignoredBodyBound, Bind(f, newBody)))
          Inst(newFix, NatLiteral(99999)) // dummy value

        case Primitive(op, arg1 :: Nil) =>
          bindPartial(apply0(arg1, boundId), boundId) { arg1 =>
            PComputed(Primitive(op, List(Var(arg1))))
          }

        case Primitive(op, arg1 :: arg2 :: Nil) =>
          bindPartial(apply0(arg1, boundId), boundId) { arg1 =>
            bindPartial(apply0(arg2, boundId), boundId) { arg2 =>
              PComputed(Primitive(op, List(Var(arg1), Var(arg2))))
            }
          }

        case IfThenElse(cond, t1, t2) =>
          bindPartial(apply0(cond, boundId), boundId) { cond =>
            IfThenElse(Var(cond), apply0(t1, boundId), apply0(t2, boundId))
          }

        // NOTE: Not in surface syntax at the moment
        // case Match(t, t0, bind) =>
        //   bindPartial(apply0(t, boundId), boundId) { t =>
        //     Match(Var(t), apply0(t0, boundId), apply0(bind, boundId))
        //   }

        case EitherMatch(t, bind1, bind2) =>
          bindPartial(apply0(t, boundId), boundId) { t =>
            EitherMatch(Var(t), apply0(bind1, boundId), apply0(bind2, boundId))
          }

        case LeftTree(t) =>
          bindPartial(apply0(t, boundId), boundId) { t =>
            PComputed(LeftTree(Var(t)))
          }
        case RightTree(t) =>
          bindPartial(apply0(t, boundId), boundId) { t =>
            PComputed(RightTree(Var(t)))
          }

        case Pair(t1, t2) =>
          bindPartial(apply0(t1, boundId), boundId) { t1 =>
            bindPartial(apply0(t2, boundId), boundId) { t2 =>
              PComputed(Pair(Var(t1), Var(t2)))
            }
          }

        case First(t) =>
          bindPartial(apply0(t, boundId), boundId) { t =>
            PComputed(First(Var(t)))
          }
        case Second(t) =>
          bindPartial(apply0(t, boundId), boundId) { t =>
            PComputed(Second(Var(t)))
          }

        case MacroTypeDecl(tpe, bind) =>
          MacroTypeDecl(tpe, apply0(bind, boundId))
        case MacroTypeInst(v1 @ Var(_), args) =>
          MacroTypeInst(
            v1,
            args.map(a => (a._1, apply0(a._2, boundId)))
          )

        // FIXME: This is funky. Disallow erased abstraction in partial mode?
        case Inst(t1, t2) => apply0(t1, boundId)

        // TODO: Adapt the remaining cases

        // case Because(t1, t2) => Because(apply0(t1, boundId), apply0(t2, boundId))
        // case ErasableLambda(tp, bind) => ErasableLambda(apply0(tp, boundId), apply0(bind, boundId))

        // NOTE: This presumes that only "library" code carefully uses fold/unfold
        case _: Fold => PComputed(t)
        case Unfold(t, bind) => Unfold(t, apply0(bind, boundId))

        // case Fold(tp, t) => Fold(apply0(tp, boundId), apply0(t, boundId))
        // case Unfold(t, bind) => Unfold(apply0(t, boundId), apply0(bind, boundId))
        // case UnfoldPositive(t, bind) => UnfoldPositive(apply0(t, boundId), apply0(bind, boundId))

        case Abs(bind) => Abs(apply0(bind, boundId))
        case TypeApp(abs, t) => TypeApp(apply0(abs, boundId), apply0(t, boundId))
        // case Error(_, _) => t

        case NatType => t
        case BoolType => t
        case UnitType => t
        case SumType(t1, t2) =>
          SumType(apply0(t1, boundId), apply0(t2, boundId))
        case PiType(t1, Bind(id, t2)) =>
          val t2_ = Partial(apply0(t2, boundId))
          PiType(apply0(t1, boundId), Bind(id, t2_))
        case SigmaType(t1, bind) =>
          SigmaType(apply0(t1, boundId), apply0(bind, boundId))
        // case IntersectionType(t1, bind) => IntersectionType(apply0(t1, boundId), apply0(bind, boundId))
        // case RefinementType(t1, bind) => RefinementType(apply0(t1, boundId), apply0(bind, boundId))
        // case RecType(n, bind) => RecType(apply0(n, boundId), apply0(bind, boundId))
        case PolyForallType(bind) => PolyForallType(apply0(bind, boundId))

        case BottomType => BottomType
        case TopType => TopType

        case _ => throw new java.lang.Exception(s"Partializer is not implemented on $t (${t.getClass}).")
      }
    }

    val boundId0 = freshBoundId()
    val body0 = apply0(t, boundId0)(Nil)
    App(Lambda(Some(NatType), Bind(boundId0, body0)), NatLiteral(InitialFuel))
  }
}
