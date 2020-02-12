package stainlessfit
package core
package typechecker

import Derivation._
import util.RunContext

case class Rule(
  name: String,
  apply: Goal => Option[(
    List[List[Judgment] => Goal],
    List[Judgment] => (Boolean, Judgment))
  ]) {
  def t(implicit rc: RunContext): Tactic[Goal, (Boolean, NodeTree[Judgment])] = Tactic { (g, subgoalSolver) =>
    rc.bench.time("Rule " + name)
    { apply(g) }.flatMap {
      case (sgs, merge) =>
        val subTrees =
          sgs.foldLeft[Option[(Boolean, List[NodeTree[Judgment]])]](Some(true, List())) {
            case (accOpt, fsg) =>
              for {
                (success, acc)        <- accOpt
                (subSuccess, subTree) <- subgoalSolver(fsg(acc.map(_.node)))
              }
                yield (success && subSuccess, acc :+ subTree)
          }
        for {
          (success, l) <- subTrees
          (mergeSuccess, mergeJudgment) = merge(l.map(_.node))
        }
          yield (success && mergeSuccess, NodeTree(mergeJudgment, l))
    }
  }
}
