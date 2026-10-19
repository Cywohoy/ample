import Lean.Elab.Tactic.Congr
import Ample.Tactic.Step

open Lean Meta Elab Tactic

namespace Course

/-- `congr : n` reduces equalities between applications to equalities between their arguments, to depth at most `n`.
For example, `congr : 1` reduces `f x = f y` to the sufficient condition `x = y`.
No injectivity of an arbitrary function is assumed, so the new conditions need not be equivalent to the original goal.
Depth uses the same notation as `ext : n` and `indisc : n`. -/
scoped syntax (name := courseCongrDepth) "congr" " : " num : tactic

private def congrAtDepth (depth : Nat) : TacticM Unit :=
  Automation.runTransform do
    let goals ← (← getMainGoal).congrN depth
    replaceMainGoal goals

@[tactic courseCongrDepth] def evalCourseCongrDepth : Tactic := fun stx =>
  congrAtDepth (⟨stx[2]⟩ : TSyntax `num).getNat

-- Preserve native congr's existing inference and compatibility spelling.
@[scoped tactic Lean.Parser.Tactic.congr, no_fallback]
def evalCourseCongr : Tactic := fun stx =>
  match stx with
  | `(tactic| congr $[$n:num]?) => congrAtDepth (n.map (·.getNat) |>.getD 1000000)
  | _ => throwUnsupportedSyntax

end Course
