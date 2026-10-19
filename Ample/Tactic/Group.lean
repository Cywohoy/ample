import Ample.Tactic.Arithmetic
import Lean.Elab.Tactic.Simp

open Lean Meta Elab Tactic

namespace Course

/-- `group_calc G` calculates group expressions using laws specialized to the group structure `G`.
It uses registered identity, inverse, associativity, and power laws, and delegates numeric side conditions and exponent arithmetic to `arith`.
Any required commutativity assumptions must be available.
Enable `set_option trace.Course.group true` to inspect the registered lemmas and hypotheses used. -/
scoped syntax (name := courseGroupCalc) "group_calc " term : tactic

/-- Use only the group laws specialized to the explicitly supplied structure. -/
@[tactic courseGroupCalc]
def evalGroupCalc : Tactic := fun stx => do
  let saved ← saveState
  let original ← getMainGoal
  try
    withMainContext do
      let group ← Term.elabTerm stx[1] none
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← whnf (← inferType group)
      unless type.isAppOfArity `Course.Group 1 do
        throwError "Expected a Course.Group structure."
      let mut rules : Array (TSyntax `term) := #[]
      for name in ← labelled `course_group_rules do
        let specialized ← mkAppM name #[group]
        rules := rules.push (← Term.exprToSyntax specialized)
      evalTactic (← `(tactic| solve
        | (try simp (disch := first | assumption | (symm; assumption)) only [$[$rules:term],*]
           all_goals arith)))
      Automation.traceCompletedProof `Course.group original
        (← labelled `course_group_rules)
        "Group calculation using the supplied structure and arithmetic."
  catch e =>
    saved.restore
    throwError "Unable to prove the goal using the supplied group structure and arithmetic.
{e.toMessageData}"

end Course

