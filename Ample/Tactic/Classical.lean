import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Classical
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Apply

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Ample.Automation

-- A hidden context marker follows the subgoals of a classical proof step.
-- It is an inhabited proposition, not an additional logical axiom.
private inductive ClassicalNormalizationScope : Prop where
  | active

def classicalNormalizationEnabled : MetaM Bool := do
  if ← Meta.isInstance ``Classical.propDecidable then return true
  return (← getLCtx).any fun decl =>
    decl.type.isConstOf ``ClassicalNormalizationScope

def markClassicalGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  if (← getLCtx).any (fun decl =>
      decl.type.isConstOf ``ClassicalNormalizationScope) then
    return goal
  let (_, next) ← goal.assertHypotheses #[{
    userName := `_ampleClassicalNormalization
    type := mkConst ``ClassicalNormalizationScope
    value := mkConst ``ClassicalNormalizationScope.active
    kind := .implDetail
  }]
  return next

private def contradictionGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless ← isProp target do
    throwTacticEx `by_contra goal "The goal must be a proposition"
  let unfolded ← whnf target
  if unfolded.isArrow && unfolded.bindingBody!.isConstOf ``False then
    return ← goal.replaceTargetDefEq unfolded
  let principle ← if let some dec ← synthInstance? (mkApp (mkConst ``Decidable) target) then
    pure <| mkApp2 (mkConst ``Decidable.byContradiction) target dec
  else
    pure <| mkApp (mkConst ``Classical.byContradiction) target
  let [next] ← goal.apply principle
    | throwTacticEx `by_contra goal "Unable to start a proof by contradiction"
  return next

end Ample.Automation

namespace Ample

/-- `by_contra h` starts a proof by contradiction: for a goal `P`, it introduces `h : ¬ P` and changes the goal to `False`.
For a negated goal `¬ P`, it instead introduces `h : P` with goal `False`.
The default name is `this`; an optional `: ...` specifies the introduced hypothesis type. -/
syntax (name := byContra) "by_contra" (ppSpace colGt rcasesPatMed)? (" : " term)? : tactic

@[tactic byContra]
def evalByContra : Tactic := fun stx => do
  match stx with
  | `(tactic| by_contra $[$pat?]? $[: $ty?]?) =>
    let untouched := (← getGoals).drop 1
    let pat ← pat?.getDM `(rcasesPatMed| $(mkIdent `this):ident)
    let next ← Automation.contradictionGoal (← getMainGoal)
    replaceMainGoal [next]
    -- Do not normalize the intermediate ¬P → False back to P before introducing ¬P.
    withOptions (fun options => options.setBool `ample.autoNormalize false) do
      evalTactic (← `(tactic| rintro ($pat:rcasesPatMed) $[: $ty?]?))
    let mut next := []
    for goal in ← getUnsolvedGoals do
      let marked ← if untouched.contains goal then pure goal
        else Automation.markClassicalGoal goal
      next := next ++ [marked]
    setGoals next
  | _ => throwUnsupportedSyntax

end Ample
