import Ample.Tactic.Rules
import Lean.Meta

/-! Registered iff theorems connect equalities and comparison conditions.
Matching does not select representatives or invent unresolved arguments. -/

open Lean Meta

namespace Course.Automation

/-- Match the equality side of a registered comparison iff without leaving unresolved arguments. -/
def registeredComparison? (equality : Expr) : MetaM (Option (Expr × Expr)) := do
  unless equality.consumeMData.eq?.isSome do return none
  if equality.hasExprMVar then return none
  for name in ← labelled `course_compare do
    let saved ← saveState
    try
      let constant ← mkConstWithFreshMVarLevels name
      let (arguments, _, conclusion) ← forallMetaTelescopeReducing (← inferType constant)
      unless conclusion.isAppOfArity ``Iff 2 do failure
      unless ← withDefault <| isDefEq conclusion.getAppArgs[0]! equality do failure
      let lemma ← instantiateMVars (mkAppN constant arguments)
      let condition ← instantiateMVars conclusion.getAppArgs[1]!
      if lemma.hasExprMVar || condition.hasExprMVar then failure
      return some (lemma, condition)
    catch _ => saved.restore
  return none

/-- Reduce an equality goal using its registered iff, preserving its named condition. -/
def registeredComparisonStep? (goal : MVarId) : MetaM (Option (List MVarId)) :=
    goal.withContext do
  let equality ← withDefault <| whnf (← instantiateMVars (← goal.getType))
  let some (lemma, _) ← registeredComparison? equality
    | return none
  return some (← goal.apply (← mkAppM ``Iff.mpr #[lemma]))

end Course.Automation
