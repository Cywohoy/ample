import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Refl
import Ample.Tactic.Normalize

/-! Shared postprocessing for a selected proof step. Existing pending goals
are never included implicitly. Reflexivity may solve a proof goal, but may
not choose values for metavariables that existed before the check. -/

open Lean Meta Elab Tactic

register_option ample.inAutoStep : Bool := {
  defValue := false
  descr := "Internal: normalize selected transformation results in Ample.Auto"
}

namespace Ample.Automation

def closeReflexive (goal : MVarId) : MetaM Bool := do
  if ← goal.isAssigned then return true
  let saved ← saveState
  try
    let proof? ← goal.withContext <| withNewMCtxDepth <| withReducible do
      let target := (← instantiateMVars (← goal.getType)).consumeMData
      if let some (_, lhs, rhs) := target.eq? then
        if ← isDefEq lhs rhs then return some (← mkEqRefl lhs)
      if target.isAppOfArity ``Iff 2 then
        if ← isDefEq target.getAppArgs[0]! target.getAppArgs[1]! then
          return some (mkApp (mkConst ``Iff.rfl) target.getAppArgs[0]!)
      if let some (_, lhs, _, rhs) := target.heq? then
        if ← isDefEq (← inferType lhs) (← inferType rhs) then
          if ← isDefEq lhs rhs then return some (← mkAppM ``HEq.refl #[lhs])
      return none
    if let some proof := proof? then
      goal.assign proof
      return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- Only the explicitly supplied results are normalized and checked. -/
def finishTransformGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining := []
  for goal in goals do
    unless ← goal.isAssigned do
      let goal ← if ample.inAutoStep.get (← getOptions) then
        -- Context construction for simp/dsimp reads the current tactic goal.
        -- A combined result is not in that list yet, and its old goals may
        -- already be assigned. Install only this result while normalizing it.
        let pending ← getGoals
        try
          setGoals [goal]
          normalizeGoal goal
        finally
          setGoals pending
      else pure goal
      unless ← closeReflexive goal do remaining := remaining ++ [goal]
  remaining.filterM fun goal => return !(← goal.isAssigned)

/-- Isolate the current goal, execute one transformation, and process its
results. Zero results do not advance postprocessing to a pending sibling. -/
def runTransform (action : TacticM Unit) : TacticM Unit := do
  let saved ← saveState
  try
    focus do
      action
      setGoals (← finishTransformGoals (← getUnsolvedGoals))
  catch error =>
    saved.restore
    throw error

end Ample.Automation
