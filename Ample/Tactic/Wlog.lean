/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Johan Commelin, Reid Barton, Thomas Murrills

Adapted from Mathlib/Tactic/WLOG.lean for Lean v4.35.0.
The generalized case and reduction case are preserved. Lean's reversion API
replaces mathlib-specific context helpers; no Mathlib dependency is required.
Source: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/WLOG.lean
-/
import Ample.Tactic.Classical
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Cases

open Lean Meta Elab Tactic

namespace Ample.Automation

def wlogRule (goal : MVarId) (condition : Expr) (name : Name)
    (variables : Array FVarId) (reductionName : Name) :
    TacticM (List MVarId) := goal.withContext do
  unless ← isProp (← goal.getType) do throwError "wlog requires a proposition goal."
  let restrictedType ← mkArrow condition (← goal.getType)
  let scratch ← mkFreshExprSyntheticOpaqueMVar restrictedType
  let (reverted, generalGoal) ← scratch.mvarId!.revert variables (preserveOrder := true)
  let generalType ← generalGoal.getType
  let (handle, reduction) ← goal.note reductionName (.mvar generalGoal) generalType
  let (_, restricted) ← generalGoal.introNP reverted.size
  let (_, restricted) ← restricted.intro name
  let (⟨easy, positive⟩, ⟨reduction, _⟩) ← reduction.byCases condition name
  easy.withContext do
    let arguments ← reverted.filterM (notM ·.isLetVar)
    let proof := mkAppN (.fvar handle) (arguments.map .fvar) |>.app (.fvar positive)
    easy.assign proof
  let parent ← goal.getTag
  reduction.setTag (appendTag parent `reduction)
  restricted.setTag (appendTag parent `restricted)
  return [← markClassicalGoal reduction, ← markClassicalGoal restricted]

end Ample.Automation

namespace Ample
/-- `wlog h : P` reduces a proof to the case where condition `P` holds.
First prove the `reduction` goal, which handles `¬ P` using the restricted result; then prove the `restricted` goal with `h : P`.
`generalizing x y` selects variables available to the reduction, and `with reduced` names the restricted result. -/
scoped syntax (name := ampleWlog)
  "wlog " binderIdent " : " term
  (" generalizing" (ppSpace colGt ident)*)? (" with " ident)? : tactic

@[tactic ampleWlog] def evalAmpleWlog : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let name := match stx[1] with
        | `(binderIdent| $id:ident) => id.getId
        | _ => `h
      let condition ← Term.elabTermEnsuringType stx[3] (mkSort .zero)
      let variables ← if stx[4].isNone then do
        (← getLCtx).getFVarIds.filterM fun id => do
          pure (!(← id.getDecl).isImplementationDetail)
      else stx[4][1].getArgs.mapM elabAsFVar
      let reductionName := if stx[5].isNone then `this else stx[5][1].getId
      replaceMainGoal (← Automation.wlogRule (← getMainGoal) condition name variables reductionName)
  catch e => saved.restore; throw e

end Ample

