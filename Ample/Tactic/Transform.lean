import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.Change
import Lean.Elab.Tactic.Unfold
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Symm
import Ample.Tactic.Step

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Ample

-- Do not expand native rw's trailing unrestricted rfl: all transformations
-- share the same non-instantiating reflexivity check instead.
@[inherit_doc Lean.Parser.Tactic.rewriteSeq]
scoped syntax (name := ampleRewrite) "ample_rw " optConfig rwRuleSeq
  (Lean.Parser.Tactic.location)? : tactic

scoped macro_rules
  | `(tactic| rw $cfg:optConfig $rules:rwRuleSeq $[$loc:location]?) =>
    `(tactic| ample_rw $cfg:optConfig $rules:rwRuleSeq $[$loc]?)

@[tactic ampleRewrite] def evalAmpleRewrite : Tactic := fun stx => do
  let `(tactic| ample_rw $cfg:optConfig $rules:rwRuleSeq $[$loc:location]?) := stx
    | throwUnsupportedSyntax
  Automation.runTransform do
    Lean.Elab.Tactic.evalRewriteSeq (← `(tactic| rewrite $cfg:optConfig $rules:rwRuleSeq $[$loc]?))
    -- Lean leaves the rewritten continuation first. Establish any extra
    -- conditions in their original contexts before returning to it.
    let goals ← getUnsolvedGoals
    if goals.length > 1 then setGoals (goals.tail! ++ [goals.head!])

@[scoped tactic Lean.Parser.Tactic.change, no_fallback]
def evalAmpleChange : Tactic := fun stx =>
  Automation.runTransform <| Lean.Elab.Tactic.evalChange stx

@[scoped tactic Lean.Parser.Tactic.unfold, no_fallback]
def evalAmpleUnfold : Tactic := fun stx =>
  Automation.runTransform <| Lean.Elab.Tactic.evalUnfold stx

@[scoped tactic Lean.Parser.Tactic.symm, no_fallback]
def evalAmpleSymm : Tactic := fun stx =>
  Automation.runTransform <| Lean.Elab.Tactic.evalSymm stx

@[scoped tactic Lean.Parser.Tactic.dsimp, no_fallback]
def evalAmpleDSimp : Tactic := fun stx =>
  Automation.runTransform do
    let { ctx, simprocs, .. } ← withMainContext <|
      mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let changed ← IO.mkRef false
    let compute (type : Expr) : MetaM Expr := do
      let result := (← Meta.dsimp type ctx simprocs).1
      if result != type then changed.set true
      return result
    withLocation (expandOptLocation stx[5])
      (fun hyp => do
        let goal ← getMainGoal
        let next ← goal.withContext do
          goal.replaceLocalDeclDefEq hyp (← compute (← hyp.getType))
        replaceMainGoal [next])
      (do
        let goal ← getMainGoal
        let next ← goal.withContext do
          goal.replaceTargetDefEq (← compute (← goal.getType))
        replaceMainGoal [next])
      (fun _ => throwError "Unable to simplify the selected expressions.")
    if ctx.config.failIfUnchanged && !(← changed.get) then
      let remaining ← Automation.finishTransformGoals (← getUnsolvedGoals)
      unless remaining.isEmpty do throwError "'dsimp' made no progress."
      setGoals []

end Ample
