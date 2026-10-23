import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.Change
import Lean.Elab.Tactic.Unfold
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Symm
import Ample.Tactic.Step
import Ample.Tactic.RelationRewrite

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Ample

-- Do not expand native rw's trailing unrestricted rfl: all transformations
-- share the same non-instantiating reflexivity check instead.
/-- Rewrite equalities/iffs with Lean's native rules, or rewrite a relation
inside a certified reversible proposition context. Relation actions must be
registered with `ample_rewrite`; arbitrary functions and integer equality are
not inferred to respect a non-equality relation. Additional conditions precede
the continuation. Use `using context` to provide an explicit certificate. -/
scoped syntax (name := ampleRewrite) "ample_rw " optConfig rwRuleSeq
  (" using " term)?
  (Lean.Parser.Tactic.location)? : tactic

/-- Rewrite using an explicit reversible relation context. Its condition, if
not already available, is left as a proof obligation before the continuation. -/
scoped syntax (name := ampleRewriteUsing) (priority := high) "rw " optConfig rwRuleSeq
  " using " term (Lean.Parser.Tactic.location)? : tactic

@[inherit_doc ampleRewrite, scoped macro Lean.Parser.Tactic.rwSeq, no_fallback]
def expandAmpleRewrite : Macro
  | `(tactic| rw $cfg:optConfig $rules:rwRuleSeq $[$loc:location]?) =>
    `(tactic| ample_rw $cfg:optConfig $rules:rwRuleSeq $[$loc]?)
  | _ => Macro.throwUnsupported

@[scoped macro ampleRewriteUsing, no_fallback]
def expandAmpleRewriteUsing : Macro
  | `(tactic| rw $cfg:optConfig $rules:rwRuleSeq using $context:term $[$loc:location]?) =>
    `(tactic| ample_rw $cfg:optConfig $rules:rwRuleSeq using $context:term $[$loc]?)
  | _ => Macro.throwUnsupported

private def rewriteOne (term : Syntax) (reverse : Bool) (hyp? : Option FVarId)
    (config : Rewrite.Config) (context? : Option Syntax) : TacticM Unit := do
  let saved ← saveState
  let originalError? ← if context?.isSome then pure none else
    try
      match hyp? with
      | none => rewriteTarget term reverse config
      | some hyp => rewriteLocalDecl term reverse hyp config
      return
    catch error =>
      saved.restore
      pure (some error)
  let result? ← Term.withSynthesize <| withMainContext do
    let goal ← getMainGoal
    let expression ← match hyp? with
      | none => goal.getType
      | some hyp => hyp.getType
    Automation.Relational.elabRewrite? goal expression term reverse config context?
  let some result := result? |
    match originalError? with
    | some error => throw error
    | none => throwError "An explicit relation context requires a relation proof."
  let result ← finishElabRewrite result
  let goal ← getMainGoal
  let next ← match hyp? with
    | none => goal.replaceTargetEq result.eNew result.eqProof
    | some hyp => do
      let replaced ← goal.replaceLocalDecl hyp result.eNew result.eqProof
      pure replaced.mvarId
  replaceMainGoal (next :: result.mvarIds)

-- A selected hypothesis may itself be the relation proof. Keep a private copy
-- for this rule so that rewriting it does not change the rule at later locations.
-- Ordinary equality/iff rewrites retain Lean's native elaboration path.
private def withStableRelationRule (term : Syntax) (action : Syntax → TacticM Unit) : TacticM Unit := do
  let saved ← saveState
  let proof? ← try withMainContext do
    let proof ← Term.elabTerm term none
    let (_, _, conclusion) ← forallMetaTelescopeReducing (← inferType proof)
    let reduced ← whnf conclusion
    if reduced.isAppOf ``Eq || reduced.isAppOf ``Iff ||
        conclusion.getAppNumArgs < 2 || !(← isProp conclusion) then return none
    return some proof
  catch _ => pure none
  let some proof := proof? | saved.restore; action term
  let name ← mkFreshUserName `_ample_rewrite_source
  let (source, next) ← (← getMainGoal).note name proof
  modifyMCtx fun context => context.setFVarKind next source .implDetail
  replaceMainGoal [next]
  action (mkIdent name)
  let mut remaining := []
  for goal in ← getUnsolvedGoals do
    let goal ← goal.withContext do
      if let some declaration := (← getLCtx).findFromUserName? name then
        goal.tryClear declaration.fvarId
      else pure goal
    remaining := remaining ++ [goal]
  setGoals remaining

@[tactic ampleRewrite] def evalAmpleRewrite : Tactic := fun stx => do
  let `(tactic| ample_rw $cfg:optConfig $rules:rwRuleSeq $[using $context:term]? $[$loc:location]?) := stx
    | throwUnsupportedSyntax
  Automation.runTransform do
    let config ← elabRewriteConfig cfg
    withRWRulesSeq stx[0] rules fun reverse term => do
      withStableRelationRule term fun stable =>
        withLocation (expandOptLocation stx[4])
          (fun hyp => rewriteOne stable reverse (some hyp) config context)
          (rewriteOne stable reverse none config context)
          (throwTacticEx `rw · "No matching occurrence was found in the selected locations.")
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
