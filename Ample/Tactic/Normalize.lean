import Lean.Elab.Tactic.Simp
import Ample.Tactic.Rules
import Ample.Tactic.Classical

/-!
Shared presentation normalization. Apply registered expression rewrites and definitional computation
without unfolding all mathematical definitions or solving goals from hypotheses.
-/

open Lean Meta Elab Tactic

attribute [course_norm] Nat.not_lt Nat.not_le Int.not_lt Int.not_le
attribute [course_classical_norm] Classical.not_not
attribute [course_norm_hyp] Subtype.ext_iff Fin.ext_iff Prod.mk.injEq

register_option course.autoNormalize : Bool := {
  defValue := true
  descr := "Normalize expressions automatically in the Course.Auto scope"
}

namespace Course.Automation

-- Preserve membership notation for named sets; compute a literal predicate by beta reduction.
dsimproc ↓ [course_norm] anonymousMembership (@Membership.mem _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  unless args.size == 5 && args[2]!.getAppFn.isConstOf `Course.instMembershipSet do
    return .continue
  let predicate := args[3]!.consumeMData
  if predicate.isLambda then
    return .done (mkApp predicate args[4]!).headBeta
  return .done e

private def isConstructedEquality (type : Expr) : MetaM Bool := do
  let some (_, lhs, rhs) := type.consumeMData.eq? | return false
  let lhs ← withReducible <| whnf lhs
  let rhs ← withReducible <| whnf rhs
  let constructors := [``Subtype.mk, ``Fin.mk, ``Prod.mk]
  return constructors.any (lhs.getAppFn.isConstOf ·) &&
    constructors.any (rhs.getAppFn.isConstOf ·)

def normalizeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let classicalEnabled ← classicalNormalizationEnabled
  -- `simp only` includes eq_self and iff_self by default. Exclude them so
  -- normalization preserves proof obligations even inside a conjunction.
  -- Selected transformation results get their reflexivity check separately.
  let targetSyntax ← if classicalEnabled then
    `(tactic| simp (config := { zetaDelta := true }) only
      [course_norm, course_classical_norm, -eq_self, -iff_self])
  else
    `(tactic| simp (config := { zetaDelta := true }) only
      [course_norm, -eq_self, -iff_self])
  let hypSyntax ← if classicalEnabled then
    `(tactic| simp (config := { zetaDelta := true }) only
      [course_norm, course_classical_norm, course_norm_hyp, -eq_self, -iff_self])
  else
    `(tactic| simp (config := { zetaDelta := true }) only
      [course_norm, course_norm_hyp, -eq_self, -iff_self])
  let targetCtx ← mkSimpContext targetSyntax (eraseLocal := false)
  let hypCtx ← mkSimpContext hypSyntax (eraseLocal := false)
  let dsimpSyntax ← `(tactic| dsimp (config := { zetaDelta := true }) only [course_norm])
  let dsimpCtx ← mkSimpContext dsimpSyntax (eraseLocal := false) (kind := .dsimp)
  let mut current := goal
  -- Normalize the target first to reduce dependencies on subtype proof fields.
  let originalTarget ← instantiateMVars (← current.getType)
  let (target, _) ← Meta.dsimp originalTarget dsimpCtx.ctx dsimpCtx.simprocs
  current ← current.replaceTargetDefEq target
  let (result, _) ← Meta.simp target targetCtx.ctx targetCtx.simprocs
  unless result.expr.consumeMData.isTrue || result.expr.consumeMData.isFalse do
    current ← applySimpResultToTarget current target result
  -- Do not use hypotheses as rewrite rules or automatically prove truth or contradiction.
  let hypotheses ← current.withContext getPropHyps
  for hyp in hypotheses do
    current ← current.withContext do
      let originalType ← instantiateMVars (← hyp.getType)
      let (type, _) ← Meta.dsimp originalType dsimpCtx.ctx dsimpCtx.simprocs
      let current ← current.replaceLocalDeclDefEq hyp type
      -- Add value comparisons for constructed elements while retaining the original equality.
      -- Equalities of variable elements remain usable directly by exact and rw.
      let ctx := if ← isConstructedEquality type then hypCtx else targetCtx
      let (result, _) ← Meta.simp type ctx.ctx ctx.simprocs
      if result.expr.consumeMData.isTrue || result.expr.consumeMData.isFalse then
        return current
      if ← isConstructedEquality type then
        -- Add the value equality without replacing the original element equality.
        let mut known := false
        for decl in ← getLCtx do
          if ← withNewMCtxDepth <| isDefEq decl.type result.expr then
            known := true
        if known then return current
        let some (proof, newType) ← applySimpResult current (mkFVar hyp) type result
            (mayCloseGoal := false) | return current
        let name ← mkFreshUserName ((← hyp.getDecl).userName.appendAfter "_values")
        let (_, next) ← current.note name proof newType
        return next
      let some (_, next) ← applySimpResultToLocalDecl current hyp result
          (mayCloseGoal := false) | return current
      return next
  return current

/-- Normalize expressions in all open goals and their hypotheses. -/
def normalizeGoals : TacticM Unit := do
  let mut normalized := []
  for goal in ← getUnsolvedGoals do
    let next ← normalizeGoal goal
    normalized := normalized ++ [next]
  setGoals normalized

end Course.Automation
