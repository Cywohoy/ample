import Lean.Elab.Tactic.Location
import Lean.Meta.Transform
import Lean.Meta.RecExt
import Lean.Meta.Tactic.Simp.Main
import Ample.Tactic.Step

/-!
Select one outer layer of definitions from the mathematical library or the current file.
After unfolding, Lean's dsimp engine computes argument substitution and pattern matching.
-/

open Lean Meta Elab Tactic

namespace Course.Automation

private def isLearnerDefinition (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => true
  | some idx => (`AlgebraBook).isPrefixOf env.header.moduleNames[idx.toNat]! || (`Ample.Math).isPrefixOf env.header.moduleNames[idx.toNat]!

-- Use Lean's definitional computation without theorem-based simplification rules.
private def reduceSurface (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (config := { zetaDelta := false })
  let (result, _) ← Meta.dsimp e ctx
  return result

private def expandHead? (e : Expr) : MetaM (Option Expr) := do
  let e ← if let .const name _ := e.getAppFn then
    if ((← getEnv).getProjectionFnInfo? name).any (·.fromClass) then
      withReducibleAndInstances <| whnf e
    else pure e
  else pure e
  if e.isHeadBetaTarget then return some (← reduceSurface e.headBeta)
  if let .letE _ _ value body _ := e then
    return some (← reduceSurface (body.instantiate1 value))
  if let .fvar id := e.getAppFn then
    if let some value := (← id.getDecl).value? then
      return some (← reduceSurface (mkAppN value e.getAppArgs))
    return none
  let .const name _ := e.getAppFn | return none
  -- Compute match auxiliaries with dsimp rather than selecting them as mathematical definitions.
  if (← getMatcherInfo? name).isSome then return none
  let env ← getEnv
  unless isLearnerDefinition env name do return none
  let some (.defnInfo info) := env.find? name | return none
  unless info.safety == .safe do return none
  if ← isIrreducible name then return none
  -- Keep the name of a function that has not received its arguments.
  if info.value.getNumHeadLambdas > e.getAppNumArgs then return none
  -- Unfold a recursive function only when its supplied arguments allow actual computation.
  if (← isRecursiveDefinition name) && !hasSmartUnfoldingDecl env name then
    return none
  let some unfolded ← unfoldDefinition? e (ignoreTransparency := true) | return none
  if unfolded == e then return none
  return some (← reduceSurface unfolded)

/-- Unfold the outermost definition in each part of an expression by one layer. -/
def unfoldExpression (e : Expr) : TacticM Expr := do
  let (result, _) ← Meta.transformWithCache e {}
    (pre := fun e => do
      if ← isProof e then return .done e
      if (← inferType e).isSort && !(← isProp e) then return .done e
      if let .const name _ := e.getAppFn then
        if (← getMatcherInfo? name).isSome ||
            ((← getEnv).find? name).any (fun info =>
              match info with | .recInfo _ => true | _ => false) then
          return .done (← reduceSurface e)
      -- Skip membership interface declarations and unfold one layer of the set definition.
      if e.isAppOfArity ``Membership.mem 5 then
        let args := e.getAppArgs
        if args[2]!.getAppFn.isConstOf `Course.instMembershipSet then
          let application := mkApp args[3]! args[4]!
          if let some expanded ← expandHead? application then
            return .done expanded
          return .done e
      if let some expanded ← expandHead? e then
        return .done expanded
      return .continue)
    (skipConstInApp := true) (skipInstances := true)
  return ← reduceSurface result

end Course.Automation

namespace Course

/-- `expand` unfolds one outer layer of mathematical-library or current-file definitions in each part of an expression.
It also computes argument substitution, local definitions, projections, and pattern matching on supplied constructors.
Newly exposed definitions remain for the next call. It does not split conjunctions or apply arithmetic lemmas.

Use `expand at h` for a hypothesis, or `expand at *` for all hypotheses and the goal.
Reflexive equalities produced in the current step are closed automatically. -/
scoped syntax (name := courseExpand) "expand" (Lean.Parser.Tactic.location)? : tactic

-- Keep the old name available for existing proof files.
@[inherit_doc courseExpand]
scoped syntax (name := courseUnfoldAuto) "unfold_auto" (Lean.Parser.Tactic.location)? : tactic

@[tactic courseExpand, tactic courseUnfoldAuto]
def evalExpand : Tactic := fun stx => Automation.runTransform do
  withLocation (expandOptLocation stx[1])
    (fun h => do
      let goal ← getMainGoal
      goal.withContext do
        let type ← instantiateMVars (← h.getType)
        let result ← Automation.unfoldExpression type
        replaceMainGoal [← goal.replaceLocalDeclDefEq h result])
    (do
      let goal ← getMainGoal
      goal.withContext do
        let target ← instantiateMVars (← goal.getType)
        let result ← Automation.unfoldExpression target
        replaceMainGoal [← goal.replaceTargetDefEq result])
    (fun _ => throwError "Unable to unfold the selected expressions.")


/-- `expand!` repeats `expand` until no further change occurs.
Use `expand! at h` to process a hypothesis. Expansion is limited to 32 iterations to prevent unbounded unfolding.
If the limit is exceeded, use explicit `expand` steps for the required recursive definitions. -/
scoped syntax (name := courseExpandRecursive) "expand!" (Lean.Parser.Tactic.location)? : tactic

@[tactic courseExpandRecursive] def evalExpandRecursive : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  let reduce (e : Expr) : TacticM Expr := do
    let mut current := e
    for _ in [:32] do
      let next ← Automation.unfoldExpression current
      if next == current then return current
      current := next
    throwError "Recursive expansion exceeded 32 steps; use explicit expand steps for recursive definitions."
  try
    withLocation (expandOptLocation stx[1])
      (fun h => do
        let goal ← getMainGoal
        goal.withContext do
          let type ← instantiateMVars (← h.getType)
          replaceMainGoal [← goal.replaceLocalDeclDefEq h (← reduce type)])
      (do
        let goal ← getMainGoal
        goal.withContext do
          let type ← instantiateMVars (← goal.getType)
          replaceMainGoal [← goal.replaceTargetDefEq (← reduce type)])
      (fun _ => throwError "Unable to expand the selected expressions.")
  catch e => saved.restore; throw e

end Course
