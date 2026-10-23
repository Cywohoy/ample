import Ample.Tactic.Rules
import Lean.Meta.Tactic.Assert
import Lean.Meta.DiscrTree

/-!
One-pass preparation of arithmetic facts. Mathematical modules register
one-premise implications; the tactic engine knows no domain definition names.
Derived facts are deduplicated and never fed back into this preparation pass.
-/

open Lean Meta Elab Tactic

namespace Ample.Automation

register_option ample.arith.maxPreparedFacts : Nat := {
  defValue := 64
  descr := "Maximum distinct facts derived from original arithmetic hypotheses."
}

initialize arithmeticPreparationIndex : EnvExtension (Array Name × DiscrTree Name) ←
  registerEnvExtension (pure (#[], {})) (asyncMode := .local)

private def premiseIndex : MetaM (DiscrTree Name) := do
  let names ← labelled `ample_arith_prepare
  let (cached, tree) := arithmeticPreparationIndex.getState (← getEnv)
  if cached == names then return tree
  let mut index : DiscrTree Name := {}
  for name in names do
    let (_, _, result) ← forallMetaTelescopeReducing (← getConstInfo name).type
    unless ← isProp result do
      throwError "Arithmetic preparation rule '{name}' must conclude a proposition."
    let (args, _, _) ← forallMetaTelescopeReducing (← getConstInfo name).type
    let premises ← args.filterM fun a => do isProp (← inferType a)
    unless premises.size == 1 do
      throwError "Arithmetic preparation rule '{name}' must have exactly one proof premise."
    index ← index.insert (← whnf (← inferType premises[0]!)) name
  modifyEnv (arithmeticPreparationIndex.setState · (names, index))
  return index

/-- Validate registered one-premise implications before speculative search. -/
def validateArithmeticPreparationRules : MetaM Unit := do
  discard premiseIndex

/-- Close a direct registered bridge using one original hypothesis, before any
arithmetic search. No derived context is retained on a failed attempt. -/
def closeByArithmeticBridge (goal : MVarId) : TacticM Bool := do
  if (← instantiateMVars (← goal.getType)).hasExprMVar then return false
  for name in ← labelled `ample_arith_prepare do
    let saved ← saveState
    try
      let remaining ← goal.withContext do
        goal.apply (← mkConstWithFreshMVarLevels name)
      if remaining.length == 1 then
        let premise := remaining.head!
        if ← premise.withContext <| isProp (← premise.getType) then
          premise.assumption
          return true
    catch _ => pure ()
    saved.restore
  return false

private def sharedData (left right : Expr) : Bool :=
  left.find? (fun e => e.isFVar && right.containsFVar e.fvarId!) |>.isSome

/-- Prepare registered facts from the initial hypotheses, without recursively
processing the newly derived facts. Local hypotheses and pending goals survive. -/
def prepareArithmeticFacts (goal : MVarId) : TacticM MVarId := goal.withContext do
  let index ← premiseIndex
  let originals ← getPropHyps
  let target ← instantiateMVars (← goal.getType)
  let targetHasData := target.hasFVar
  let mut relevant := #[target]
  -- Close relevance along hypotheses: a chain can pass through variables that
  -- are absent from the final goal, for example a~b, b~d, d~c implies a~c.
  let mut seenHyps : Std.HashSet FVarId := {}
  if targetHasData then
    for _ in [:originals.size] do
      let mut changed := false
      for h in originals do
        unless seenHyps.contains h do
          let type ← h.getType
          if relevant.any (sharedData · type) then
            relevant := relevant.push type
            seenHyps := seenHyps.insert h
            changed := true
      unless changed do break
  let mut known : Std.HashSet Expr := {}
  for h in originals do known := known.insert ((← h.getType).consumeMData)
  let mut current := goal
  let mut count := 0
  let limit := ample.arith.maxPreparedFacts.get (← getOptions)
  for h in originals do
    if count >= limit then break
    let type ← instantiateMVars (← h.getType)
    -- A ground goal or contradiction can depend on any original arithmetic fact.
    if targetHasData && !seenHyps.contains h then continue
    for name in ← index.getMatch (← whnf type) do
      if count >= limit then break
      let saved ← saveState
      let derived? ← try
        let lemma ← mkConstWithFreshMVarLevels name
        let (args, _, result) ← forallMetaTelescopeReducing (← inferType lemma)
        let premises ← args.filterM fun a => do isProp (← inferType a)
        let premise := premises[0]!
        if !(← isDefEq (← inferType premise) type) then pure none
        else
          premise.mvarId!.assign (mkFVar h)
          let result ← instantiateMVars result
          let proof ← instantiateMVars (mkAppN lemma args)
          if result.hasExprMVar || proof.hasExprMVar || known.contains result.consumeMData then pure none
          else pure (some (proof, result))
      catch _ => pure none
      match derived? with
      | none => saved.restore
      | some (proof, result) =>
        let (_, next) ← current.note (← mkFreshUserName `__ample_arithmetic) proof
        current := next
        known := known.insert result.consumeMData
        count := count + 1
  return current

end Ample.Automation
