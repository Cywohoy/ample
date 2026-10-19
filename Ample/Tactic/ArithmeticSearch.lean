import Ample.Tactic.ArithmeticRules
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Simp
import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Assert

/-!
Select arithmetic lemmas by the shape of the goal and discharge their premises recursively.
Depth and attempt limits prevent repeated exploration of the same goal.
-/

open Lean Meta Elab Tactic

namespace Ample.Automation

-- This derived cache is local to each elaboration branch; it registers no new rules.
initialize arithmeticRuleIndex : EnvExtension (Array Name × DiscrTree Name) ←
  registerEnvExtension (pure (#[], {})) (asyncMode := .local)

-- Expose bounds of Fin values occurring in the expression within this simplification only.
private def addFinBounds (goal : MVarId) : TacticM MVarId := goal.withContext do
  let mut roots := #[← goal.getType]
  let mut known : Std.HashSet Expr := {}
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      roots := roots.push decl.type
      if ← isProp decl.type then
        known := known.insert decl.type.consumeMData
      else if (← whnf decl.type).isAppOfArity ``Fin 1 then
        roots := roots.push (← mkAppM ``Fin.val #[decl.toExpr])
  let bounds ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef known
  for root in roots do
    root.forEach' fun e => do
      if e.hasLooseBVars then return false
      if ← isProof e then return false
      if e.isAppOfArity ``Fin.val 2 then
        let proof := mkApp2 (mkConst ``Fin.isLt) e.getAppArgs[0]! e.getAppArgs[1]!
        let type := (← inferType proof).consumeMData
        unless (← seen.get).contains type do
          seen.modify (·.insert type)
          bounds.modify (·.push proof)
        return false
      return true
  let mut current := goal
  for proof in ← bounds.get do
    let (_, next) ← current.note (← mkFreshUserName `__ample_bound) proof
    current := next
  return current

private def makeRuleIndex : MetaM (DiscrTree Name) := do
  let names ← labelled `ample_arith_apply
  let (cachedNames, cachedIndex) := arithmeticRuleIndex.getState (← getEnv)
  if names == cachedNames then return cachedIndex
  let mut index : DiscrTree Name := {}
  for name in names do
    let (_, _, conclusion) ← forallMetaTelescopeReducing (← getConstInfo name).type
    index ← index.insert conclusion name
  modifyEnv (arithmeticRuleIndex.setState · (names, index))
  return index

private def closeUsing (goal : MVarId) (tactic : Syntax) : TacticM Bool := do
  let saved ← saveState
  try
    let remaining ← evalTacticAt tactic goal
    if remaining.isEmpty then return true
  catch _ => pure ()
  saved.restore
  return false

-- Keep logical introductions and outer comparisons as explicit proof steps.
private def closeByCalculation (goal : MVarId) : TacticM Bool := do
  let simpRules := mkIdent `ample_arith_simp
  closeUsing goal (← `(tactic| solve
    | omega
    | (simp (disch := omega) only [$simpRules:ident] at *; all_goals omega)))

private partial def search (index : DiscrTree Name) (goal : MVarId)
    (depth : Nat) (ancestors : List Expr) (budget : IO.Ref Nat) : TacticM Bool := do
  if ← goal.isAssigned then return true
  if (← budget.get) == 0 then return false
  budget.modify (· - 1)
  let target ← goal.withContext <| instantiateMVars (← goal.getType)
  -- Restore failed branches and branches that return to the same goal.
  if target.hasExprMVar || ancestors.contains target then return false
  if ← closeByCalculation goal then return true
  if depth == 0 then return false
  let candidates ← goal.withContext <| index.getMatch target
  for name in candidates do
    let saved ← saveState
    try
      let next ← goal.withContext do
        goal.apply (← mkConstWithFreshMVarLevels name)
      let mut success := true
      for subgoal in next do
        unless ← search index subgoal (depth - 1) (target :: ancestors) budget do
          success := false
          break
      if success then return true
    catch _ => pure ()
    saved.restore
  return false

/-- Perform bounded, goal-directed arithmetic search using Fin bounds. -/
def searchArithmetic (goal : MVarId) : TacticM Bool := do
  if ← closeUsing goal (← `(tactic| omega)) then return true
  let saved ← saveState
  let goal ← addFinBounds goal
  let index ← makeRuleIndex
  let budget ← IO.mkRef 64
  if ← search index goal 4 [] budget then return true
  saved.restore
  return false

end Ample.Automation
