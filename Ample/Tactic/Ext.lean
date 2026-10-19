/-
Native ext pattern processing is adapted from Lean.Elab.Tactic.Ext.
Copyright (c) 2021 Gabriel Ebner, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in Lean's LICENSE.
-/

import Lean.Elab.Tactic.Ext
import Lean.Meta.Tactic.Replace
import Ample.Tactic.Indisc
import Ample.Tactic.Step

open Lean Meta Elab Tactic

namespace Course.Automation

-- Expose the relation stored in a concrete Setoid, keeping its mathematical name.
private def exposeQuotientRelation (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← withReducible <| whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOfArity ``Setoid.r 4 do return goal
  let args := target.getAppArgs
  let bundle ← withDefault <| whnf args[1]!
  unless bundle.isAppOfArity ``Setoid.mk 3 do return goal
  let relation := mkApp2 bundle.getAppArgs[1]! args[2]! args[3]!
  return ← goal.replaceTargetDefEq relation

private def quotientStep? (goal : MVarId) : TermElabM (Option (List MVarId)) :=
    goal.withContext do
  let target ← withDefault <| whnf (← instantiateMVars (← goal.getType))
  let some (_, lhs, rhs) := target.eq? | return none
  if lhs.hasExprMVar || rhs.hasExprMVar then return none
  let left ← withDefault <| whnf lhs
  let right ← withDefault <| whnf rhs
  unless left.isAppOfArity ``Quot.mk 3 && right.isAppOfArity ``Quot.mk 3 do
    return none
  let saved ← saveState
  try
    let next ← goal.apply (← mkConstWithFreshMVarLevels ``Quotient.sound)
    return some (← next.mapM fun g => exposeQuotientRelation g)
  catch _ =>
    saved.restore
    return none

-- Keep native pattern processing and depth semantics at each ordinary ext step.
private partial def compareEquality (goal : MVarId)
    (pats : List (TSyntax `rcasesPat)) (depth : Nat)
    (failIfUnchanged : Bool) :
    TermElabM (Nat × Array (MVarId × List (TSyntax `rcasesPat))) := do
  if depth == 0 then return (0, #[(goal, pats)])
  if let some next ← registeredComparisonStep? goal then
    return (0, next.toArray.map (·, pats))
  if let some next ← quotientStep? goal then
    -- A quotient relation is the final comparison condition, not another ext step.
    return (0, next.toArray.map (·, pats))
  let (used, next) ← Lean.Elab.Tactic.Ext.extCore goal pats 1 failIfUnchanged
  let mut totalUsed := used
  let mut results := #[]
  for (subgoal, remaining) in next do
    let saved ← saveState
    try
      let (childUsed, children) ← compareEquality subgoal remaining (depth - 1) true
      totalUsed := totalUsed.max (used + childUsed)
      results := results ++ children
    catch _ =>
      saved.restore
      results := results.push (subgoal, remaining)
  return (totalUsed, results)

end Course.Automation

namespace Course

@[scoped tactic Lean.Elab.Tactic.Ext.applyExtTheorem]
def evalCourseApplyExtTheorem : Tactic := fun _ => do
  let goal ← getMainGoal
  if let some next ← Automation.registeredComparisonStep? goal then
    replaceMainGoal next
  else if let some next ← Automation.quotientStep? goal then
    replaceMainGoal next
  else
    replaceMainGoal (← Lean.Elab.Tactic.Ext.applyExtTheoremAt goal)

/-- `ext` applies one mathematical comparison rule to an equality goal.
For example, pairs produce component equalities and sets produce membership equivalences.
Use `ext x` to name an arbitrary function argument or set element.
Use `ext : n` for a fixed depth, or `ext!` to repeat comparisons. -/
scoped syntax (name := courseExt) (priority := high)
  "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic

@[tactic courseExt, scoped tactic Lean.Elab.Tactic.Ext.ext, no_fallback]
def evalCourseExt : Tactic := fun stx => Automation.runTransform do
  let pats := RCases.expandRIntroPats (stx[1].getArgs.map (fun p => (⟨p⟩ : TSyntax `rintroPat)))
  let depth := if stx[2].isNone then 1 else (⟨stx[2][1]⟩ : TSyntax `num).getNat
  let (used, goals) ← Automation.compareEquality (← getMainGoal) pats.toList depth true
  if RCases.linter.unusedRCasesPattern.get (← getOptions) then
    if used < pats.size then
      let unused := MessageData.andList <| pats[used...*].toList.map (m!"`{·}`")
      Linter.logLint RCases.linter.unusedRCasesPattern (mkNullNode pats[used...*].toArray)
        m!"`ext` did not consume the patterns {unused}"
  replaceMainGoal (← goals.toList.mapM fun g => Automation.normalizeComparisonGoal g.1)


open Course.Automation in
/-- `ext with first second` reduces an equality to its comparison conditions and names the resulting goals.
The default applies one comparison rule. Use `ext : n` for a fixed depth or `ext!` to repeat.
Select a named goal with `case first => ...`.

For example, an equality of pairs produces equalities of their components.
For functions, `ext x with value` introduces an arbitrary argument `x`. -/
scoped syntax (name := courseExtNamed) (priority := high)
  "ext" (colGt ppSpace rintroPat)* (" : " num)?
  " with" (ppSpace colGt ruleOutput)+ : tactic
open Course.Automation in
/-- `ext!` repeats mathematical comparisons, optionally naming the resulting goals with `with`.
Use `ext` to apply just one comparison rule. -/
scoped syntax (name := courseExtRecursive)
  "ext!" (colGt ppSpace rintroPat)* (" with" (ppSpace colGt ruleOutput)+)?
  (" : " num)? : tactic

@[tactic courseExtNamed] def evalCourseExtNamed : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    let binders := RCases.expandRIntroPats (stx[1].getArgs.map (fun p => (⟨p⟩ : TSyntax `rintroPat)))
    let patterns ← stx[4].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
    let depth := if stx[2].isNone then 1 else (⟨stx[2][1]⟩ : TSyntax `num).getNat
    let (_, next) ← Automation.compareEquality (← getMainGoal) binders.toList depth true
    replaceMainGoal (← Automation.nameRuleGoals (← next.toList.mapM fun g => Automation.normalizeComparisonGoal g.1) patterns)
  catch e => saved.restore; throw e

@[tactic courseExtRecursive] def evalCourseExtRecursive : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    let binders := RCases.expandRIntroPats (stx[1].getArgs.map (fun p => (⟨p⟩ : TSyntax `rintroPat)))
    let patterns ← if stx[2].isNone then pure #[] else
      stx[2][1].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
    let depth := if stx[3].isNone then 32 else (⟨stx[3][1]⟩ : TSyntax `num).getNat
    let (_, next) ← Automation.compareEquality (← getMainGoal) binders.toList depth true
    replaceMainGoal (← Automation.nameRuleGoals (← next.toList.mapM fun g => Automation.normalizeComparisonGoal g.1) patterns)
  catch e => saved.restore; throw e

end Course
