import Tests.RelationRewrite

open Ample Lean Meta Elab Tactic

namespace RelationRewriteStateTests

private def snapshot : TacticM (List MVarId × Array (Expr × Array (FVarId × Expr))) := do
  let goals ← getGoals
  let mut states := #[]
  for goal in goals do
    let context ← goal.withContext do
      return (← getLCtx).foldl (init := #[]) fun a d => a.push (d.fvarId, d.type)
    states := states.push (← goal.getType, context)
  return (goals, states)

elab "check_relation_restore" : tactic => do
  let before ← snapshot
  let messages ← Core.getMessageLog
  let hab := mkIdent `hab
  let bad := mkIdent `bad
  let original ← saveState
  evalTactic (← `(tactic| rw [$hab:ident]))
  unless (← snapshot) != before do throwError "The first rewrite made no change."
  original.restore
  let failed ← tryCatchRuntimeEx
    (do evalTactic (← `(tactic| rw [$hab:ident, $bad:ident])); pure false)
    (fun _ => pure true)
  Core.setMessageLog messages
  unless failed do throwError "Expected an uncertified rewrite to fail."
  unless (← snapshot) == before do throwError "A failed relation rewrite changed the proof state."

example (n a b : Int) (hab : Congruent n a b) (bad : Congruent 2 0 2) :
    Congruent n a a ∧ True := by
  constructor
  check_relation_restore
  · exact congruent_refl n _
  · trivial

elab "check_relation_budget" : tactic => do
  let before ← snapshot
  let messages ← Core.getMessageLog
  let hab := mkIdent `hab
  let failed ← withOptions (fun o => o.set `ample.rewrite.maxSteps (0 : Nat)) do
    tryCatchRuntimeEx
      (do evalTactic (← `(tactic| rw [$hab:ident])); pure false)
      (fun _ => pure true)
  Core.setMessageLog messages
  unless failed && (← snapshot) == before do
    throwError "A relation rewrite budget failure changed the proof state."

example (n a b : Int) (hab : Congruent n a b) : Congruent n a a := by
  check_relation_budget
  exact congruent_refl n _

/-- error: Relation rewrite search exhausted 'ample.rewrite.maxSteps'. Increase the limit or supply an explicit context with 'using'. -/
#guard_msgs in
set_option ample.rewrite.maxSteps 0 in
example (n a b : Int) (hab : Congruent n a b) : Congruent n a a := by
  rw [hab]
  exact congruent_refl n _

elab "check_no_private_rewrite_hypotheses" : tactic => withMainContext do
  for declaration in ← getLCtx do
    if declaration.userName.toString.startsWith "_ample_rewrite_source" then
      throwError "A temporary relation proof leaked into the continuation."

example (n a b c : Int)
    (hab : Congruent n a b) (hac : Congruent n a c) : Congruent n b c := by
  rw [hab] at hab hac
  check_no_private_rewrite_hypotheses
  exact hac

elab "check_transform_runtime_restore" : tactic => do
  let before ← snapshot
  let exhausted ← tryCatchRuntimeEx
    (do
      Ample.Automation.runTransform do
        let (_, next) ← (← getMainGoal).note `temporary (mkConst ``True.intro)
        replaceMainGoal [next]
        Core.throwMaxHeartbeat `test `maxHeartbeats 1
      pure false)
    (fun error => pure error.isMaxHeartbeat)
  unless exhausted && (← snapshot) == before do
    throwError "A transformation did not restore state before propagating its runtime limit."

example : True ∧ True := by
  constructor
  check_transform_runtime_restore
  · trivial
  · trivial

def singletonSet {A : Type} (x : A) : Set A := fun y => y = x

example {A : Type} (S : Set A) (x : A) (hx : x ∈ S) : singletonSet x ⊆ S := by
  intro y hy
  rw [hy]
  exact hx

/--
error: Unknown identifier `missing_rewrite_proof`
---
error: unsolved goals
⊢ 0 = 0
-/
#guard_msgs in
example : (0 : Nat) = 0 := by
  rw [missing_rewrite_proof]

end RelationRewriteStateTests
