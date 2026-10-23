import Ample.Math.Numbers

open Ample Lean Meta Elab Tactic

namespace ArithmeticPreparationTests

private def snapshot : TacticM (List MVarId × Array (Expr × Array (FVarId × Expr))) := do
  let goals ← getGoals
  let mut data := #[]
  for g in goals do
    let context ← g.withContext do
      return (← getLCtx).foldl (init := #[]) fun a d => a.push (d.fvarId, d.type)
    data := data.push (← g.getType, context)
  return (goals, data)

@[irreducible] def sealed (x : Int) : Int := x
theorem sealed_spec (x : Int) : sealed x = x := by unfold sealed

elab "check_arith_restore" : tactic => do
  let before ← snapshot
  let failed ← tryCatchRuntimeEx
    (do evalTactic (← `(tactic| arith)); pure false)
    (fun _ => pure true)
  unless failed do throwError "Expected an arithmetic failure."
  unless (← snapshot) == before do throwError "Arithmetic failure changed the proof state."

example (n a b : Int) (h : Congruent n a b) : sealed a = a := by
  check_arith_restore
  exact sealed_spec a

example (n a b : Int) (h : Congruent n a b) :
    sealed a = a ∧ sealed b = b := by
  constructor
  check_arith_restore
  · exact sealed_spec a
  · exact sealed_spec b

elab "check_arith_outer_limit" : tactic => do
  let before ← snapshot
  let ctx ← readThe Core.Context
  let beats ← IO.getNumHeartbeats
  let error? ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => {c with maxHeartbeats := beats - ctx.initHeartbeats + 1}) do
      evalTactic (← `(tactic| arith))
      pure none)
    (fun e => pure (some e))
  unless error?.any (·.isMaxHeartbeat) do
    throwError "Arithmetic swallowed or replaced the user's overall heartbeat limit."
  unless (← snapshot) == before do throwError "User-limit failure changed the proof state."

example (n a b : Int) (h : Congruent n a b) : sealed a = a := by
  check_arith_outer_limit
  exact sealed_spec a

elab "check_arith_recursion_limit" : tactic => do
  let before ← snapshot
  let (failed, option, limit) ← withOptions (fun o => o.set `maxRecDepth (4 : Nat)) do
    let failed ← tryCatchRuntimeEx
      (do evalTactic (← `(tactic| arith)); pure false)
      (fun _ => pure true)
    return (failed, maxRecDepth.get (← getOptions), (← readThe Core.Context).maxRecDepth)
  unless failed && option == 4 && limit == 4 do
    throwError "Arithmetic raised or reset the user's recursion limit."
  unless (← snapshot) == before do throwError "Recursion-limit failure changed the proof state."

example (n a b : Int) (h : Congruent n a b) : sealed a = a := by
  check_arith_recursion_limit
  exact sealed_spec a

def Initial (n : Int) : Prop := n = 0 ∧ True
def Middle (n : Int) : Prop := n = 0
def Final (n : Int) : Prop := 0 = n

theorem first (n : Int) (h : Initial n) : Middle n := h.left
theorem firstDuplicate (n : Int) (h : Initial n) : Middle n := h.left
theorem second (n : Int) (h : Middle n) : Final n := h.symm

section
attribute [local ample_arith_prepare] first firstDuplicate second

elab "check_one_preparation" : tactic => do
  replaceMainGoal [← Ample.Automation.prepareArithmeticFacts (← getMainGoal)]
  withMainContext do
    let mut middle := 0
    for d in ← getLCtx do
      if d.type.isAppOf ``Middle then middle := middle + 1
      if d.type.isAppOf ``Final then throwError "New facts were recursively prepared."
    unless middle == 1 do throwError "Duplicate or irrelevant arithmetic facts were retained."

example (n m : Int) (hn : Initial n) (hm : Initial m) : n = 0 := by
  check_one_preparation
  exact hn.left

example (n : Int) (hn : Initial n) : n = 0 := by
  check_one_preparation
  exact hn.left

end

elab "check_preparation_noise" : tactic => do
  let mut goal ← getMainGoal
  for i in [:100] do
    let proof ← mkAppM ``Ample.congruent_refl #[mkIntLit 7, mkIntLit (Int.ofNat i)]
    let (_, next) ← goal.note (← mkFreshUserName `noise) proof
    goal := next
  replaceMainGoal [goal]
  let before ← goal.withContext getPropHyps
  let prepared ← Ample.Automation.prepareArithmeticFacts goal
  let after ← prepared.withContext getPropHyps
  unless after.size == before.size + 3 do
    throwError "Irrelevant hypotheses consumed the fact budget or useful facts were lost."
  replaceMainGoal [prepared]

example (a b : Int) (hab : Congruent 7 a b) : a % 7 = b % 7 := by
  check_preparation_noise
  arith

elab "check_no_preparation" : tactic => do
  let before ← snapshot
  let goal ← getMainGoal
  let next ← withOptions (fun o => o.set `ample.arith.maxPreparedFacts (0 : Nat)) do
    Ample.Automation.prepareArithmeticFacts goal
  unless next == goal && (← snapshot) == before do
    throwError "A zero preparation budget changed the proof state."

example (a b : Int) (hab : Congruent 7 a b) : a % 7 = b % 7 := by
  check_no_preparation
  exact congruent_emod_eq 7 a b hab

-- With a fixed modulus, the middle link shares no endpoint with the goal.
example (a b c d : Int)
    (hab : Congruent 7 a b) (hbd : Congruent 7 b d)
    (hdc : Congruent 7 d c) : Congruent 7 a c := by
  arith

end ArithmeticPreparationTests

-- Run with an independent cancellation token so the test does not cancel its
-- enclosing compilation. Invoke arith directly to exercise its own handlers.
open Lean.Elab.Command in
run_cmd do
  let token ← IO.CancelToken.new
  let started ← IO.mkRef false
  let action : CoreM Unit := MetaM.run' <| Term.TermElabM.run' do
    let goal ← mkFreshExprMVar (mkConst ``False)
    let tacticSyntax ← `(tactic| arith)
    let _ ← Tactic.run goal.mvarId! do
      started.set true
      token.set
      Ample.evalAmpleArith tacticSyntax
    pure ()
  let context ← liftCoreM (read : CoreM Core.Context)
  let state ← liftCoreM (get : CoreM Core.State)
  let result ← (action.run { context with cancelTk? := some token } state).toBaseIO
  unless ← started.get do throwError "The cancellation test did not invoke arithmetic."
  match result with
  | .error error => unless error.isInterrupt do throwError "Arithmetic replaced an interrupt with another error."
  | .ok _ => throwError "Arithmetic swallowed a cancellation request."
