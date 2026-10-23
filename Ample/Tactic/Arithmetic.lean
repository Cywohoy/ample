import Ample.Tactic.Normalize
import Ample.Tactic.ArithmeticRules
import Ample.Tactic.ArithmeticSearch
import Ample.Tactic.ArithmeticFacts
import Ample.Tactic.Trace
import Ample.Tactic.Unfold
import Ample.Tactic.Injection
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Grind

/-!
Arithmetic automation for natural numbers and integers.
Opening `Ample` enables `arith` and the compatibility wrapper for `omega`.
Arithmetic lemmas are registered in `ArithmeticRules.lean`; `suffices` uses Lean's standard explicit proof syntax.
-/

open Lean Elab Tactic

namespace Ample

@[inherit_doc Lean.Parser.Tactic.omega]
scoped syntax (name := arithmeticOmega) (priority := high)
    "omega" Lean.Parser.Tactic.optConfig : tactic

@[tactic arithmeticOmega]
def evalArithmeticOmega : Tactic := fun stx => do
  let _ ← getMainGoal
  -- Normalize goals and hypotheses using the shared presentation rules.
  Automation.normalizeGoals
  -- Use the imported domain's rules rather than naming particular example sets.
  evalTactic (← `(tactic| try dsimp only [ample_arith_simp] at *))
  unless (← getGoals).isEmpty do
    -- Call the native elaborator directly to avoid invoking this wrapper again.
    let coreSyntax := Syntax.node stx.getHeadInfo
      ``Lean.Parser.Tactic.omega stx.getArgs
    Lean.Elab.Tactic.Omega.evalOmega coreSyntax

/-- `arith` proves goals about natural numbers and integers using local hypotheses and registered arithmetic rules.
It supports linear arithmetic, polynomial identities, product bounds, division, remainders, divisibility, and `Fin` bounds.
Imported domain rules also support integer congruence: ring operations, natural powers, divisibility, and remainder bridges.
Required sign and range conditions must be available or derivable. Group laws are not included.

For example, it proves `2 * n ≠ 5` for `n : Int`.
Enable `set_option trace.Ample.arith true` to inspect the rules and conditions used in a completed proof. -/
scoped syntax (name := ampleArith) "arith" : tactic

/-- Check linear arithmetic, polynomial identities, and basic division and remainder calculations. -/
private def runAmpleArith : TacticM Unit := do
  let _ ← getMainGoal
  Automation.normalizeGoals
  let simpRules := mkIdent `ample_arith_simp
  let grindRules := mkIdent `ample_arith_grind
  withOptions (fun opts => opts.setBool `linter.unusedSimpArgs false) do
    if ← Automation.searchArithmetic (← getMainGoal) then
      replaceMainGoal []
      return
    -- Use local hypotheses without importing unrestricted grind rules from other domains.
    evalTactic (← `(tactic| solve
    | (simp (disch := omega) only [$simpRules:ident] at *
       all_goals (first | omega | grind only [$grindRules:ident]))
    | grind only [$grindRules:ident]))

-- Stage limits count allocations without resetting Lean's overall heartbeat
-- budget. Only exhaustion of our own smaller limit is recoverable here.
private def tryArithmeticStage (budget : Nat) (prepare : Bool) : TacticM Bool := do
  let saved ← saveState
  let ctx ← readThe Core.Context
  let start ← IO.getNumHeartbeats
  let localLimit := start - ctx.initHeartbeats + budget
  let ownLimit := ctx.maxHeartbeats == 0 || localLimit < ctx.maxHeartbeats
  let limit := if ownLimit then localLimit else ctx.maxHeartbeats
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := limit }) do
      if prepare then replaceMainGoal [← Automation.prepareArithmeticFacts (← getMainGoal)]
      runAmpleArith
      return true)
    (fun e => do
      saved.restore
      if e.isRuntime && !(e.isMaxHeartbeat && ownLimit) then throw e
      -- Even if our smaller limit fired, a concurrently exhausted outer budget
      -- must remain visible to the caller.
      if e.isMaxHeartbeat && ctx.maxHeartbeats != 0 &&
          (← IO.getNumHeartbeats) - ctx.initHeartbeats >= ctx.maxHeartbeats then throw e
      return false)

@[tactic ampleArith]
def evalAmpleArith : Tactic := fun _ => do
  let saved ← saveState
  let goal ← getMainGoal
  tryCatchRuntimeEx (do
    Automation.validateArithmeticPreparationRules
    if ← Automation.closeByArithmeticBridge goal then replaceMainGoal []
    else if (← labelled `ample_arith_prepare).isEmpty then runAmpleArith
    else unless ← tryArithmeticStage 2000000 false do
      unless ← tryArithmeticStage 6000000 true do
        throwError "No arithmetic derivation was found within the staged search limits."
    Automation.traceCompletedProof `Ample.arith goal
      (← labelled `ample_arith_apply)
      "Arithmetic calculation using the registered rules and local hypotheses.")
    (fun e => do
    saved.restore
    if e.isRuntime then throw e
    throwError "Arithmetic could not close the goal. Check the required bounds, signs, and nonzero conditions; then use an explicit intermediate statement if needed.\n{e.toMessageData}")

end Ample
