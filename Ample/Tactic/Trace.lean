import Lean.Elab.Tactic
import Lean.Util.Trace

open Lean Meta Elab Tactic

initialize registerTraceClass `Ample.arith
initialize registerTraceClass `Ample.card
initialize registerTraceClass `Ample.group

namespace Ample.Automation

private partial def inspectProof (category : Name) (rules : Array Name)
    (locals : Array FVarId) (used : IO.Ref (Array Name))
    (facts : IO.Ref (Array FVarId)) (e : Expr) : TacticM Unit := do
  if let .const name _ := e.getAppFn then
    if rules.contains name && !(← used.get).contains name then
      used.modify (·.push name)
      let publicName := (privateToUserName? name).getD name
      let displayName := match publicName with
        | `Ample.calc_assoc => `Ample.Group.assoc
        | `Ample.calc_id_left => `Ample.Group.id_left
        | `Ample.calc_id_right => `Ample.Group.id_right
        | `Ample.calc_inv_left => `Ample.Group.inv_left
        | `Ample.calc_inv_right => `Ample.Group.inv_right
        | other => other
      addTrace category m!"Rule: {displayName}"
      let mut count := 0
      for arg in e.getAppArgs do
        if count < 6 && (← isProof arg) then
          addTrace category m!"  condition: {← inferType arg}"
          count := count + 1
  match e with
  | .lam name type body bi =>
    withLocalDecl name bi type fun x =>
      inspectProof category rules locals used facts (body.instantiate1 x)
  | .letE _ _ value body _ =>
    inspectProof category rules locals used facts value
    inspectProof category rules locals used facts (body.instantiate1 value)
  | .app fn arg =>
    inspectProof category rules locals used facts fn
    inspectProof category rules locals used facts arg
  | .mdata _ body | .proj _ _ body =>
    inspectProof category rules locals used facts body
  | .fvar id =>
    if locals.contains id && !(← facts.get).contains id then
      let decl ← id.getDecl
      if !decl.isImplementationDetail && (← isProp decl.type) then
        facts.modify (·.push id)
  | _ => pure ()

/-- Report only applications in the completed proof, never abandoned search branches. -/
def traceCompletedProof (category : Name) (goal : MVarId)
    (rules : Array Name) (calculation : String) : TacticM Unit := do
  unless ← isTracingEnabledFor category do return
  goal.withContext do
    let proof ← instantiateMVars (mkMVar goal)
    if proof.hasExprMVar then return
    addTrace category m!"Proved: {← goal.getType}"
    let used ← IO.mkRef (#[] : Array Name)
    let facts ← IO.mkRef (#[] : Array FVarId)
    inspectProof category rules (← getLCtx).getFVarIds used facts proof
    if (← used.get).isEmpty then
      addTrace category m!"Method: {calculation}"
    for id in (← facts.get).toList.take 8 do
      let decl ← id.getDecl
      addTrace category m!"Hypothesis: {decl.userName} : {decl.type}"

end Ample.Automation
