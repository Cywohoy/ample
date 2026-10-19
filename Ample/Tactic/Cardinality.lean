import Ample.Tactic.Arithmetic
import Lean.Elab.Tactic.SolveByElim
import Lean.Meta.Tactic.Assert

open Lean Meta Elab Tactic

namespace Ample

/-- `card` proves cardinality goals using local hypotheses and lemmas registered in `ample_card_rules`.
It connects cardinal equalities, inequalities, finiteness, infinitude, and finite cardinalities; it does not construct new bijections.
Enable `set_option trace.Ample.card true` to inspect the registered lemmas and hypotheses used. -/
scoped syntax (name := ampleCard) "card" : tactic

private structure ComparisonFact where
  lhs : Expr
  rhs : Expr
  proof : Expr

private def addEquality (facts : Array ComparisonFact)
    (proof : Expr) : MetaM (Array ComparisonFact) := do
  let type ← withDefault <| whnf (← inferType proof)
  let some (_, a, b) := type.eq? | return facts
  let a ← withDefault <| whnf (← instantiateMVars a)
  let b ← withDefault <| whnf (← instantiateMVars b)
  if a.hasExprMVar || b.hasExprMVar then return facts
  for fact in facts do
    if (← isDefEq fact.lhs a) && (← isDefEq fact.rhs b) then return facts
  return facts.push ⟨a, b, proof⟩

private def addBound (facts : Array ComparisonFact) (proof : Expr) :
    MetaM (Array ComparisonFact) := do
  let type ← instantiateMVars (← inferType proof)
  unless type.isAppOfArity ``LE.le 4 do return facts
  unless ← isDefEq (type.getArg! 0) (mkConst `Ample.Cardinal) do return facts
  let a ← withDefault <| whnf (type.getArg! 2)
  let b ← withDefault <| whnf (type.getArg! 3)
  if a.hasExprMVar || b.hasExprMVar then return facts
  for fact in facts do
    if (← isDefEq fact.lhs a) && (← isDefEq fact.rhs b) then return facts
  return facts.push ⟨a, b, proof⟩

-- Connect facts with known endpoints before doing goal-directed search.
-- Backward applications of transitivity otherwise invent unknown intermediate types.
private def prepareComparisons (goal : MVarId) (rules : Array Name) : MetaM MVarId :=
    goal.withContext do
  unless (← getEnv).contains `Ample.Cardinal do return goal
  let mut equalities := #[]
  let mut bounds := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let proof := decl.toExpr
    let type ← instantiateMVars decl.type
    if type.isAppOfArity `Ample.SameCardinality 2 &&
        rules.contains `Ample.cardinal_eq_of_sameCardinality then
      let converted ← mkAppM `Ample.cardinal_eq_of_sameCardinality #[proof]
      equalities ← addEquality equalities converted
    else
      let type ← withDefault <| whnf type
      if let some (ty, _, _) := type.eq? then
        if ← isDefEq ty (mkConst `Ample.Cardinal) then
          equalities ← addEquality equalities proof
    bounds ← addBound bounds proof
  if rules.contains `Ample.Cardinal.eq_symm then
    for fact in equalities do
      equalities ← addEquality equalities (← mkEqSymm fact.proof)
  if rules.contains `Ample.Cardinal.eq_trans then
    for _ in [:equalities.size + 1] do
      let before := equalities.size
      for first in equalities do
        for second in equalities do
          if equalities.size ≥ 256 then break
          if ← isDefEq first.rhs second.lhs then
            equalities ← addEquality equalities
              (← mkEqTrans first.proof second.proof)
      if equalities.size == before then break
  if rules.contains `Ample.Cardinal.le_of_eq then
    for fact in equalities do
      let saved ← saveState
      try
        bounds ← addBound bounds (← mkAppM `Ample.Cardinal.le_of_eq #[fact.proof])
      catch _ => saved.restore
  if rules.contains `Ample.Cardinal.le_trans then
    for _ in [:bounds.size + 1] do
      let before := bounds.size
      for first in bounds do
        for second in bounds do
          if bounds.size ≥ 256 then break
          if ← isDefEq first.rhs second.lhs then
            let saved ← saveState
            try
              let proof ← mkAppM `Ample.Cardinal.le_trans #[first.proof, second.proof]
              bounds ← addBound bounds proof
            catch _ => saved.restore
      if bounds.size == before then break
  let mut goal := goal
  for fact in equalities ++ bounds do
    if !fact.proof.isFVar then
      let (_, next) ← goal.note (← mkFreshUserName `card_fact) fact.proof
      goal := next
  if rules.contains `Ample.sameCardinality_of_cardinal_eq then
    let target ← instantiateMVars (← goal.getType)
    if target.isAppOfArity `Ample.SameCardinality 2 then
      let [next] ← goal.apply (← mkConstWithFreshMVarLevels
        `Ample.sameCardinality_of_cardinal_eq) | return goal
      return next
  return goal

private def forwardRule (name : Name) : Bool :=
  #[`Ample.sameCardinality_symm, `Ample.sameCardinality_trans,
    `Ample.sameCardinality_of_cardinal_eq,
    `Ample.Cardinal.eq_symm, `Ample.Cardinal.eq_trans,
    `Ample.Cardinal.le_trans].contains name

/-- Use registered cardinality facts and local hypotheses. -/
@[tactic ampleCard]
def evalAmpleCard : Tactic := fun _ => do
  let saved ← saveState
  let original ← getMainGoal
  try
    Automation.normalizeGoals
    let rules ← labelled `ample_card_rules
    replaceMainGoal [← prepareComparisons (← getMainGoal) rules]
    let terms ← (rules.filter fun name => !forwardRule name).mapM fun name =>
      `(Lean.Parser.Tactic.SolveByElim.arg| $(mkIdent name):term)
    evalTactic (← `(tactic| first
      | assumption
      | rfl
      | solve_by_elim (maxDepth := 6) only [*, $terms,*]))
    Automation.traceCompletedProof `Ample.card original rules
      "Equality reasoning using the registered cardinality facts."
  catch error =>
    saved.restore
    throwError "Unable to solve the goal using the registered cardinality facts. Supply the needed size relation or construct an explicit injection or bijection.\n{error.toMessageData}"

end Ample
