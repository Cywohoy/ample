import Lean.Meta.Transform
import Lean.Meta.Tactic.Assumption
import Ample.Tactic.Step

/-! Apply an explicitly supplied, nondependent function to an equality.
No mathematical comparison registry or theorem simplifier is consulted. -/

open Lean Meta Elab Tactic

namespace Ample.Automation.ApplyFun

-- Project a known field without unfolding the mathematical expression stored in it.
private partial def projectHead (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if let .letE _ _ value body _ := e then
    return ← projectHead (body.instantiate1 value)
  let projection? ← if let .proj _ index owner := e then
      pure (some (owner, index, #[]))
    else if let .const name _ := e.getAppFn then do
      if let some info := (← getEnv).getProjectionFnInfo? name then
        if !info.fromClass && e.getAppNumArgs > info.numParams then
          pure (some (e.getAppArgs[info.numParams]!, info.i,
            e.getAppArgs[(info.numParams + 1)...*].toArray))
        else pure none
      else pure none
    else pure none
  if let some (owner, index, args) := projection? then
    if let some field ← withDefault <| project? owner index then
      let result := (mkAppN field args).headBeta
      if result != e then return ← projectHead result
  return e

private def compute (e : Expr) : MetaM Expr := do
  let (result, _) ← Meta.transformWithCache e {}
    (pre := fun e => do
      if ← isProof e then return .done e
      let result ← projectHead e
      return if result == e then .continue else .visit result)
    (skipConstInApp := true) (skipInstances := true)
  return result

private def imageEquality (f lhs rhs : Expr) : MetaM Expr := do
  mkEq (← compute (mkApp f lhs)) (← compute (mkApp f rhs))

private def elaborateFunction (functionSyntax : Term) (domain : Expr) : TacticM Expr := do
  let codomain ← mkFreshExprMVar (mkSort (← mkFreshLevelMVar))
  let expected ← mkArrow domain codomain
  let f ← Term.elabTermEnsuringType functionSyntax expected
  Term.synthesizeSyntheticMVarsNoPostponing
  let f ← instantiateMVars f
  let type ← instantiateMVars (← inferType f)
  if f.hasExprMVar || type.hasExprMVar then
    throwErrorAt functionSyntax "The supplied function has unresolved arguments. Specify its function and types."
  return f

private def injectivityType (domain f : Expr) : MetaM Expr :=
  withLocalDeclD `x domain fun x =>
    withLocalDeclD `y domain fun y => do
      let premise ← mkEq (mkApp f x) (mkApp f y)
      mkForallFVars #[x, y] (← mkArrow premise (← mkEq x y))

def atHypothesis (function : Term) (hyp : FVarId) (name? : Option Name) :
    TacticM Unit := withMainContext do
  let declaration ← hyp.getDecl
  let type ← withReducible <| whnf (← instantiateMVars declaration.type)
  let some (domain, lhs, rhs) := type.eq?
    | throwError "apply_fun expects an equality hypothesis."
  let f ← elaborateFunction function domain
  let proof ← mkAppM ``congrArg #[f, mkFVar hyp]
  let result ← imageEquality f lhs rhs
  let (_, next) ← (← getMainGoal).note (name?.getD declaration.userName) proof result
  -- Dependencies on the old equality may require retaining it internally.
  let next ← if name?.isSome then pure next else next.tryClear hyp
  replaceMainGoal [next]

def atGoal (function : Term) (using? : Option Term) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let type ← withReducible <| whnf (← instantiateMVars (← goal.getType))
  let some (domain, lhs, rhs) := type.eq?
    | throwError "apply_fun expects an equality goal."
  let f ← elaborateFunction function domain
  let law ← injectivityType domain f
  let (injective, obligations) : Expr × List MVarId ← if let some lawSyntax := using? then do
      let proof ← Term.elabTermEnsuringType lawSyntax law
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (← instantiateMVars proof, [])
    else do
      let proof ← mkFreshExprSyntheticOpaqueMVar law ((← goal.getTag).append `injective)
      let solved ← proof.mvarId!.assumptionCore
      pure (proof, if solved then [] else [proof.mvarId!])
  let image ← mkFreshExprSyntheticOpaqueMVar (← imageEquality f lhs rhs) (← goal.getTag)
  goal.assign (mkAppN injective #[lhs, rhs, image])
  replaceMainGoal (image.mvarId! :: obligations)

end Ample.Automation.ApplyFun

namespace Ample

/-- Apply the supplied function to both sides of an equality.

`apply_fun (fun x => x + 1) at h` replaces `h : a = b` with
`h : a + 1 = b + 1`. `with result` retains `h` and names the new equality.
Function application, local let expressions, and projections of known constructors
are computed; mathematical definitions and registered comparison rules are not expanded.

On an equality goal `a = b`, `apply_fun f` produces `f a = f b` and an
injectivity obligation `forall x y, f x = f y -> x = y`. A matching local
injectivity proof is reused, or supply it with `apply_fun f using hf`.
Without a supplied proof, the image equality precedes the injectivity goal.
`with` is available only when selecting a hypothesis with `at`.

The selected transformation result receives Ample's restricted reflexivity check;
unrelated pending goals are preserved. Inequalities and dependent functions are not supported. -/
scoped syntax (name := ampleApplyFun)
  "apply_fun " term:max (" at " ident)? (" using " term)? (" with " ident)? : tactic

@[tactic ampleApplyFun]
def evalAmpleApplyFun : Tactic := fun stx => Automation.runTransform do
  let `(tactic| apply_fun $f $[at $hyp]? $[using $law]? $[with $result]?) := stx
    | throwUnsupportedSyntax
  if let some hyp := hyp then
    if law.isSome then throwError "The 'using' clause is only supported on an equality goal."
    Automation.ApplyFun.atHypothesis f (← getFVarId hyp) (result.map (·.getId))
  else
    if result.isSome then throwError "Use 'at h with name' to name a derived equality."
    Automation.ApplyFun.atGoal f law

end Ample
