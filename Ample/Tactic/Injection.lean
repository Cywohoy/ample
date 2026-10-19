import Lean.Elab.Tactic.Injection
import Lean.Meta.Tactic.Assert

/-!
Add component equalities while retaining the original equality and intermediate steps.
Pairs, Fin values, and subtypes can be compared even when given as variables.
Other constructors use Lean's native injection machinery.
-/

open Lean Meta Elab Tactic

namespace Course.Automation

inductive RetainedInjectionResult where
  | unchanged
  | solved
  | subgoal (goal : MVarId) (equalities : Array FVarId) (remainingNames : List Name)

private def alreadyKnown (goal : MVarId) (type : Expr) : MetaM Bool := goal.withContext do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      try
        if ← withNewMCtxDepth <| isDefEq decl.type type then return true
      catch _ => pure ()
  return false

private def projectEquality (type : Expr) (proof : Expr) (projection : Name) :
    MetaM (Expr × Expr) := do
  let some (α, lhs, rhs) := type.eq?
    | throwError "Expected an equality."
  withLocalDeclD `x α fun x => do
    let value ← mkAppM projection #[x]
    let map ← mkLambdaFVars #[x] value
    let result ← mkCongrArg map proof
    let calculate (arg : Expr) : MetaM Expr := do
      let application ← mkAppM projection #[arg]
      let head ← withDefault <| whnf arg
      if (← isConstructorApp'? head).isSome then
        withDefault <| whnf application
      else
        pure application
    let left ← calculate lhs
    let right ← calculate rhs
    return (result, ← mkEq left right)

def retainedInjection (goal : MVarId) (hyp : FVarId) (names : List Name := [])
    (deduplicate := false) : MetaM RetainedInjectionResult := goal.withContext do
  let decl ← hyp.getDecl
  let type ← whnf (← instantiateMVars decl.type)
  let projections ← match type.eq? with
    | some (α, _, _) => do
      let α ← whnf α
      if α.isAppOfArity ``Prod 2 then pure [``Prod.fst, ``Prod.snd]
      else if α.isAppOfArity ``Fin 1 then pure [``Fin.val]
      else if α.isAppOfArity ``Subtype 2 then pure [``Subtype.val]
      else pure []
    | none => pure []
  if !projections.isEmpty then
    let mut current := goal
    let mut added := #[]
    let mut remaining := names
    for projection in projections do
      let (proof, newType) ← projectEquality type (mkFVar hyp) projection
      if deduplicate && (← alreadyKnown current newType) then continue
      let (name, rest) ← match remaining with
        | name :: rest => pure (name, rest)
        | [] => do
          let suffix := "_" ++ projection.getString!
          pure (← mkFreshUserName (decl.userName.appendAfter suffix), [])
      let (id, next) ← current.note name proof newType
      current := next
      added := added.push id
      remaining := rest
    if added.isEmpty then return .unchanged
    return .subgoal current added remaining
  -- Give the native tactic a copy so that the original hypothesis is retained.
  let saved ← saveState
  try
    let (copy, next) ← goal.note (← mkFreshUserName `__course_injection_copy) (mkFVar hyp)
    match ← Meta.injection next copy names with
    | .solved => return .solved
    | .subgoal next eqs rest =>
      if deduplicate then
        let mut hasNew := false
        for id in eqs do
          let newType ← next.withContext <| id.getType
          unless ← alreadyKnown goal newType do hasNew := true
        unless hasNew do
          saved.restore
          return .unchanged
      return .subgoal next eqs rest
  catch _ =>
    saved.restore
    return .unchanged

def retainedInjections (goal : MVarId) (names : List Name := []) :
    MetaM RetainedInjectionResult := do
  let roots ← goal.withContext getPropHyps
  let mut queue := roots.map fun id => (id, 0)
  let mut current := goal
  let mut remaining := names
  let mut processed : Std.HashSet FVarId := {}
  let mut cursor := 0
  let mut count := 0
  while cursor < queue.size && count < 128 do
    let (hyp, depth) := queue[cursor]!
    cursor := cursor + 1
    if processed.contains hyp || depth >= 8 then continue
    processed := processed.insert hyp
    match ← retainedInjection current hyp remaining (deduplicate := true) with
    | .unchanged => pure ()
    | .solved => return .solved
    | .subgoal next eqs rest =>
      current := next
      remaining := rest
      count := count + eqs.size
      queue := queue ++ eqs.map fun id => (id, depth + 1)
  return .subgoal current #[] remaining

end Course.Automation

namespace Course

@[inherit_doc Lean.Parser.Tactic.injection]
scoped syntax (name := courseInjection) (priority := high)
    "injection " term (" with" (ppSpace colGt (ident <|> hole))+)? : tactic

@[inherit_doc Lean.Parser.Tactic.injections]
scoped syntax (name := courseInjections) (priority := high)
    "injections" (ppSpace colGt (ident <|> hole))* : tactic

@[tactic courseInjection]
def evalRetainedInjection : Tactic := fun stx => withMainContext do
  let hyp ← elabAsFVar stx[1]
  let names := if stx[2].isNone then [] else stx[2][1].getArgs.toList.map getNameOfIdent'
  match ← Automation.retainedInjection (← getMainGoal) hyp names with
  | .unchanged => throwError "No structural equality could be extracted from this hypothesis."
  | .solved => replaceMainGoal []
  | .subgoal goal _ remaining =>
    unless remaining.isEmpty do throwError "Too many names supplied to injection."
    if ← goal.withContext goal.assumptionCore then replaceMainGoal []
    else replaceMainGoal [goal]

@[tactic courseInjections]
def evalRetainedInjections : Tactic := fun stx => do
  let names := stx[1].getArgs.toList.map getNameOfIdent'
  match ← Automation.retainedInjections (← getMainGoal) names with
  | .unchanged => pure ()
  | .solved => replaceMainGoal []
  | .subgoal goal _ remaining =>
    unless remaining.isEmpty do throwError "Too many names supplied to injections."
    if ← goal.withContext goal.assumptionCore then replaceMainGoal []
    else replaceMainGoal [goal]

end Course
