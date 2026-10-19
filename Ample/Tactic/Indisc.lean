import Lean.Elab.Tactic.Ext
import Lean.Elab.Tactic.Congr
import Ample.Tactic.Injection
import Ample.Tactic.Rule
import Ample.Tactic.Step
import Ample.Tactic.Comparison

open Lean Meta Elab Tactic

namespace Ample.Automation

-- Construct the reflexive comparison without using the forward extensionality theorem.
private partial def reflexiveComparison (type : Expr) : MetaM Expr := do
  let type ← withReducible <| whnf type
  if let .forallE name domain body bi := type then
    return ← withLocalDecl name bi domain fun x => do
      mkLambdaFVars #[x] (← reflexiveComparison (body.instantiate1 x))
  if type.isAppOfArity ``And 2 then
    return ← mkAppM ``And.intro #[← reflexiveComparison type.getAppArgs[0]!,
      ← reflexiveComparison type.getAppArgs[1]!]
  if let some (_, lhs, _) := type.eq? then
    let proof ← mkEqRefl lhs
    unless ← isDefEq (← inferType proof) type do failure
    return proof
  if type.isAppOfArity ``HEq 4 then
    let proof ← mkAppM ``HEq.refl #[type.getAppArgs[1]!]
    unless ← isDefEq (← inferType proof) type do failure
    return proof
  if type.isAppOfArity ``Iff 2 then
    let proof ← mkAppM ``Iff.rfl #[type.getAppArgs[0]!]
    unless ← isDefEq (← inferType proof) type do failure
    return proof
  if type.isConstOf ``True then return mkConst ``True.intro
  throwError "Cannot construct the reflexive comparison."

private def inverseExtComparison? (type proof : Expr) : TacticM (Option (Expr × Expr)) := do
  let some (α, lhs, rhs) := type.eq? | return none
  let reduced ← withDefault <| whnf α
  let candidates := (← Lean.Meta.Ext.getExtTheorems α) ++
    (← Lean.Meta.Ext.getExtTheorems reduced)
  for lemma in candidates do
    let iffName := lemma.declName.appendAfter "_iff"
    unless (← getEnv).contains iffName do continue
    let saved ← saveState
    try
      let result ← withLocalDeclD `other α fun other => do
        let constant ← mkConstWithFreshMVarLevels iffName
        let (_, _, iffType) ← forallMetaTelescopeReducing (← inferType constant)
        unless iffType.isAppOfArity ``Iff 2 do failure
        unless ← isDefEq iffType.getAppArgs[0]! (← mkEq lhs other) do failure
        let condition ← instantiateMVars iffType.getAppArgs[1]!
        if condition.hasExprMVar then failure
        let motive ← mkLambdaFVars #[other] condition
        let reflexive ← reflexiveComparison (mkApp motive lhs).headBeta
        let transport ← mkCongrArg motive proof
        let result ← mkAppM ``Eq.mp #[transport, reflexive]
        return (result, (mkApp motive rhs).headBeta)
      return some result
    catch _ => saved.restore
  return none

private def primitiveComparison? (type proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (α, lhs, rhs) := type.eq? | return none
  if (← withDefault <| whnf α) == mkSort .zero then
    let result ← mkAppM ``Iff.of_eq #[proof]
    return some (result, mkApp2 (mkConst ``Iff) lhs rhs)
  -- Keep membership notation when a set is compared at an element.
  if α.isAppOfArity `Ample.Set 1 then
    return ← withLocalDeclD `x α.getAppArgs[0]! fun x => do
      let result ← mkAppM ``Iff.of_eq #[← mkAppM ``congrFun #[proof, x]]
      let left ← mkAppM ``Membership.mem #[lhs, x]
      let right ← mkAppM ``Membership.mem #[rhs, x]
      let condition := mkApp2 (mkConst ``Iff) left right
      return some (← mkLambdaFVars #[x] result, ← mkForallFVars #[x] condition)
  return none

private def quotientComparison? (type proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_, lhs, rhs) := type.eq? | return none
  let left ← withDefault <| whnf lhs
  let right ← withDefault <| whnf rhs
  unless left.isAppOfArity ``Quot.mk 3 && right.isAppOfArity ``Quot.mk 3 do return none
  let result ← mkAppM ``Quotient.exact #[proof]
  let resultType ← instantiateMVars (← inferType result)
  let head ← withReducible <| whnf resultType
  unless head.isAppOfArity ``Setoid.r 4 do return some (result, resultType)
  let args := head.getAppArgs
  let bundle ← withDefault <| whnf args[1]!
  unless bundle.isAppOfArity ``Setoid.mk 3 do return some (result, resultType)
  return some (result, mkApp2 bundle.getAppArgs[1]! args[2]! args[3]!)

private def registeredEvidence? (type proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (lemma, condition) ← registeredComparison? type | return none
  return some (← mkAppM ``Iff.mp #[lemma, proof], condition)

private def specializeComparison (proof type : Expr) (args : Array Syntax) :
    TacticM (Expr × Expr) := do
  let mut proof := proof
  let mut type := type
  for arg in args do
    let reduced ← withReducible <| whnf type
    if let .forallE _ domain body _ := reduced then
      let value ← Term.elabTermEnsuringType arg domain
      proof := mkApp proof value
      type := body.instantiate1 value
    else if let some (α, _, _) := reduced.eq? then
      let .forallE _ domain _ _ ← withReducible <| whnf α
        | throwError "The comparison does not accept another argument."
      let value ← Term.elabTermEnsuringType arg domain
      proof ← mkAppM ``congrFun #[proof, value]
      type ← inferType proof
    else
      throwError "The comparison does not accept another argument."
  if let some (α, lhs, rhs) := type.eq? then
    if (← withReducible <| whnf α) == mkSort .zero then
      proof ← mkAppM ``Iff.of_eq #[proof]
      type := mkApp2 (mkConst ``Iff) lhs rhs
  return (proof, type)

private partial def propositionalComparison (proof type : Expr) : MetaM (Expr × Expr) := do
  if let .forallE name domain body bi := type.consumeMData then
    return ← withLocalDecl name bi domain fun x => do
      let (next, nextType) ← propositionalComparison (mkApp proof x) (body.instantiate1 x)
      return (← mkLambdaFVars #[x] next, ← mkForallFVars #[x] nextType)
  if let some (α, lhs, rhs) := type.eq? then
    if (← withDefault <| whnf α) == mkSort .zero then
      return (← mkAppM ``Iff.of_eq #[proof], mkApp2 (mkConst ``Iff) lhs rhs)
  return (proof, type)

private partial def computeProjection (e : Expr) : MetaM Expr := do
  let projection? ← if let .proj _ i owner := e then pure (some (owner, i, #[]))
    else if let .const name _ := e.getAppFn then do
      if let some info := (← getEnv).getProjectionFnInfo? name then
        if !info.fromClass && e.getAppNumArgs > info.numParams then
          pure (some (e.getAppArgs[info.numParams]!, info.i,
            e.getAppArgs[(info.numParams + 1)...*].toArray))
        else pure none
      else pure none
    else pure none
  if let some (owner, index, arguments) := projection? then
    if let some field ← withDefault <| project? owner index then
      -- Extract the field without reducing the arithmetic or predicate it contains.
      let result := (mkAppN field arguments).headBeta
      if result != e then return ← computeProjection result
  return e

private partial def computeComparison (type : Expr) : MetaM Expr := do
  if let some (_, lhs, rhs) := type.eq? then
    return ← mkEq (← computeProjection lhs) (← computeProjection rhs)
  if type.isAppOfArity ``And 2 then
    return mkApp2 (mkConst ``And) (← computeComparison type.getAppArgs[0]!)
      (← computeComparison type.getAppArgs[1]!)
  return type


private partial def splitComparisons (proof type : Expr) : MetaM (Array (Expr × Expr)) := do
  -- Split only conjunctions of comparison conditions; keep named relations intact.
  let type := type.consumeMData
  if type.isAppOfArity ``And 2 then
    return (← splitComparisons (← mkAppM ``And.left #[proof]) type.getAppArgs[0]!) ++
      (← splitComparisons (← mkAppM ``And.right #[proof]) type.getAppArgs[1]!)
  return #[(proof, ← computeComparison type)]

def indiscernHypothesis (goal : MVarId) (hyp : FVarId)
    (args : Array Syntax) (names : List Name) (deduplicate := false) :
    TacticM (List MVarId) := goal.withContext do
  let decl ← hyp.getDecl
  let type ← withReducible <| whnf (← instantiateMVars decl.type)
  let some (α, _, _) := type.eq? | throwError "Expected an equality hypothesis."
  if !args.isEmpty && !(← withDefault <| whnf α).isForall then
    throwError "Only function or predicate equalities accept observation arguments."
  let proof := mkFVar hyp
  let comparison ← registeredEvidence? type proof
  let comparison ← match comparison with
    | some value => pure (some value)
    | none => primitiveComparison? type proof
  let comparison ← match comparison with
    | some value => pure (some value)
    | none => quotientComparison? type proof
  let comparison ← match comparison with
    | some value => pure (some value)
    | none => inverseExtComparison? type proof
  if let some (proof, type) := comparison then
    let (proof, type) ← specializeComparison proof type args
    let (proof, type) ← propositionalComparison proof type
    if names.isEmpty && !deduplicate then
      let (_, next) ← goal.note decl.userName proof (← computeComparison type)
      return [← next.tryClear hyp]
    let facts ← splitComparisons proof type
    if names.length > facts.size then throwError "Too many names supplied to indiscern."
    let mut next := goal
    for i in [:facts.size] do
      let (proof, type) := facts[i]!
      if deduplicate then
        let known ← next.withContext do
          for decl in ← getLCtx do
            unless decl.isImplementationDetail do
              if ← withNewMCtxDepth <| isDefEq decl.type type then return true
          return false
        if known then continue
      let name ← if let some name := names[i]? then pure name
        else mkFreshUserName (decl.userName.appendAfter s!"_compare{i + 1}")
      let (_, updated) ← next.note name proof type
      next := updated
    return [next]
  unless args.isEmpty do throwError "No pointwise comparison rule is available."
  match ← retainedInjection goal hyp names deduplicate with
  | .unchanged => throwError "No comparison rule is available for this equality."
  | .solved => return []
  | .subgoal next equalities remaining =>
    unless remaining.isEmpty do throwError "Too many names supplied to indiscern."
    if names.isEmpty && !deduplicate && equalities.size == 1 then
      let proof := mkFVar equalities[0]!
      let type ← next.withContext <| inferType proof
      let (_, updated) ← next.note decl.userName proof type
      return [← updated.tryClear hyp]
    return [next]

def indiscernRecursively (goal : MVarId) (roots : Array FVarId) (args : Array Syntax) :
    TacticM (List MVarId) := do
  let mut current := goal
  let mut queue := roots.map (·, 0)
  let mut cursor := 0
  let mut count := 0
  while cursor < queue.size && count < 128 do
    let (hyp, depth) := queue[cursor]!
    cursor := cursor + 1
    if depth >= 8 then continue
    let saved ← saveState
    try
      let before ← current.withContext do pure (← getLCtx).getFVarIds
      let next ← indiscernHypothesis current hyp (if depth == 0 then args else #[]) [] true
      if next.isEmpty then return []
      current := next.head!
      let added ← current.withContext do
        pure ((← getLCtx).getFVarIds.filter fun id => !before.contains id)
      count := count + added.size
      queue := queue ++ added.map (·, depth + 1)
    catch _ => saved.restore
  return [current]

private def projectedObjects? (lhs rhs : Expr) : MetaM (Option (Expr × Expr)) := do
  if let .proj name index left := lhs then
    if let .proj name' index' right := rhs then
      if name == name' && index == index' then return some (left, right)
  let .const name _ := lhs.getAppFn | return none
  unless rhs.getAppFn.isConstOf name do return none
  let some info := (← getEnv).getProjectionFnInfo? name | return none
  let left := lhs.getAppArgs
  let right := rhs.getAppArgs
  if left.size > info.numParams && right.size > info.numParams then
    return some (left[info.numParams]!, right[info.numParams]!)
  return none

private partial def wholeEquality? (condition : Expr) : MetaM (Option Expr) := do
  let condition := condition.consumeMData
  if let .forallE name domain body bi := condition then
    return ← withLocalDecl name bi domain fun x => do
      let body := (body.instantiate1 x).consumeMData
      if body.isAppOfArity ``Iff 2 then
        let left := body.getAppArgs[0]!
        let right := body.getAppArgs[1]!
        if left.isAppOfArity ``Membership.mem 5 && right.isAppOfArity ``Membership.mem 5 then
          if left.getAppArgs[4]! == x && right.getAppArgs[4]! == x then
            return some (← mkEq left.getAppArgs[3]! right.getAppArgs[3]!)
      let sides ← if let some (_, lhs, rhs) := body.eq? then
        pure (some (lhs, rhs))
      else if body.isAppOfArity ``Iff 2 then
        pure (some (body.getAppArgs[0]!, body.getAppArgs[1]!))
      else do
        let some eq ← wholeEquality? body | return none
        let some (_, lhs, rhs) := eq.eq? | return none
        pure (some (lhs, rhs))
      let some (lhs, rhs) := sides | return none
      let left ← mkLambdaFVars #[x] lhs (etaReduce := true)
      let right ← mkLambdaFVars #[x] rhs (etaReduce := true)
      return some (← mkEq left right)
  if condition.isAppOfArity ``And 2 then return ← wholeEquality? condition.getAppArgs[0]!
  if condition.isAppOfArity ``Iff 2 then
    let lhs := condition.getAppArgs[0]!
    let rhs := condition.getAppArgs[1]!
    if lhs.isAppOfArity ``Membership.mem 5 && rhs.isAppOfArity ``Membership.mem 5 then
      if ← isDefEq lhs.getAppArgs[4]! rhs.getAppArgs[4]! then
        return some (← mkEq lhs.getAppArgs[3]! rhs.getAppArgs[3]!)
    return some (← mkEq lhs rhs)
  if let some (_, lhs, rhs) := condition.eq? then
    if let some (left, right) ← projectedObjects? lhs rhs then return some (← mkEq left right)
    if lhs.isApp && rhs.isApp then
      if ← isDefEq lhs.appArg! rhs.appArg! then
        return some (← mkEq lhs.appFn! rhs.appFn!)
      if ← isDefEq lhs.appFn! rhs.appFn! then
        return some (← mkEq lhs.appArg! rhs.appArg!)
  if condition.isAppOfArity ``Setoid.r 4 then
    let args := condition.getAppArgs
    let left ← mkAppM ``Quotient.mk #[args[1]!, args[2]!]
    let right ← mkAppM ``Quotient.mk #[args[1]!, args[3]!]
    return some (← mkEq left right)
  return none

private partial def flattenFacts (proof : Expr) : MetaM (Array Expr) := do
  let type ← inferType proof
  if type.isAppOfArity ``And 2 then
    return (← flattenFacts (← mkAppM ``And.left #[proof])) ++
      (← flattenFacts (← mkAppM ``And.right #[proof]))
  return #[proof]

private def forwardExtStep (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  if let some next ← registeredComparisonStep? goal then return next
  let type ← goal.getType
  if let some (_, lhs, rhs) := type.eq? then
    let left ← withDefault <| whnf lhs
    let right ← withDefault <| whnf rhs
    if left.isAppOfArity ``Quot.mk 3 && right.isAppOfArity ``Quot.mk 3 then
      return ← goal.apply (← mkConstWithFreshMVarLevels ``Quotient.sound)
  return ← Lean.Elab.Tactic.Ext.applyExtTheoremAt goal

private partial def solveComparison (goal : MVarId) (sources : Array Expr)
    (forwardExt : Bool) (depth : Nat := 12) : TacticM Unit := goal.withContext do
  for source in sources do
    let saved ← saveState
    try
      let next ← goal.apply source
      if next.isEmpty then return
      saved.restore
    catch _ => saved.restore
  if ← closeReflexive goal then return
  let type ← withReducible <| whnf (← goal.getType)
  if type.isForall then
    let (_, next) ← goal.intro1
    solveComparison next sources forwardExt depth
    return
  if type.isAppOfArity ``And 2 then
    for next in ← goal.apply (← mkConstWithFreshMVarLevels ``And.intro) do
      solveComparison next sources forwardExt depth
    return
  if type.isConstOf ``True then
    goal.assign (mkConst ``True.intro)
    return
  if depth == 0 then
    throwError "Comparison reached the specified depth. Increase ': n' or supply the intermediate comparison."
  if type.isAppOfArity ``Iff 2 then
    let saved ← saveState
    try
      for next in ← goal.apply (← mkConstWithFreshMVarLevels `Iff.of_eq) do
        solveComparison next sources forwardExt (depth - 1)
      return
    catch _ => saved.restore
  let saved ← saveState
  try
    let next ← if forwardExt then forwardExtStep goal else goal.congrN 1
    if next.isEmpty then return
    for child in next do solveComparison child sources forwardExt (depth - 1)
    return
  catch _ => saved.restore
  throwError "The supplied comparison does not establish this equality. For functions, provide equality at every input; for products, provide all required field equalities. Specify the intended whole equality after ':' if it cannot be inferred."

def recoverEquality (goal : MVarId) (hyp : FVarId) (target? : Option Syntax)
    (name? : Option Name) : TacticM (List MVarId) := goal.withContext do
  let decl ← hyp.getDecl
  let target ← if let some targetSyntax := target? then Term.elabTermEnsuringType targetSyntax (mkSort .zero)
    else do
      let some target ← wholeEquality? decl.type
        | throwError "Cannot infer the whole equality; specify it after ':'."
      pure target
  unless target.isAppOfArity ``Eq 3 do throwError "Expected an equality as the result type."
  let proof ← mkFreshExprSyntheticOpaqueMVar target
  solveComparison proof.mvarId! (← flattenFacts (mkFVar hyp)) true
  let proof ← instantiateMVars proof
  let (_, next) ← goal.note (name?.getD decl.userName) proof target
  return [← if name?.isSome then pure next else next.tryClear hyp]

def compareGoal (goal : MVarId) (target? : Option Syntax) : TacticM (List MVarId) := goal.withContext do
  let current ← goal.getType
  let target ← if let some targetSyntax := target? then Term.elabTermEnsuringType targetSyntax (mkSort .zero)
    else do
      let some target ← wholeEquality? current
        | throwError "Cannot infer the whole equality; supply it as an argument."
      pure target
  unless target.isAppOfArity ``Eq 3 do throwError "Expected an equality as the new goal."
  if ← isDefEq current target then throwError "The new equality is already the current goal."
  let bridge ← withLocalDeclD `whole_eq target fun hyp => do
    let proof ← mkFreshExprSyntheticOpaqueMVar current
    let saved ← saveState
    let mut sources := #[hyp]
    let before := (← getLCtx).getFVarIds
    try
      let next ← indiscernHypothesis proof.mvarId! hyp.fvarId! #[] [] true
      unless next.isEmpty do
        let next := next.head!
        let added ← next.withContext do
          pure ((← getLCtx).getFVarIds.filter fun id => !before.contains id)
        sources := sources ++ added.map mkFVar
        solveComparison next sources false
    catch _ =>
      saved.restore
      solveComparison proof.mvarId! #[hyp] false
    mkLambdaFVars #[hyp] (← instantiateMVars proof)
  let next ← mkFreshExprSyntheticOpaqueMVar target
  goal.assign (mkApp bridge next)
  return [next.mvarId!]


/-- The premise slots come from the chosen ext theorem, not from flattening its iff. -/
private def comparisonOutputs (goal : MVarId) (hyp : FVarId)
    (args : Array Syntax) : TacticM (Array RuleOutput) := goal.withContext do
  let type ← withReducible <| whnf (← instantiateMVars (← hyp.getType))
  let proof := mkFVar hyp
  let mut comparison ← registeredEvidence? type proof
  if comparison.isNone then comparison ← primitiveComparison? type proof
  if comparison.isNone then comparison ← quotientComparison? type proof
  if comparison.isNone then comparison ← inverseExtComparison? type proof
  let some (evidence, condition) := comparison
    | throwError "No registered comparison rule is available for this equality."
  if !args.isEmpty then
    let (evidence, condition) ← specializeComparison evidence condition args
    return #[{ proof := evidence, type := ← computeComparison condition }]
  let prototype ← mkFreshExprSyntheticOpaqueMVar type
  let slots ← forwardExtStep prototype.mvarId!
  let sources ← flattenFacts evidence
  let mut outputs := #[]
  for slot in slots do
    let slotType ← slot.withContext <| instantiateMVars (← slot.getType)
    let condition ← if slots.length == 1 && (← isDefEq slotType condition) then
      pure condition else pure slotType
    solveComparison slot sources false
    outputs := outputs.push {
      proof := ← instantiateMVars (.mvar slot)
      type := ← computeComparison condition
    }
  return outputs

def extractRuleComparison (goal : MVarId) (hyp : FVarId)
    (args : Array Syntax) (patterns : Array RulePattern) : TacticM (List MVarId) := do
  let base ← hyp.getUserName
  let saved ← saveState
  let result : Except Exception (Array RuleOutput) ← try pure (.ok (← comparisonOutputs goal hyp args))
    catch error => pure (.error error)
  match result with
  | .ok outputs =>
    noteRuleOutputs goal outputs patterns base (if patterns.isEmpty then some hyp else none)
  | .error error =>
    saved.restore
    unless args.isEmpty do throw error
    -- Constructor injectivity is also a one-layer comparison, including Int.ofNat.
    let before ← goal.withContext do pure (← getLCtx).getFVarIds
    match ← retainedInjection goal hyp with
    | .unchanged => throw error
    | .solved => pure []
    | .subgoal next facts _ =>
      let introduced ← next.withContext do
        pure ((← getLCtx).getFVarIds.filter fun id => !before.contains id)
      let outputs ← next.withContext <| facts.mapM fun id => do
        pure { proof := mkFVar id, type := ← id.getType : RuleOutput }
      let goals ← noteRuleOutputs next outputs patterns base (if patterns.isEmpty then some hyp else none)
      -- Keep the requested outputs, not the temporary copy used by native injection.
      goals.mapM fun g => introduced.reverse.foldlM (fun g id => g.tryClear id) g

private def pairEquality (types : Array Expr) : MetaM Expr := do
  unless types.size >= 2 do throwError "Select at least two equality goals or hypotheses."
  let mut left := #[]
  let mut right := #[]
  for type in types do
    let type ← instantiateMVars type
    let type := type.consumeMData
    let some (_, a, b) := type.eq?
      | throwError "Automatic grouping requires equalities; specify the resulting equality explicitly."
    left := left.push a
    right := right.push b
  let mut a := left.back!
  let mut b := right.back!
  for i in (List.range (types.size - 1)).reverse do
    a ← mkAppM ``Prod.mk #[left[i]!, a]
    b ← mkAppM ``Prod.mk #[right[i]!, b]
  mkEq a b

def extractComparisonsRecursively (goal : MVarId) (roots : Array FVarId)
    (args : Array Syntax) (maxDepth : Nat := 100)
    (patterns : Array RulePattern := #[]) : TacticM (List MVarId) := do
  let mut current := goal
  let mut queue := roots.map (·, 0)
  let mut leaves : Array RuleOutput := #[]
  let mut cursor := 0
  let mut count := 0
  let mut applied := false
  while cursor < queue.size do
    if count >= 256 then
      throwError "Comparison exceeded 256 facts; use 'indisc : n' on a selected hypothesis."
    let (hyp, depth) := queue[cursor]!
    cursor := cursor + 1
    if depth >= maxDepth then
      leaves := leaves.push { proof := mkFVar hyp, type := ← current.withContext hyp.getType }
      continue
    let saved ← saveState
    try
      let before ← current.withContext do pure (← getLCtx).getFVarIds
      let outputs ← comparisonOutputs current hyp (if depth == 0 then args else #[])
      applied := true
      let parentType ← current.withContext hyp.getType
      let mut fresh := #[]
      for output in outputs do
        -- Preserve distinct output slots even when their propositions coincide.
        -- A rule returning its own input is a leaf, not a recursive cycle.
        if ← current.withContext <| withNewMCtxDepth <| isDefEq parentType output.type then
          leaves := leaves.push output
        else fresh := fresh.push output
      unless fresh.isEmpty do
        let base ← mkFreshUserName ((← hyp.getUserName).appendAfter "_compare")
        let next ← noteRuleOutputs current fresh #[] base
        current := next.head!
      let added ← current.withContext do
        pure ((← getLCtx).getFVarIds.filter fun id => !before.contains id)
      -- Match ext's left-to-right, depth-first order when naming leaf results.
      queue := queue[:cursor].toArray ++ added.map (·, depth + 1) ++ queue[cursor...*].toArray
      count := count + added.size
    catch _ =>
      saved.restore
      -- Generated constructors also provide a sound reverse comparison rule.
      let next ← retainedInjection current hyp [] true
      match next with
      | .solved => return []
      | .subgoal g facts _ =>
        applied := applied || !facts.isEmpty
        current := g
        queue := queue[:cursor].toArray ++ facts.map (·, depth + 1) ++ queue[cursor...*].toArray
        count := count + facts.size
      | .unchanged =>
        unless depth == 0 do
          leaves := leaves.push { proof := mkFVar hyp, type := ← current.withContext hyp.getType }
  if !applied && maxDepth > 0 && roots.size == 1 then
    throwError "No comparison rule applies to this hypothesis. Supply an equality or use an explicit inference rule."
  if !patterns.isEmpty then
    return ← noteRuleOutputs current leaves patterns (← roots[0]!.getUserName)
  return [current]


/-- Combine selected goals by constructing a separate projection proof for every old goal. -/
def combineComparisonGoals (selected : Array MVarId) (target? : Option Syntax)
    (patterns : Array RulePattern) : TacticM Unit := do
  checkSharedGoals selected
  selected[0]!.withContext do
    let types ← selected.mapM fun g => do instantiateMVars (← g.getType)
    let target ← if let some stx := target? then
      Term.elabTermEnsuringType stx (mkSort .zero)
    else pairEquality types
    unless target.isAppOfArity ``Eq 3 do throwError "The combined goal must be an equality."
    let next ← mkFreshExprSyntheticOpaqueMVar target
    let mut proofs := #[]
    -- Only the proposed equality is available to the bridge; unrelated assumptions are not used.
    for type in types do
      let bridge ← withLocalDeclD `combined_eq target fun source => do
        let result ← mkFreshExprSyntheticOpaqueMVar type
        let outputs ← comparisonOutputs result.mvarId! source.fvarId! #[]
        solveComparison result.mvarId! (#[source] ++ outputs.map (·.proof)) false
        mkLambdaFVars #[source] (← instantiateMVars result)
      proofs := proofs.push (mkApp bridge next)
    for goal in selected, proof in proofs do goal.assign proof
    let nextGoals ← nameRuleGoals [next.mvarId!] patterns
    replaceSelectedGoals selected (← finishTransformGoals nextGoals)

def assembleComparisonHypotheses (goal : MVarId) (hyps : Array FVarId)
    (target? : Option Syntax) (patterns : Array RulePattern)
    (recursive := false) (maxDepth : Nat := 12) : TacticM (List MVarId) := goal.withContext do
  unless !hyps.isEmpty do throwError "Select at least one hypothesis."
  let types ← hyps.mapM (·.getType)
  let target ← if let some stx := target? then
    Term.elabTermEnsuringType stx (mkSort .zero)
  else if hyps.size == 1 then
    match ← wholeEquality? types[0]! with
    | some type => pure type
    | none => throwError "Cannot infer the whole equality; specify it after ':'."
  else pairEquality types
  unless target.isAppOfArity ``Eq 3 do throwError "Expected an equality as the result type."
  let result ← mkFreshExprSyntheticOpaqueMVar target
  let sources := (← hyps.mapM fun h => flattenFacts (.fvar h)).flatten
  if recursive then
    solveComparison result.mvarId! sources true maxDepth
  else
    let slots ← forwardExtStep result.mvarId!
    if hyps.size > 1 && slots.length != hyps.size then
      throwError "The rule has {slots.length} premise slot(s), but {hyps.size} hypotheses were selected."
    for slot in slots do solveComparison slot sources false
  let output := { proof := ← instantiateMVars result, type := target : RuleOutput }
  let next ← noteRuleOutputs goal #[output] patterns (← hyps[0]!.getUserName)
  if patterns.isEmpty then
    next.mapM fun g => hyps.foldlM (fun g h => g.tryClear h) g
  else pure next

def normalizeComparisonGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  goal.replaceTargetDefEq (← computeComparison type)


end Ample.Automation

namespace Ample

/-- `indiscern at h` is a compatibility spelling for extracting comparison facts from an equality.
Use `indiscern x at h` to observe a function at `x`, and `with ...` to name the results.
The current one-step spelling is `indisc at h`. -/
scoped syntax (name := ampleIndiscern) (priority := high)
  "indiscern" (ppSpace colGt term:max)* " at " ident
  (" with" (ppSpace colGt (ident <|> hole))+)? : tactic

/-- `indiscern! at h` is a compatibility spelling for recursive extraction of comparison facts.
It retains the source equality and intermediate comparisons. The current spelling is `indisc! at h`. -/
scoped syntax (name := ampleIndiscernRecursive) "indiscern!"
  (ppSpace colGt term:max)* " at " (ident <|> "*") : tactic

/-- `indiscern` is a compatibility spelling for replacing a comparison goal by a sufficient whole equality.
The current one-step spelling is `indisc`. Supply the intended equality as an argument if it cannot be inferred. -/
scoped syntax (name := ampleIndiscernGoal) "indiscern" (ppSpace colGt term:max)? : tactic


@[tactic ampleIndiscern]
def evalIndiscern : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let hyp ← elabAsFVar stx[3]
      let args := stx[1].getArgs
      let names := if stx[4].isNone then [] else stx[4][1].getArgs.toList.map getNameOfIdent'
      replaceMainGoal (← Automation.indiscernHypothesis (← getMainGoal) hyp args names)
  catch e =>
    saved.restore
    throw e

@[tactic ampleIndiscernRecursive]
def evalIndiscernRecursive : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let args := stx[1].getArgs
      let roots ← if stx[3].isIdent then pure #[← elabAsFVar stx[3]]
        else do
          unless args.isEmpty do throwError "Observation arguments require a single hypothesis."
          getPropHyps
      replaceMainGoal (← Automation.indiscernRecursively (← getMainGoal) roots args)
  catch e =>
    saved.restore
    throw e

@[tactic ampleIndiscernGoal]
def evalIndiscernGoal : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let target? := if stx[1].isNone then none else some stx[1][0]
      replaceMainGoal (← Automation.compareGoal (← getMainGoal) target?)
  catch e => saved.restore; throw e


open Ample.Automation in
/-- `indisc at h` extracts one layer of comparison facts from an equality hypothesis.
For example, an equality of pairs gives equalities of their components.
Without `with`, the original hypothesis is replaced; `with` keeps it and names the new facts.

`indisc x at h` observes a function equality at `x`.
Use `indisc : n at h` for a fixed depth or `indisc! at h` to repeat comparisons.
`with first second` names the comparison facts in left-to-right order; names do not determine the depth. -/
scoped syntax (name := ampleIndiscAt) (priority := high)
  "indisc" (ppSpace colGt term:max)* (" : " num)? " at " (ident <|> "*")
  (" with" (ppSpace colGt ruleOutput)+)? : tactic
open Ample.Automation in
/-- `indisc` replaces a comparison goal by a whole equality sufficient to establish it.
For example, it can replace `p.1 = q.1` by the pair equality `p = q`.
The default applies one rule. Use `indisc : n` for a fixed depth or `indisc!` to repeat.
Use an explicit argument such as `indisc (p = q)` when the whole equality cannot be inferred. -/
scoped syntax (name := ampleIndiscGoal)
  "indisc" (ppSpace colGt term:max)? (" : " num)?
  (" with" (ppSpace colGt ruleOutput)+)? : tactic
open Ample.Automation in
/-- `indisc goals first second with combined` combines selected comparison goals into one whole equality.
For example, goals `a = b` and `c = d` combine into `(a, c) = (b, d)`.
Only independent goals in the same local context can be combined. An optional `: ...` specifies the whole equality. -/
scoped syntax (name := ampleIndiscGoals) (priority := high)
  "indisc" &"goals" (ppSpace colGt ident)+ (" with" (ppSpace colGt ruleOutput)+)?
  (" : " term)? : tactic
/-- `indisc! at h` repeatedly extracts comparisons, retaining the source and intermediate facts.
Use `indisc! at *` to process the current hypotheses, or `indisc at h` for one layer. -/
scoped syntax (name := ampleIndiscRecursive) "indisc!"
  (ppSpace colGt term:max)* " at " (ident <|> "*") : tactic
/-- `indisc!` repeatedly replaces a comparison goal by a sufficient whole equality.
Use `indisc` to perform one step. -/
scoped syntax (name := ampleIndiscGoalRecursive)
  "indisc!" (ppSpace colGt term:max)? : tactic
open Ample.Automation in
/-- `ext at h1 h2 with h` derives a whole equality from comparison hypotheses.
For example, `h1 : a = b` and `h2 : c = d` give `h : (a, c) = (b, d)`.
Use `ext at h with whole : p = q` to specify the intended equality.

The default uses one comparison layer; `ext : n at ...` selects a depth and `ext! at ...` repeats.
Supplying `with` retains the original hypotheses. -/
scoped syntax (name := ampleExtAtMany) (priority := high)
  "ext" (" : " num)? " at" (ppSpace colGt ident)+ (" with" (ppSpace colGt ruleOutput)+)?
  (" : " term)? : tactic

@[tactic ampleIndiscAt] def evalIndiscAt : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    withMainContext do
      let roots ← if stx[4].isIdent then pure #[← elabAsFVar stx[4]] else getPropHyps
      let patterns ← if stx[5].isNone then pure #[] else
        stx[5][1].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
      let depth := if stx[2].isNone then 1 else (⟨stx[2][1]⟩ : TSyntax `num).getNat
      if roots.isEmpty then throwError "Select an equality hypothesis."
      unless stx[4].isIdent || (patterns.isEmpty && stx[1].getArgs.isEmpty) do
        throwError "Observation arguments and output names require one hypothesis."
      if depth == 1 && roots.size == 1 then
        replaceMainGoal (← Automation.extractRuleComparison (← getMainGoal) roots[0]! stx[1].getArgs patterns)
      else
        replaceMainGoal (← Automation.extractComparisonsRecursively (← getMainGoal) roots stx[1].getArgs depth patterns)
  catch e => saved.restore; throw e

@[tactic ampleIndiscGoal] def evalIndiscGoal : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    let target? := if stx[1].isNone then none else some stx[1][0]
    let patterns ← if stx[3].isNone then pure #[] else
      stx[3][1].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
    let depth := if stx[2].isNone then 1 else (⟨stx[2][1]⟩ : TSyntax `num).getNat
    let mut next := [← getMainGoal]
    let mut used := 0
    for _ in [:depth] do
      let savedStep ← saveState
      try
        next ← Automation.compareGoal next.head! target?
        used := used + 1
        if target?.isSome then break
      catch error =>
        savedStep.restore
        if used == 0 then throw error
        break
    replaceMainGoal (← Automation.nameRuleGoals next patterns)
  catch e => saved.restore; throw e

@[tactic ampleIndiscGoals] def evalIndiscGoals : Tactic := fun stx => do
  let saved ← saveState
  try
    let selected ← Automation.selectRuleGoals (stx[2].getArgs.map (·.getId))
    let patterns ← if stx[3].isNone then pure #[] else
      stx[3][1].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
    let target? := if stx[4].isNone then none else some stx[4][1]
    Automation.combineComparisonGoals selected target? patterns
  catch e => saved.restore; throw e

@[tactic ampleIndiscRecursive] def evalIndiscRecursive : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    withMainContext do
      let roots ← if stx[3].isIdent then pure #[← elabAsFVar stx[3]] else getPropHyps
      unless stx[3].isIdent || stx[1].getArgs.isEmpty do
        throwError "Observation arguments require a single hypothesis."
      replaceMainGoal (← Automation.extractComparisonsRecursively (← getMainGoal) roots stx[1].getArgs)
  catch e => saved.restore; throw e

@[tactic ampleIndiscGoalRecursive] def evalIndiscGoalRecursive : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    let target? := if stx[1].isNone then none else some stx[1][0]
    let mut next ← Automation.compareGoal (← getMainGoal) target?
    if target?.isNone then
      for _ in [:7] do
        let step ← saveState
        try next ← Automation.compareGoal next.head! none catch _ => step.restore; break
    replaceMainGoal next
  catch e => saved.restore; throw e

@[tactic ampleExtAtMany] def evalExtAtMany : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    withMainContext do
      let hyps ← stx[3].getArgs.mapM elabAsFVar
      let patterns ← if stx[4].isNone then pure #[] else
        stx[4][1].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
      let target? := if stx[5].isNone then none else some stx[5][1]
      let depth := if stx[1].isNone then 1 else (⟨stx[1][1]⟩ : TSyntax `num).getNat
      replaceMainGoal (← Automation.assembleComparisonHypotheses (← getMainGoal) hyps target? patterns (depth != 1) depth)
  catch e => saved.restore; throw e


open Ample.Automation in
/-- `ext! at h1 h2 with whole` combines comparison hypotheses through multiple layers.
Use `ext at ...` when the hypotheses are the immediate comparison conditions. -/
scoped syntax (name := ampleExtAtRecursive)
  "ext!" " at" (ppSpace colGt ident)+ (" with" (ppSpace colGt ruleOutput)+)?
  (" : " term)? : tactic

@[tactic ampleExtAtRecursive] def evalExtAtRecursive : Tactic := fun stx => Automation.runTransform do
  let saved ← saveState
  try
    withMainContext do
      let hyps ← stx[2].getArgs.mapM elabAsFVar
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => Automation.parseRulePattern ⟨p⟩
      let target? := if stx[4].isNone then none else some stx[4][1]
      -- Assembly can use several registered comparison layers; its result remains one equality.
      if hyps.size == 1 then
        let name? ← if patterns.isEmpty then pure none else
          match patterns[0]! with
          | .name name => pure (some name)
          | _ => throwError "The assembled equality requires a name, not a tuple pattern."
        Automation.checkPatternArity patterns 1
        replaceMainGoal (← Automation.recoverEquality (← getMainGoal) hyps[0]! target? name?)
      else
        replaceMainGoal (← Automation.assembleComparisonHypotheses (← getMainGoal) hyps target? patterns true)
  catch e => saved.restore; throw e

end Ample
