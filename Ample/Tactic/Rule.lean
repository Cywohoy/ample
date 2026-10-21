/-
The forward apply-at interface follows Mathlib/Tactic/ApplyAt.lean.
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The rule argument matcher and shared pattern/goal machinery are implemented
here using Lean's core APIs.
Source: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/ApplyAt.lean
-/
import Lean.Elab.Tactic.RCases
import Lean.Meta.Tactic.Constructor
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Induction
import Ample.Tactic.Classical

open Lean Meta Elab Tactic

namespace Ample.Automation

/-- A pattern names a rule output, or explicitly opens one grouped output. -/
inductive RulePattern where
  | name (name : Name)
  | tuple (children : Array RulePattern)
  deriving Inhabited

declare_syntax_cat ruleOutput
syntax ident : ruleOutput
syntax "_" : ruleOutput
syntax "⟨" ruleOutput,* "⟩" : ruleOutput

partial def parseRulePattern (stx : TSyntax `ruleOutput) : TacticM RulePattern := do
  match stx with
  | `(ruleOutput| $id:ident) => return .name id.getId
  | `(ruleOutput| _) => return .name .anonymous
  | `(ruleOutput| ⟨$[$children],*⟩) =>
    return .tuple (← children.mapM parseRulePattern)
  | _ => throwUnsupportedSyntax

private partial def nativePattern (pat : RulePattern) : TacticM (TSyntax `rcasesPat) := do
  match pat with
  | .name n =>
    if n.isAnonymous then `(rcasesPat| _)
    else `(rcasesPat| $(mkIdent n):ident)
  | .tuple children =>
    let children ← children.mapM nativePattern
    `(rcasesPat| ⟨$[$children],*⟩)

/-- Output boundaries are preserved: a tuple pattern consumes exactly one output. -/
def checkPatternArity (patterns : Array RulePattern) (outputs : Nat) : TacticM Unit := do
  unless patterns.isEmpty || patterns.size == outputs do
    throwError "Expected {outputs} output pattern(s), but received {patterns.size}. Use separate names for independent outputs; use one tuple pattern only to open a single grouped output."
  let rec names : RulePattern → Array Name
    | .name n => if n.isAnonymous then #[] else #[n]
    | .tuple children => children.flatMap names
  let mut seen : Array Name := #[]
  for name in patterns.flatMap names do
    if seen.contains name then
      throwError "Duplicate output name '{name}'. Choose a distinct name for each result, or use '_' for an unnamed result."
    seen := seen.push name

private partial def nameGoal (goal : MVarId) (pattern : RulePattern) :
    TacticM (List MVarId) := goal.withContext do
  match pattern with
  | .name n =>
    unless n.isAnonymous do goal.setTag n
    return [goal]
  | .tuple children =>
    let type ← whnf (← goal.getType)
    let .const head _ := type.getAppFn
      | throwError "A tuple pattern requires a goal with one constructor."
    let some (.inductInfo info) := (← getEnv).find? head
      | throwError "A tuple pattern requires a goal with one constructor."
    unless info.ctors.length == 1 do
      throwError "A tuple pattern cannot choose between different constructors."
    let next ← goal.apply (← mkConstWithFreshMVarLevels info.ctors.head!) { newGoals := .all }
    let children := if type.isAppOfArity ``And 2 && children.size > 2 then
      #[children[0]!, .tuple children[1...*].toArray] else children
    unless children.size == next.length do
      throwError "The grouped output has {next.length} component(s), but the pattern names {children.size}."
    let mut results := []
    for g in next, p in children do
      results := results ++ (← nameGoal g p)
    return results

def nameRuleGoals (goals : List MVarId) (patterns : Array RulePattern) :
    TacticM (List MVarId) := do
  checkPatternArity patterns goals.length
  if patterns.isEmpty then return goals
  let mut results := []
  for goal in goals, pattern in patterns do
    results := results ++ (← nameGoal goal pattern)
  return results

/-- An output is a typed proof term; a group is never flattened implicitly. -/
structure RuleOutput where
  proof : Expr
  type : Expr
  deriving Inhabited

def noteRuleOutputs (goal : MVarId) (outputs : Array RuleOutput)
    (patterns : Array RulePattern) (base : Name)
    (replace? : Option FVarId := none) : TacticM (List MVarId) := do
  checkPatternArity patterns outputs.size
  let mut current := [goal]
  for i in [:outputs.size] do
    let pattern := patterns[i]?.getD (.name <|
      if outputs.size == 1 then base else base.appendAfter s!"_{i + 1}")
    -- Check the same grouped shape that is required when naming goal outputs.
    if pattern matches .tuple _ then
      let saved ← saveState
      try
        let scratch ← mkFreshExprSyntheticOpaqueMVar outputs[i]!.type
        discard <| nameGoal scratch.mvarId! pattern
        saved.restore
      catch e => saved.restore; throw e
    let mut next := []
    for g in current do
      let updated ← g.withContext do
        let name ← match pattern with
          | .name n => if n.isAnonymous then mkFreshUserName base else pure n
          | .tuple _ => mkFreshUserName (base.appendAfter "_group")
        let (_, g) ← if ← isProp outputs[i]!.type then
          g.note name outputs[i]!.proof outputs[i]!.type
        else
          (← g.define name outputs[i]!.type outputs[i]!.proof).intro1P
        match pattern with
        | .name _ => return [g]
        | .tuple _ =>
          let pat ← nativePattern pattern
          evalTacticAt (← `(tactic| rcases $(mkIdent name):ident with $pat:rcasesPat)) g
      next := next ++ updated
    current := next
  if let some old := replace? then
    current ← current.mapM (·.tryClear old)
  return current

/-- Only genuinely shared local contexts may be combined without quantification. -/
def checkSharedGoals (goals : Array MVarId) (propositionsOnly := true) : TacticM Unit := do
  unless !goals.isEmpty do throwError "Select at least one goal."
  let first ← goals[0]!.getDecl
  for goal in goals do
    let decl ← goal.getDecl
    unless decl.lctx.getFVarIds == first.lctx.getFVarIds &&
        decl.localInstances == first.localInstances do
      throwError "Selected goals have different local contexts. Goals '{← goals[0]!.getTag}' and '{← goal.getTag}' use different assumptions. Combine them before introducing branch-specific assumptions, or prove them separately."
    goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      if propositionsOnly && !(← isProp type) then
        throwError "Only proposition goals can be combined."
      if type.hasExprMVar then
        throwError "Selected goals contain unresolved dependencies. Choose the required witness or value first; then combine the independent goals."

def selectRuleGoals (names : Array Name) : TacticM (Array MVarId) := do
  let all ← getUnsolvedGoals
  let mut selected := #[]
  for name in names do
    let matchingGoals ← all.filterM fun goal => do pure ((← goal.getTag) == name)
    let [goal] := matchingGoals
      | throwError "Goal name '{name}' must identify exactly one open goal."
    if selected.contains goal then throwError "A goal cannot be selected twice."
    selected := selected.push goal
  return selected

def replaceSelectedGoals (selected : Array MVarId) (next : List MVarId) :
    TacticM Unit := do
  let all ← getGoals
  let mut replaced := false
  let mut result := []
  for goal in all do
    if selected.contains goal then
      unless replaced do
        result := result ++ next
        replaced := true
    else result := result ++ [goal]
  unless replaced do throwError "The selected goals are no longer open."
  setGoals result

private partial def matchingRuleArguments (type wanted : Expr)
    (arguments : Array Expr := #[]) (infos : Array BinderInfo := #[])
    (fuel : Nat := 64) : MetaM (Array Expr × Array BinderInfo) := do
  if fuel == 0 then throwError "Rule argument search exceeded its limit."
  let .forallE name domain body info ← whnf type
    | throwError "No argument of this rule matches the hypothesis."
  let saved ← saveState
  let matched ← try isDefEq domain wanted catch _ => pure false
  if matched then return (arguments, infos)
  saved.restore
  let argument ← mkFreshExprMVar domain (userName := name)
  matchingRuleArguments (body.instantiate1 argument) wanted
    (arguments.push argument) (infos.push info) (fuel - 1)


/-- Supply ordered hypotheses to the actual telescope; later binders remain unapplied. -/
def applyRuleAtMany (rule : Expr) (hypotheses : Array FVarId)
    (patterns : Array RulePattern) : TacticM (List MVarId) := do
  let goal ← getMainGoal
  goal.withContext do
    unless !hypotheses.isEmpty do throwError "Supply at least one hypothesis."
    let mut proof := rule
    let mut pending := #[]
    let mut pendingInfos := #[]
    for hyp in hypotheses do
      let decl ← hyp.getDecl
      let (arguments, infos) ← matchingRuleArguments (← inferType proof) decl.type
      proof := mkAppN proof (arguments.push (mkFVar hyp))
      pending := pending ++ arguments
      pendingInfos := pendingInfos ++ infos
    -- Solve typeclass slots after supplied arguments have constrained their
    -- types. Use Lean's retrying synthesis rather than turning an absent
    -- instance into an ordinary mathematical obligation.
    try
      postprocessAppMVars `apply goal pending pendingInfos false false
    catch error =>
      throwError "Cannot synthesize a required instance. Add a local instance with 'letI' or supply the structure explicitly.\n{error.toMessageData}"
    let type ← instantiateMVars (← inferType proof)
    let base ← hypotheses[0]!.getUserName
    let next ← noteRuleOutputs goal #[{ proof, type }] patterns base
      (if patterns.isEmpty && hypotheses.size == 1 then some hypotheses[0]! else none)
    let mut missing := []
    for argument in pending do
      unless ← argument.mvarId!.isAssigned do missing := missing ++ [argument.mvarId!]
    -- Explicit holes in the supplied rule are obligations too; they are not
    -- necessarily among the binders introduced by the argument matcher.
    for id in ← getMVarsNoDelayed proof do
      unless missing.contains id || (← id.isAssigned) do missing := missing ++ [id]
    return missing ++ next

def applyRuleAt (rule : Expr) (hyp : FVarId)
    (patterns : Array RulePattern) : TacticM (List MVarId) :=
  applyRuleAtMany rule #[hyp] patterns

/-- Infer a binary conjunction or product while retaining each selected type as one field. -/
private def inferredBundleType (types : Array Expr) (recursive := false) : MetaM Expr := do
  unless types.size >= 2 && (recursive || types.size == 2) do
    throwError "Automatic grouping requires two inputs. Specify the result type for another constructor."
  let propositions ← types.allM isProp
  let mut result := types.back!
  for i in (List.range (types.size - 1)).reverse do
    if propositions then result := mkApp2 (mkConst `And) types[i]! result
    else
      try result ← mkAppM `Prod #[types[i]!, result]
      catch _ => throwError "Cannot infer a product type for these inputs; specify the result type."
  return result

/-- Apply an actual constructor, checking its field count, field order, and dependencies. -/
private def constructFromInputs (type : Expr) (inputs : Array Expr) : MetaM Expr := do
  let reduced ← whnf type
  let .const head _ := reduced.getAppFn
    | throwError "The result type is not an inductive type."
  let some (.inductInfo info) := (← getEnv).find? head
    | throwError "The result type is not an inductive type."
  let mut candidates := #[]
  for ctor in info.ctors do
    let saved ← saveState
    try
      let proof ← mkFreshExprSyntheticOpaqueMVar type
      let fields ← proof.mvarId!.applyConst ctor { newGoals := .all }
      unless fields.length == inputs.size do
        throwError "The constructor field count does not match the supplied inputs."
      for field in fields, input in inputs do
        field.withContext do
          unless ← isDefEq (← field.getType) (← inferType input) do
            throwError "An input does not have the required field type."
          field.assign input
      let result ← instantiateMVars proof
      if result.hasExprMVar then throwError "The constructor has unresolved dependencies."
      saved.restore
      candidates := candidates.push result
    catch _ => saved.restore
  let #[proof] := candidates
    | if candidates.isEmpty then
        throwError "No constructor matches the supplied inputs and result type."
      else throwError "Several constructors match. Use an explicit constructor with apply."
  return proof

def constructorRuleAt (goal : MVarId) (inputs : Array FVarId)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  let types ← inputs.mapM fun h => do instantiateMVars (← h.getType)
  let values := inputs.map mkFVar
  let (proof, type) ← if let some resultSyntax := target? then do
    let type ← Term.elabType resultSyntax
    if type.hasExprMVar then throwError "The result type contains unresolved dependencies."
    pure (← constructFromInputs type values, type)
  else do
    let current ← instantiateMVars (← goal.getType)
    let saved ← saveState
    let currentProof? ← try pure (some (← constructFromInputs current values))
      catch _ => saved.restore; pure none
    if let some proof := currentProof? then pure (proof, current)
    else
      let type ← inferredBundleType types
      pure (← constructFromInputs type values, type)
  -- Construction adds a fact; it does not solve the current goal implicitly.
  noteRuleOutputs goal #[{proof, type}] patterns `h


/-- Match independent outputs in order, recursively opening only unmatched grouped fields. -/
private def caseFieldOutputs (goal : MVarId) (fields : Array Expr)
    (types : Array Expr) (recursive : Bool) : MetaM (MVarId × Array Expr) := do
  let mut current := goal
  let mut remaining := fields.toList
  let mut outputs := #[]
  let mut fuel := 32
  for type in types do
    let mut found := false
    while !found do
      let field :: tail := remaining
        | throwError "Not enough constructor fields for the selected goals."
      let matched ← current.withContext do isDefEq (← inferType field) type
      if matched then
        outputs := outputs.push field
        remaining := tail
        found := true
      else
        unless recursive && field.isFVar do
          throwError "A constructor field does not match its selected goal."
        if fuel == 0 then throwError "Recursive case analysis exceeded its depth limit."
        fuel := fuel - 1
        let next ← current.withContext do
          let fieldType ← whnf (← inferType field)
          let .const head _ := fieldType.getAppFn
            | throwError "This field cannot be decomposed as a group."
          let some (.inductInfo info) := (← getEnv).find? head
            | throwError "This field cannot be decomposed as a group."
          unless info.ctors.length == 1 do
            throwError "Case branches cannot be combined as simultaneous fields."
          current.cases field.fvarId!
        let #[branch] := next
          | throwError "Recursive case analysis requires exactly one branch."
        current := branch.mvarId
        remaining := branch.fields.toList ++ tail.map branch.subst.apply
        outputs := outputs.map branch.subst.apply
  unless remaining.isEmpty do
    throwError "The constructor has more fields than the selected goals."
  return (current, outputs)

/-- Reverse case analysis only after proving a projection for each selected goal. -/
def combineConstructorGoals (selected : Array MVarId) (target? : Option Syntax)
    (patterns : Array RulePattern) (recursive := false) : TacticM Unit := do
  checkSharedGoals selected false
  selected[0]!.withContext do
    let types ← selected.mapM fun g => do instantiateMVars (← g.getType)
    let target ← if let some resultSyntax := target? then Term.elabType resultSyntax
      else inferredBundleType types recursive
    if target.hasExprMVar then throwError "The combined type contains unresolved dependencies."
    let reduced ← whnf target
    let .const head _ := reduced.getAppFn
      | throwError "The combined type must have exactly one constructor."
    let some (.inductInfo info) := (← getEnv).find? head
      | throwError "The combined type must have exactly one constructor."
    unless info.ctors.length == 1 do
      throwError "Case branches cannot be combined as simultaneous fields."
    let next ← mkFreshExprSyntheticOpaqueMVar target
    let mut bridges := #[]
    for i in [:types.size] do
      let bridge ← withLocalDeclD `combined target fun packed => do
        let proof ← mkFreshExprSyntheticOpaqueMVar types[i]!
        let #[branch] ← proof.mvarId!.cases packed.fvarId!
          | throwError "The result type does not yield one case."
        let (projected, outputs) ← caseFieldOutputs branch.mvarId branch.fields types recursive
        projected.assign outputs[i]!
        let result ← instantiateMVars proof
        if result.hasExprMVar then throwError "The projection has unresolved dependencies."
        mkLambdaFVars #[packed] result
      bridges := bridges.push bridge
    for goal in selected, bridge in bridges do goal.assign (mkApp bridge next)
    replaceSelectedGoals selected (← nameRuleGoals [next.mvarId!] patterns)


/-- Open one product-like constructor. A field naming pattern never selects a sum branch. -/
def unpackRuleHypothesis (goal : MVarId) (hypothesis : FVarId)
    (pattern? : Option RulePattern) (eliminate : Bool := true) : TacticM (List MVarId) := goal.withContext do
  let type ← whnf (← hypothesis.getType)
  let .const head _ := type.getAppFn
    | throwError "unpack requires a product-like type with one constructor."
  let some (.inductInfo info) := (← getEnv).find? head
    | throwError "unpack requires a product-like type with one constructor."
  unless info.ctors.length == 1 && info.numIndices == 0 do
    throwError "Cannot unpack hypothesis '{← hypothesis.getUserName}' : {type}. Its constructors represent different cases, not simultaneous fields. Use 'cases' for case analysis or 'rcases' with a branching pattern."
  let .ctorInfo ctor ← getConstInfo info.ctors.head!
    | throwError "Unable to inspect the constructor fields."
  let pattern ← if let some pattern := pattern? then
    match pattern with
    | .tuple children =>
      unless children.size == ctor.numFields do
        throwError "Expected {ctor.numFields} field names in one tuple pattern. Write 'unpack h with ⟨field1, ...⟩' for the fields of this object."
      for child in children do
        unless child matches .name _ do
          throwError "unpack opens one layer; use another unpack or rcases for a nested pattern."
      pure pattern
    | _ => throwError "Use a tuple pattern for the fields of this one object."
  else do
    let children ← (List.range ctor.numFields).toArray.mapM fun i => do
      pure (RulePattern.name (← mkFreshUserName (.mkSimple s!"field_{i + 1}")))
    pure (.tuple children)
  if !eliminate then
    if let some structureInfo := getStructureInfo? (← getEnv) head then
      let .tuple children := pattern | throwError "Expected a tuple field pattern."
      unless structureInfo.fieldNames.size == children.size do
        throwError "The structure fields do not match the constructor fields."
      let mut outputs := #[]
      for fieldName in structureInfo.fieldNames do
        let some field := getFieldInfo? (← getEnv) head fieldName
          | throwError "Unable to inspect a projection function."
        let proof ← mkAppM field.projFn #[mkFVar hypothesis]
        outputs := outputs.push {proof, type := ← inferType proof}
      return ← noteRuleOutputs goal outputs children `field
  let pattern ← nativePattern pattern
  let name ← hypothesis.getUserName
  evalTacticAt (← `(tactic| rcases $(mkIdent name):ident with $pattern:rcasesPat)) goal


/-- Disjunction introduction may leave its unused proposition as an explicit type goal. -/
def disjunctionRuleAt (goal : MVarId) (hyp : FVarId) (side : Bool)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  let input := mkFVar hyp
  let inputType ← instantiateMVars (← inferType input)
  unless ← isProp inputType do throwError "Disjunction introduction requires a proposition proof."
  let mut missing := []
  let target ← if let some resultSyntax := target? then Term.elabType resultSyntax
  else do
    let current ← instantiateMVars (← goal.getType)
    if (← whnf current).isAppOfArity `Or 2 then pure current
    else
      let other ← mkFreshExprMVar (mkSort .zero) (userName := `alternative)
      other.mvarId!.setTag `alternative
      missing := [other.mvarId!]
      pure (if side then mkApp2 (mkConst `Or) other inputType
        else mkApp2 (mkConst `Or) inputType other)
  unless (← whnf target).isAppOfArity `Or 2 do
    throwError "The result type must be a disjunction."
  let result ← mkFreshExprSyntheticOpaqueMVar target
  let [field] ← result.mvarId!.applyConst (if side then `Or.inr else `Or.inl) { newGoals := .all }
    | throwError "Unable to apply disjunction introduction."
  unless ← isDefEq (← field.getType) inputType do
    throwError "The hypothesis has type {inputType}, which does not match the selected side of {target}. Specify the intended result with ': P ∨ Q', and choose 'left' or 'right' to match that side."
  field.assign input
  let next ← noteRuleOutputs goal #[{proof := ← instantiateMVars result, type := target}]
    patterns `h
  return next ++ missing

private partial def fillAndInputs (goal : MVarId) (inputs : Array Expr)
    (cursor : Nat := 0) (fuel : Nat := 32) : MetaM Nat := goal.withContext do
  if cursor < inputs.size then
    let saved ← saveState
    if ← isDefEq (← goal.getType) (← inferType inputs[cursor]!) then
      goal.assign inputs[cursor]!
      return cursor + 1
    saved.restore
  if fuel == 0 then throwError "Conjunction construction exceeded its depth limit."
  unless (← whnf (← goal.getType)).isAppOfArity `And 2 do
    throwError "An input does not match the required conjunct."
  let fields ← goal.applyConst `And.intro { newGoals := .all }
  fields.foldlM (fun cursor field => fillAndInputs field inputs cursor (fuel - 1)) cursor

def conjunctionRuleAt (goal : MVarId) (inputs : Array FVarId)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  let types ← inputs.mapM fun h => do instantiateMVars (← h.getType)
  unless ← types.allM (fun type => do isProp type) do throwError "Conjunction introduction requires proposition proofs."
  let target ← if let some resultSyntax := target? then Term.elabType resultSyntax
    else inferredBundleType types true
  unless (← whnf target).isAppOfArity `And 2 do throwError "The result type must be a conjunction."
  let result ← mkFreshExprSyntheticOpaqueMVar target
  let consumed ← fillAndInputs result.mvarId! (inputs.map mkFVar)
  unless consumed == inputs.size do throwError "Some input proofs were not used as conjuncts."
  noteRuleOutputs goal #[{proof := ← instantiateMVars result, type := target}] patterns `h

def existenceRuleAt (goal : MVarId) (witness : Syntax) (hyp : FVarId)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  let target ← if let some resultSyntax := target? then Term.elabType resultSyntax else goal.getType
  let target ← whnf target
  unless target.isAppOfArity `Exists 2 do
    throwError "Specify an existential result type after ':', or use an existential current goal."
  let value ← Term.elabTermEnsuringType witness target.getAppArgs[0]!
  let result ← constructFromInputs target #[value, mkFVar hyp]
  noteRuleOutputs goal #[{proof := result, type := target}] patterns `h


/-- Turn native case contexts into typed handler obligations in the original context. -/
def casesGoalRule (goal : MVarId) (sourceType : Expr)
    (patterns : Array RulePattern) : TacticM (List MVarId) := goal.withContext do
  let reduced ← whnf sourceType
  let .const head _ := reduced.getAppFn
    | throwError "Case analysis requires an inductive source type."
  let some (.inductInfo info) := (← getEnv).find? head
    | throwError "Case analysis requires an inductive source type."
  unless info.numIndices == 0 do
    throwError "Indexed case analysis needs an explicit elimination theorem; use apply."
  let context := (← getLCtx).getFVarIds
  let target ← goal.getType
  let (bridge, handlers) ← withLocalDeclD `source sourceType fun source => do
    let mut handlers := []
    let body ← mkFreshExprSyntheticOpaqueMVar target
    let branches ← body.mvarId!.cases source.fvarId!
    for branch in branches do
      let handlerType ← branch.mvarId.withContext do
        mkForallFVars branch.fields (← branch.mvarId.getType)
      if (handlerType.find? fun e => e.isFVar && !context.contains e.fvarId!).isSome then
        throwError "The branch depends on an unsupported local context."
      let handler ← goal.withContext do mkFreshExprSyntheticOpaqueMVar handlerType
      handler.mvarId!.setTag (.mkSimple (branch.ctorName.getD `branch).getString!)
      branch.mvarId.assign (mkAppN handler branch.fields)
      handlers := handlers ++ [handler.mvarId!]
    let body ← instantiateMVars body
    return (← mkLambdaFVars #[source] body, handlers)
  let source ← mkFreshExprSyntheticOpaqueMVar sourceType
  source.mvarId!.setTag `source
  goal.assign (mkApp bridge source)
  nameRuleGoals (source.mvarId! :: handlers) patterns

def casesRuleAtMany (goal : MVarId) (inputs : Array FVarId)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  unless !inputs.isEmpty do throwError "Supply the source and its case handlers."
  let target ← if let some resultSyntax := target? then Term.elabType resultSyntax else goal.getType
  let result ← mkFreshExprSyntheticOpaqueMVar target
  let sourceType ← inputs[0]!.getType
  let obligations ← casesGoalRule result.mvarId! sourceType #[]
  unless obligations.length == inputs.size do
    throwError "Expected the source and {obligations.length - 1} case handler(s)."
  for obligation in obligations, input in inputs do
    obligation.withContext do
      unless ← isDefEq (← obligation.getType) (← input.getType) do
        throwError "The source or a case handler has the wrong type."
      obligation.assign (mkFVar input)
  noteRuleOutputs goal #[{ proof := ← instantiateMVars result, type := target }] patterns `h


private partial def wlogForwardProof (restricted negative : Expr) (fuel := 32) : MetaM Expr := do
  if fuel == 0 then throwError "Generalized case analysis exceeded its depth limit."
  let .forallE name domain _ info ← whnf (← inferType restricted)
    | throwError "The restricted proof must conclude with a condition implying the result."
  if ← isProp domain then
    return ← mkAppM `Classical.byCases #[restricted, negative]
  withLocalDecl name info domain fun x => do
    let negativeType ← whnf (← inferType negative)
    let .forallE _ negativeDomain _ _ := negativeType
      | throwError "The reduction proof has incompatible generalized variables."
    unless ← isDefEq domain negativeDomain do
      throwError "The reduction proof has incompatible generalized variables."
    let proof ← wlogForwardProof (mkApp restricted x) (mkApp negative x) (fuel - 1)
    mkLambdaFVars #[x] proof

def wlogRuleAt (goal : MVarId) (inputs : Array FVarId)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  unless inputs.size == 2 do throwError "Supply the restricted proof and its reduction proof."
  let restricted := mkFVar inputs[0]!
  let reduction := mkFVar inputs[1]!
  let .forallE _ expected _ _ ← whnf (← inferType reduction)
    | throwError "The reduction proof must take the restricted proof as an argument."
  unless ← isDefEq expected (← inferType restricted) do
    throwError "The reduction proof does not accept this restricted proof."
  let proof ← wlogForwardProof restricted (mkApp reduction restricted)
  let type ← inferType proof
  if let some resultSyntax := target? then
    unless ← isDefEq type (← Term.elabType resultSyntax) do throwError "The result type does not match."
  noteRuleOutputs (← markClassicalGoal goal) #[{proof, type}] patterns `h

def inductionRuleAt (goal : MVarId) (inputs : Array FVarId)
    (patterns : Array RulePattern) (target? : Option Syntax) : TacticM (List MVarId) :=
    goal.withContext do
  unless inputs.size == 2 do throwError "Supply the zero case and the successor step."
  let type ← if let some resultSyntax := target? then Term.elabType resultSyntax
  else do
    let .forallE name domain body info ← whnf (← inputs[1]!.getType)
      | throwError "The successor step must quantify over a natural number."
    unless ← isDefEq domain (mkConst `Nat) do
      throwError "The induction interface currently supports natural numbers."
    withLocalDecl name info domain fun n => do
      let .forallE _ inductionHypothesis _ _ ← whnf (body.instantiate1 n)
        | throwError "The successor step must take the induction hypothesis."
      mkForallFVars #[n] inductionHypothesis
  let .forallE _ domain _ _ ← whnf type
    | throwError "The result type must quantify over a natural number."
  unless ← isDefEq domain (mkConst `Nat) do
    throwError "The induction interface currently supports natural numbers."
  let context := (← getLCtx).getFVarIds
  let result ← mkFreshExprSyntheticOpaqueMVar type
  let (major, body) ← result.mvarId!.intro `n
  let branches ← body.induction major `Nat.rec
  unless branches.size == inputs.size do throwError "The induction rule has an unexpected branch count."
  for branch in branches, input in inputs do
    let handlerType ← branch.mvarId.withContext do
      mkForallFVars branch.fields (← branch.mvarId.getType)
    if (handlerType.find? fun e => e.isFVar && !context.contains e.fvarId!).isSome then
      throwError "The induction step has unsupported local dependencies."
    unless ← isDefEq handlerType (← input.getType) do
      throwError "The zero case or successor step has the wrong type."
    branch.mvarId.assign (mkAppN (mkFVar input) branch.fields)
  let proof ← instantiateMVars result
  if proof.hasExprMVar then throwError "The induction proof contains unresolved dependencies."
  noteRuleOutputs goal #[{proof, type}] patterns `h


/-- Introduction adds one binder and constructs its body from a proof or a pointwise family. -/
def introRuleAt (goal : MVarId) (input : FVarId) (patterns : Array RulePattern)
    (target? : Option Syntax) : TacticM (List MVarId) := goal.withContext do
  let type ← if let some resultSyntax := target? then Term.elabType resultSyntax else goal.getType
  unless (← whnf type).isForall do
    throwError "Specify a function or implication result type after ':'."
  let result ← mkFreshExprSyntheticOpaqueMVar type
  let (argument, body) ← result.mvarId!.intro `argument
  let source := mkFVar input
  let saved ← saveState
  let supplied ← body.withContext do
    isDefEq (← inferType source) (← body.getType)
  if supplied then body.assign source
  else
    saved.restore
    let applied? ← body.withContext do
      let .forallE _ domain _ _ ← whnf (← inferType source) | return none
      unless ← isDefEq domain (← argument.getType) do return none
      let applied := mkApp source (mkFVar argument)
      unless ← isDefEq (← inferType applied) (← body.getType) do return none
      return some applied
    if let some proof := applied? then body.assign proof
    else
      let missing ← body.apply source { newGoals := .all }
      unless missing.isEmpty do
        throwError "The supplied proof does not establish the body for the introduced argument."
  let proof ← instantiateMVars result
  noteRuleOutputs goal #[{proof, type}] patterns `h

end Ample.Automation

namespace Ample
open Ample.Automation

/-- `apply rule at hp with hq` applies `rule` to a hypothesis `hp` and records the result as `hq`.
For example, `rule : P → Q` and `hp : P` give `hq : Q`.
Use `apply rule at hp hq with hr` to supply multiple arguments in order.
Missing premises become goals before the continuation using the new fact. Supplying `with` retains the input hypotheses. -/
scoped syntax (name := ruleApplyAt) (priority := high)
  "apply " term " at" (ppSpace colGt ident)+ (" with" (ppSpace colGt ruleOutput)+)? : tactic
/-- `apply rule with first second` matches the rule conclusion to the current goal and leaves its premises as new goals.
Goal order is the native Lean `apply` order; `with` names goals in that order.
Use `case first => ...` to select a goal, or `with ⟨first, second⟩` to decompose one grouped premise. -/
scoped syntax (name := ruleApplyGoal) (priority := high)
  "apply " term " with" (ppSpace colGt ruleOutput)+ : tactic
/-- `constructor with first second` applies a constructor and leaves its fields as named goals.
For `P ∧ Q`, the resulting goals are `first : P` and `second : Q`.
Select them with `case first => ...`; a tuple pattern `⟨...⟩` can further decompose one grouped field. -/
scoped syntax (name := ruleConstructor) (priority := high)
  "constructor" " with" (ppSpace colGt ruleOutput)+ : tactic

@[tactic ruleApplyAt] def evalRuleApplyAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let rule ← elabTermForApply stx[1]
      let hypotheses ← stx[3].getArgs.mapM elabAsFVar
      let patterns ← if stx[4].isNone then pure #[] else
        stx[4][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      replaceMainGoal (← applyRuleAtMany rule hypotheses patterns)
  catch e => saved.restore; throw e

@[tactic ruleApplyGoal] def evalRuleApplyGoal : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let rule ← elabTermForApply stx[1]
      let patterns ← stx[3].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      replaceMainGoal (← nameRuleGoals (← (← getMainGoal).apply rule) patterns)
  catch e => saved.restore; throw e

@[tactic ruleConstructor] def evalRuleConstructor : Tactic := fun stx => do
  let saved ← saveState
  try
    let patterns ← stx[2].getArgs.mapM fun p => parseRulePattern ⟨p⟩
    let goal ← getMainGoal
    let (next, constructors) ← goal.constructorCore { newGoals := .all }
    unless constructors.size == 1 do
      throwError "Multiple constructors match this goal. Use apply with an explicit constructor."
    replaceMainGoal (← nameRuleGoals next patterns)
  catch e => saved.restore; throw e


/-- `constructor at hp hq with h` constructs a new value or proof from the supplied fields.
For example, `hp : P` and `hq : Q` give `h : P ∧ Q`.
Specify the result type when needed: `constructor at hp hq with h : P ∧ Q`. -/
scoped syntax (name := ruleConstructorAt) (priority := high)
  "constructor" " at" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic
/-- `rcases at h with pattern` decomposes a hypothesis and splits cases according to a pattern.
It is a compatibility spelling of `rcases h with pattern`. -/
scoped syntax (name := ruleRCasesAt) (priority := high)
  "rcases" " at " ident (" with " rcasesPat)? : tactic
/-- `rcases goals first second with combined` replaces selected goals by a goal for a bundled value or proof.
Nested product structures may be opened to connect the individual goals.
Selected goals must share a local context and have no unresolved witness dependencies. -/
scoped syntax (name := ruleRCasesGoals) (priority := high)
  "rcases" &"goals" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic

@[tactic ruleConstructorAt] def evalRuleConstructorAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let inputs ← stx[2].getArgs.mapM elabAsFVar
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[4].isNone then none else some stx[4][1]
      replaceMainGoal (← constructorRuleAt (← getMainGoal) inputs patterns target?)
  catch e => saved.restore; throw e

@[tactic ruleRCasesAt] def evalRuleRCasesAt : Tactic := fun stx => do
  let saved ← saveState
  try
    let hypothesis : TSyntax `ident := ⟨stx[2]⟩
    if stx[3].isNone then
      evalTactic (← `(tactic| rcases $hypothesis:ident))
    else
      let pattern : TSyntax `rcasesPat := ⟨stx[3][1]⟩
      evalTactic (← `(tactic| rcases $hypothesis:ident with $pattern:rcasesPat))
  catch e => saved.restore; throw e

@[tactic ruleRCasesGoals] def evalRuleRCasesGoals : Tactic := fun stx => do
  let saved ← saveState
  try
    let selected ← selectRuleGoals (stx[2].getArgs.map (·.getId))
    let patterns ← if stx[3].isNone then pure #[] else
      stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
    let target? := if stx[4].isNone then none else some stx[4][1]
    combineConstructorGoals selected target? patterns true
  catch e => saved.restore; throw e


/-- `cases at h` splits into cases according to the constructors of the hypothesis or value `h`.
It is a compatibility spelling of `cases h`; each branch receives its constructor arguments. -/
scoped syntax (name := ruleCasesAt) (priority := high)
  "cases" " at " ident (Lean.Parser.Tactic.inductionAlts)? : tactic
/-- `cases goals first second with combined` combines goals obtained by decomposing a single constructor.
The selected goals must be independent and share a local context.
For a conjunction or product, the basic spelling is also `unpack goals first second`. -/
scoped syntax (name := ruleCasesGoals) (priority := high)
  "cases" &"goals" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic

@[tactic ruleCasesAt] def evalRuleCasesAt : Tactic := fun stx => do
  let saved ← saveState
  try
    let hypothesis : TSyntax `ident := ⟨stx[2]⟩
    if stx[3].isNone then
      evalTactic (← `(tactic| cases $hypothesis:ident))
    else
      let alternatives : TSyntax `Lean.Parser.Tactic.inductionAlts := ⟨stx[3][0]⟩
      evalTactic (← `(tactic| cases $hypothesis:ident $alternatives:inductionAlts))
  catch e => saved.restore; throw e

@[tactic ruleCasesGoals] def evalRuleCasesGoals : Tactic := fun stx => do
  let saved ← saveState
  try
    let selected ← selectRuleGoals (stx[2].getArgs.map (·.getId))
    let patterns ← if stx[3].isNone then pure #[] else
      stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
    let target? := if stx[4].isNone then none else some stx[4][1]
    combineConstructorGoals selected target? patterns
  catch e => saved.restore; throw e


/-- `unpack h with ⟨hp, hq⟩` opens one layer of a single-constructor value or proof, such as a pair or conjunction.
For example, `h : P ∧ Q` yields `hp : P` and `hq : Q`.
For a local variable, the original variable is eliminated and dependent hypotheses and the goal are updated, as with `rcases`.
For a structure-valued expression, the field names denote its projections without eliminating variables inside the expression.
Use `cases` for a choice of constructors, or `rcases` for nested pattern decomposition. -/
scoped syntax (name := ruleUnpack) (priority := high)
  "unpack " term (" with " ruleOutput)? : tactic
/-- `unpack goals first second with combined` bundles selected goals into a conjunction or product goal.
For example, goals `first : P` and `second : Q` combine into `P ∧ Q`.
Only independent goals in the same local context can be combined. An optional `: ...` specifies the bundle type. -/
scoped syntax (name := ruleUnpackGoals) (priority := high)
  "unpack" &"goals" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic

@[tactic ruleUnpack] def evalRuleUnpack : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let value ← Term.elabTerm stx[1] none
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      let (hypothesis, goal) ← if value.isFVar then
        pure (value.fvarId!, ← getMainGoal)
      else do
        let name ← mkFreshUserName `source
        let type ← inferType value
        if ← isProp type then (← getMainGoal).note name value type
        else (← (← getMainGoal).define name type value).intro1P
      let pattern? ← if stx[2].isNone then pure none else
        pure (some (← parseRulePattern ⟨stx[2][1]⟩))
      replaceMainGoal (← unpackRuleHypothesis goal hypothesis pattern? value.isFVar)
  catch e => saved.restore; throw e

@[tactic ruleUnpackGoals] def evalRuleUnpackGoals : Tactic := fun stx => do
  let saved ← saveState
  try
    let selected ← selectRuleGoals (stx[2].getArgs.map (·.getId))
    let patterns ← if stx[3].isNone then pure #[] else
      stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
    let target? := if stx[4].isNone then none else some stx[4][1]
    combineConstructorGoals selected target? patterns
  catch e => saved.restore; throw e


/-- `left at hp with h : P ∨ Q` constructs the left alternative using `hp : P`, giving `h : P ∨ Q`.
Without a result type, the other proposition is inferred from the current goal or left as a proposition-selection goal. -/
scoped syntax (name := ruleLeftAt) (priority := high)
  "left" " at " ident (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic
/-- `right at hq with h : P ∨ Q` constructs the right alternative using `hq : Q`, giving `h : P ∨ Q`.
Without a result type, the other proposition is inferred from the current goal or left as a proposition-selection goal. -/
scoped syntax (name := ruleRightAt) (priority := high)
  "right" " at " ident (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic
/-- `and_intros at hp hq hr with h` bundles supplied proofs into a conjunction.
For example, `hp : P`, `hq : Q`, and `hr : R` give `h : P ∧ Q ∧ R`.
Specify a result proposition after `: ...` when a different grouping is needed. -/
scoped syntax (name := ruleAndIntrosAt) (priority := high)
  "and_intros" " at" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic
/-- `exists a at ha with h : ∃ x, P x` constructs an existential proof from a witness `a` and a proof `ha : P a`.
The result type can be omitted when the current goal is the intended existential proposition.
The result `h` is a proof of existence, not a subtype element. -/
scoped syntax (name := ruleExistsAt) (priority := high)
  "exists " term " at " ident
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic

@[tactic ruleLeftAt, tactic ruleRightAt] def evalDisjunctionRuleAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let hyp ← elabAsFVar stx[2]
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[4].isNone then none else some stx[4][1]
      replaceMainGoal (← disjunctionRuleAt (← getMainGoal) hyp
        (stx.getKind == ``ruleRightAt) patterns target?)
  catch e => saved.restore; throw e

@[tactic ruleAndIntrosAt] def evalConjunctionRuleAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let inputs ← stx[2].getArgs.mapM elabAsFVar
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[4].isNone then none else some stx[4][1]
      replaceMainGoal (← conjunctionRuleAt (← getMainGoal) inputs patterns target?)
  catch e => saved.restore; throw e

@[tactic ruleExistsAt] def evalExistenceRuleAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let hyp ← elabAsFVar stx[3]
      let patterns ← if stx[4].isNone then pure #[] else
        stx[4][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[5].isNone then none else some stx[5][1]
      replaceMainGoal (← existenceRuleAt (← getMainGoal) stx[1] hyp patterns target?)
  catch e => saved.restore; throw e


/-- `cases goal T` requests a value or proof of `T` and one handler deriving the current conclusion for each constructor.
For a goal `R`, `cases goal (P ∨ Q)` leaves goals `P ∨ Q`, `P → R`, and `Q → R`.
Use `with source first second` to name them. -/
scoped syntax (name := ruleCasesGoal) (priority := high)
  "cases" &"goal" ppSpace term (" with" (ppSpace colGt ruleOutput)+)? : tactic
/-- `cases at h fromP fromQ with result` combines a source with handlers for its constructors.
For example, `h : P ∨ Q`, `fromP : P → R`, and `fromQ : Q → R` yield `result : R`.
Specify an otherwise ambiguous result after `: R`. -/
scoped syntax (name := ruleCasesApplyAt) (priority := high)
  "cases" " at" (ppSpace colGt ident)+
  " with" (ppSpace colGt ruleOutput)+ (" : " term)? : tactic

@[tactic ruleCasesGoal] def evalRuleCasesGoal : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let type ← Term.elabType stx[2]
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      replaceMainGoal (← casesGoalRule (← getMainGoal) type patterns)
  catch e => saved.restore; throw e

@[tactic ruleCasesApplyAt] def evalRuleCasesApplyAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let inputs ← stx[2].getArgs.mapM elabAsFVar
      let patterns ← stx[4].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[5].isNone then none else some stx[5][1]
      replaceMainGoal (← casesRuleAtMany (← getMainGoal) inputs patterns target?)
  catch e => saved.restore; throw e


/-- `by_contra at h with result` applies proof by contradiction to `h : ¬ P → False`, producing `result : P`.
It creates a fact from an existing implication, rather than introducing a negated hypothesis in the current goal. -/
scoped syntax (name := ruleByContraAt) (priority := high)
  "by_contra" " at" (ppSpace colGt ident)+ (" with" (ppSpace colGt ruleOutput)+)? : tactic
/-- `by_cases at positive negative with result` combines implications for a proposition and its negation.
Given `positive : P → R` and `negative : ¬ P → R`, it produces `result : R`. -/
scoped syntax (name := ruleByCasesAt) (priority := high)
  "by_cases" " at" (ppSpace colGt ident)+ (" with" (ppSpace colGt ruleOutput)+)? : tactic
/-- `wlog at restricted reduction with result` combines a restricted proof and a reduction to its condition.
The first input proves the conditional result; the second uses that proof to handle the remaining case.
An optional `: ...` specifies the result type. -/
scoped syntax (name := ruleWlogAt) (priority := high)
  "wlog" " at" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic
/-- `induction at zeroCase successorStep with result` assembles a natural-number induction proof.
Given `zeroCase : P 0` and `successorStep : ∀ n, P n → P (n + 1)`, it produces `result : ∀ n, P n`.
This forward interface currently supports induction on natural numbers. -/
scoped syntax (name := ruleInductionAt) (priority := high)
  "induction" " at" (ppSpace colGt ident)+
  (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic

@[tactic ruleByContraAt, tactic ruleByCasesAt] def evalClassicalRuleAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let inputs ← stx[2].getArgs.mapM elabAsFVar
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let principle := if stx.getKind == ``ruleByCasesAt then `Classical.byCases
        else `Classical.byContradiction
      let next ← applyRuleAtMany (← mkConstWithFreshMVarLevels principle) inputs patterns
      replaceMainGoal (← next.mapM (fun g => do markClassicalGoal g))
  catch e => saved.restore; throw e

@[tactic ruleWlogAt, tactic ruleInductionAt] def evalGeneralizedRuleAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let inputs ← stx[2].getArgs.mapM elabAsFVar
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[4].isNone then none else some stx[4][1]
      let next ← if stx.getKind == ``ruleWlogAt then
        wlogRuleAt (← getMainGoal) inputs patterns target?
      else inductionRuleAt (← getMainGoal) inputs patterns target?
      replaceMainGoal next
  catch e => saved.restore; throw e


/-- `intro at hq with h : P → Q` constructs an implication using the supplied `hq : Q` for its body.
For a universal statement, supply a proof valid at an arbitrary input; a fact about one element is not generalized.
When omitted, the result type is inferred from the current goal. -/
scoped syntax (name := ruleIntroAt) (priority := high)
  "intro" " at " ident (" with" (ppSpace colGt ruleOutput)+)? (" : " term)? : tactic
/-- `apply goal G` specifies a proposition to use in place of an already proved rule.
It leaves a proof goal for `G` and any premises needed to apply that proof to the current goal.
For example, on a goal `P a`, `apply goal (∀ x, P x)` requests the universal statement. -/
scoped syntax (name := ruleApplyGoalType) (priority := high)
  "apply" &"goal" ppSpace term (" with" (ppSpace colGt ruleOutput)+)? : tactic

@[tactic ruleIntroAt] def evalRuleIntroAt : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let input ← elabAsFVar stx[2]
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      let target? := if stx[4].isNone then none else some stx[4][1]
      replaceMainGoal (← introRuleAt (← getMainGoal) input patterns target?)
  catch e => saved.restore; throw e

@[tactic ruleApplyGoalType] def evalRuleApplyGoalType : Tactic := fun stx => do
  let saved ← saveState
  try
    withMainContext do
      let type ← Term.elabType stx[2]
      let source ← mkFreshExprSyntheticOpaqueMVar type
      source.mvarId!.setTag `rule
      let obligations ← (← getMainGoal).apply source { newGoals := .all }
      let obligations := source.mvarId! :: obligations.filter (· != source.mvarId!)
      let patterns ← if stx[3].isNone then pure #[] else
        stx[3][1].getArgs.mapM fun p => parseRulePattern ⟨p⟩
      replaceMainGoal (← nameRuleGoals obligations patterns)
  catch e => saved.restore; throw e

end Ample

