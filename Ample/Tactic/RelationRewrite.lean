import Ample.Tactic.Rules
import Lean.Elab.Tactic.Rewrite
import Lean.Meta.Tactic.Assumption

/-!
Certificates for relation-preserving operations. A relation proof never changes
Lean's equality: rewriting propositions requires a proof of their iff.
Mathematical modules register laws/actions with `ample_rewrite`.
-/

namespace Ample.Rewriting

structure Laws {α : Type u} (R : α → α → Prop) : Prop where
  refl : ∀ a, R a a
  symm : ∀ {a b}, R a b → R b a
  trans : ∀ {a b c}, R a b → R b c → R a c

structure SymmetricTransitive {α : Type u} (R : α → α → Prop) : Prop where
  symm : ∀ {a b}, R a b → R b a
  trans : ∀ {a b c}, R a b → R b c → R a c

structure Action {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop) (f : α → β) : Prop where
  map : ∀ {a b}, R a b → S (f a) (f b)

structure Action2 {α : Type u} {β : Type v} {γ : Type w}
    (R : α → α → Prop) (S : β → β → Prop)
    (T : γ → γ → Prop) (f : α → β → γ) : Prop where
  map : ∀ {a b c d}, R a b → S c d → T (f a c) (f b d)

@[ample_rewrite] theorem iffLaws : Laws Iff :=
  ⟨Iff.refl, Iff.symm, Iff.trans⟩

@[ample_rewrite] theorem eqLaws (α : Type u) : Laws (@Eq α) :=
  ⟨Eq.refl, Eq.symm, Eq.trans⟩

@[ample_rewrite] theorem relationAction {α : Type u}
    (R : α → α → Prop) (laws : Laws R) : Action2 R R Iff R := by
  constructor
  intro a b c d hab hcd
  constructor
  · intro hac
    exact laws.trans (laws.trans (laws.symm hab) hac) hcd
  · intro hbd
    exact laws.trans (laws.trans hab hbd) (laws.symm hcd)

@[ample_rewrite] theorem symmetricTransitiveOfLaws {α : Type u}
    (R : α → α → Prop) (laws : Laws R) : SymmetricTransitive R :=
  ⟨laws.symm, laws.trans⟩

@[ample_rewrite] theorem symmetricTransitiveOfProofs {α : Type u}
    (R : α → α → Prop)
    (hs : ∀ a b, R a b → R b a)
    (ht : ∀ a b c, R a b → R b c → R a c) : SymmetricTransitive R :=
  ⟨hs _ _, ht _ _ _⟩

@[ample_rewrite] theorem relationLeftAction {α : Type u}
    (R : α → α → Prop) (laws : SymmetricTransitive R) (c : α) :
    Action R Iff (fun a => R a c) :=
  ⟨fun hab => ⟨fun hac => laws.trans (laws.symm hab) hac, fun hbc => laws.trans hab hbc⟩⟩

@[ample_rewrite] theorem relationRightAction {α : Type u}
    (R : α → α → Prop) (laws : SymmetricTransitive R) (c : α) :
    Action R Iff (fun a => R c a) :=
  ⟨fun hab => ⟨fun hca => laws.trans hca hab, fun hcb => laws.trans hcb (laws.symm hab)⟩⟩

@[ample_rewrite] theorem andAction : Action2 Iff Iff Iff And :=
  ⟨fun hp hq => and_congr hp hq⟩

@[ample_rewrite] theorem orAction : Action2 Iff Iff Iff Or :=
  ⟨fun hp hq => or_congr hp hq⟩

@[ample_rewrite] theorem notAction : Action Iff Iff Not :=
  ⟨fun hp => not_congr hp⟩

@[ample_rewrite] theorem iffAction : Action2 Iff Iff Iff Iff :=
  ⟨fun hp hq => iff_congr hp hq⟩

@[ample_rewrite] theorem existsAction (α : Type u) :
    Action (fun P Q : α → Prop => ∀ x, P x ↔ Q x) Iff Exists :=
  ⟨fun hp => exists_congr hp⟩

end Ample.Rewriting

/-- An explicit reversible context for a relation rewrite. Its condition is an
ordinary proof obligation; it defaults to `True`. Use the same predicate for
both `P` and `Q` when supplying a context for `rw [h] using context`. -/
structure Ample.RewriteContext {α : Type u} (R : α → α → Prop)
    (P Q : α → Prop) where
  Condition : Prop := True
  transport : Condition → ∀ {a b}, R a b → (P a ↔ Q b)

open Lean Meta Elab Tactic

namespace Ample.Automation.Relational

initialize registerTraceClass `Ample.rewrite

register_option ample.rewrite.maxDepth : Nat := {
  defValue := 10
  descr := "Maximum comparison depth when constructing a reversible relation context."
}

register_option ample.rewrite.maxSteps : Nat := {
  defValue := 128
  descr := "Maximum certificate/comparison steps in a relation rewrite search."
}

private def certificateKind (type : Expr) : Bool :=
  type.isAppOf ``Rewriting.Laws || type.isAppOf ``Rewriting.Action || type.isAppOf ``Rewriting.Action2
    || type.isAppOf ``Rewriting.SymmetricTransitive

private def assumption? (type : Expr) : MetaM (Option Expr) := do
  for h in ← getPropHyps do
    let saved ← saveState
    if ← isDefEq (← h.getType) type then return some (mkFVar h)
    saved.restore
  return none

private def spend (budget : IO.Ref Nat) : MetaM Bool := do
  if (← budget.get) == 0 then return false
  budget.modify (· - 1)
  return true

-- Only registered certificate constructors may introduce side conditions.
-- Failure to preserve an operation is not turned into a new equality goal.
private structure Candidate where
  proof : Expr
  obligations : List MVarId
  state : Meta.SavedState

private partial def certificates (type : Expr) (depth : Nat)
    (budget : IO.Ref Nat) : MetaM (Array Candidate) := do
  if depth == 0 || !(← spend budget) then return #[]
  let start ← saveState
  let mut found := #[]
  for h in ← getPropHyps do
    if certificateKind (← h.getType) && (← isDefEq (← h.getType) type) then
      found := found.push ⟨mkFVar h, [], ← saveState⟩
    start.restore
  for name in ← labelled `ample_rewrite do
    let saved ← saveState
    let candidate? ← try
      let proof ← mkConstWithFreshMVarLevels name
      let (args, _, result) ← forallMetaTelescopeReducing (← inferType proof)
      if !certificateKind result || !(← isDefEq result type) then pure none
      else
        let mut obligations := []
        let mut valid := true
        for arg in args do
          let arg ← instantiateMVars arg
          if arg.isMVar then
            let premise ← instantiateMVars (← inferType arg)
            if !(← isProp premise) || premise.hasExprMVar then
              valid := false
              break
            if let some h ← assumption? premise then arg.mvarId!.assign h
            else if certificateKind premise then
              let choices ← certificates premise (depth - 1) budget
              match choices.find? (·.obligations.isEmpty) <|> choices[0]? with
              | some candidate =>
                candidate.state.restore
                arg.mvarId!.assign candidate.proof
                obligations := obligations ++ candidate.obligations
              | none =>
                valid := false
                break
            else if type.isAppOf ``Rewriting.Laws || type.isAppOf ``Rewriting.SymmetricTransitive then
              -- Establish relation laws from known proofs, rather than inventing
              -- obligations such as reflexivity/symmetry of an arbitrary function.
              valid := false
              break
            else
              arg.mvarId!.setKind .syntheticOpaque
              obligations := obligations ++ [arg.mvarId!]
        if valid then pure (some (← instantiateMVars (mkAppN proof args), obligations))
        else pure none
    catch error =>
      trace[Ample.rewrite] "Certificate candidate failed: {error.toMessageData}"
      pure none
    match candidate? with
    | some (proof, obligations) => found := found.push ⟨proof, obligations, ← saveState⟩
    | none => pure ()
    saved.restore
  return found

private def certificate (type : Expr) (depth : Nat)
    (budget : IO.Ref Nat) : MetaM (Option (Expr × List MVarId)) := do
  let choices ← certificates type depth budget
  match choices.find? (·.obligations.isEmpty) <|> choices[0]? with
  | none => return none
  | some candidate =>
    candidate.state.restore
    return some (candidate.proof, candidate.obligations)

private def relationType (α : Expr) : MetaM Expr := do
  mkArrow α (← mkArrow α (mkSort .zero))

private def comparison (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let args := type.getAppArgs
  if args.size < 2 then return none
  let left := args[args.size-2]!.headBeta
  let right := args[args.size-1]!.headBeta
  unless ← isDefEq (← inferType left) (← inferType right) do return none
  let relation := mkAppN type.getAppFn (args.extract 0 (args.size-2))
  unless ← isDefEq (← inferType relation) (← relationType (← inferType left)) do return none
  return some (relation, left, right)

private partial def proveComparison (goal : MVarId) (depth : Nat)
    (budget : IO.Ref Nat) (source : Expr)
    (missing : IO.Ref (Array String)) : MetaM (Option (List MVarId)) := goal.withContext do
  if depth == 0 || !(← spend budget) then return none
  let target := (← instantiateMVars (← goal.getType)).headBeta
  if ← isDefEq (← inferType source) target then
    goal.assign source
    return some []
  if let some proof ← assumption? target then
    goal.assign proof
    return some []
  if target.isForall then
    let (_, next) ← goal.intro1
    return ← proveComparison next (depth - 1) budget source missing
  let some (R, left, right) ← comparison target | return none
  if ← isDefEq left right then
    let lawsType ← mkAppM ``Rewriting.Laws #[R]
    if let some (laws, extra) ← certificate lawsType depth budget then
      goal.assign (← mkAppM ``Rewriting.Laws.refl #[laws, left])
      return some extra
  if R.isConstOf ``Iff && left.isForall && right.isForall then
    let saved ← saveState
    let logical? ← try
      let leftDomain := left.bindingDomain!
      let rightDomain := right.bindingDomain!
      let leftBody := left.bindingBody!
      let rightBody := right.bindingBody!
      if ← isDefEq leftDomain rightDomain then
        let statement := mkForall `_element .default leftDomain (mkIff leftBody rightBody)
        let h ← mkFreshExprMVar statement
        match ← proveComparison h.mvarId! (depth-1) budget source missing with
        | none => pure none
        | some pending =>
          goal.assign (← mkAppM ``forall_congr' #[h])
          pure (some pending)
      else if (← isProp leftDomain) && (← isProp rightDomain) &&
          !leftBody.hasLooseBVars && !rightBody.hasLooseBVars then
        let hp ← mkFreshExprMVar (mkIff leftDomain rightDomain)
        let hq ← mkFreshExprMVar (mkIff leftBody rightBody)
        match ← proveComparison hp.mvarId! (depth-1) budget source missing,
            ← proveComparison hq.mvarId! (depth-1) budget source missing with
        | some p, some q =>
          goal.assign (← mkAppM ``imp_congr #[hp, hq])
          pure (some (p ++ q))
        | _, _ => pure none
      else pure none
    catch error =>
      trace[Ample.rewrite] "Logical context failed: {error.toMessageData}"
      pure none
    match logical? with
    | some pending => return some pending
    | none => saved.restore
  -- Structural application rules cover operations with one or two arguments.
  -- The function and its fixed type/instance arguments must agree on both sides.
  for arity in [2, 1] do
    let leftArgs := left.getAppArgs
    let rightArgs := right.getAppArgs
    if leftArgs.size < arity || rightArgs.size < arity then continue
    let saved ← saveState
    let attempt? ← try
      let mut selected := #[]
      let mut f := mkAppN left.getAppFn (leftArgs.extract 0 (leftArgs.size-arity))
      let mut g := mkAppN right.getAppFn (rightArgs.extract 0 (rightArgs.size-arity))
      if arity == 1 then
        if leftArgs.size != rightArgs.size || !(← isDefEq left.getAppFn right.getAppFn) then
          saved.restore
          continue
        for i in [:leftArgs.size] do
          unless ← isDefEq leftArgs[i]! rightArgs[i]! do selected := selected.push i
        if selected.size != 1 then
          saved.restore
          continue
        let i := selected[0]!
        f ← withLocalDeclD `_argument (← inferType leftArgs[i]!) fun x =>
          mkLambdaFVars #[x] (mkAppN left.getAppFn (leftArgs.set! i x))
        g := f
      else selected := #[leftArgs.size-2, leftArgs.size-1]
      if !(← isDefEq f g) then pure none
      else
        let a := leftArgs[selected[0]!]!
        let inputR ← mkFreshExprMVar (← relationType (← inferType a))
        let mut relations := #[inputR]
        if arity == 2 then
          relations := relations.push (← mkFreshExprMVar (← relationType (← inferType leftArgs.back!)))
        let actionType ← if arity == 1 then mkAppM ``Rewriting.Action #[inputR, R, f]
          else mkAppM ``Rewriting.Action2 #[inputR, relations[1]!, R, f]
        let choices ← certificates actionType depth budget
        if choices.isEmpty then
          let operation := (← ppExpr f).pretty
          missing.modify fun previous => if previous.contains operation then previous else previous.push operation
          trace[Ample.rewrite] "No registered relation action for {f}"
        let mut best : Option (List MVarId × Meta.SavedState) := none
        for candidate in choices do
          candidate.state.restore
          let action := candidate.proof
          let mut pending := candidate.obligations
          let mut children := #[]
          let mut valid := true
          for i in [:arity] do
            let r ← instantiateMVars relations[i]!
            if r.hasExprMVar then
              valid := false
              break
            let position := selected[i]!
            let child ← mkFreshExprMVar (mkApp2 r leftArgs[position]! rightArgs[position]!)
            match ← proveComparison child.mvarId! (depth-1) budget source missing with
            | none =>
              valid := false
              break
            | some additional =>
              children := children.push child
              pending := pending ++ additional
          if valid then
            let projection := if arity == 1 then ``Rewriting.Action.map else ``Rewriting.Action2.map
            let proof ← mkAppM projection (#[action] ++ children)
            goal.assign proof
            if pending.isEmpty then return some pending
            if (best.map fun previous => decide (pending.length < previous.1.length)).getD true then
              best := some (pending, ← saveState)
        match best with
        | none => pure none
        | some (pending, state) =>
          state.restore
          pure (some pending)
    catch _ => pure none
    match attempt? with
    | some pending => return some pending
    | none => saved.restore
  return none

/-- Construct an equality between propositions from a certified relation
context. Return none for ordinary equality/iff/definition rewrite arguments. -/
def elabRewrite? (goal : MVarId) (expression : Expr) (rule : Syntax)
    (reverse : Bool) (config : Rewrite.Config)
    (context? : Option Syntax := none) : TacticM (Option RewriteResult) := goal.withContext do
  let source ← elabTerm rule none true
  if source.hasSyntheticSorry then throwAbortTactic
  let (args, _, type) ← forallMetaTelescopeReducing (← inferType source)
  if type.isAppOf ``Eq || type.isAppOf ``Iff then return none
  unless ← isProp type do return none
  let some (R, left, right) ← comparison type | return none
  let source := mkAppN source args
  let pattern := if reverse then right else left
  let replacement := if reverse then left else right
  if pattern.getAppFn.isMVar then
    throwError "Relation rewrite pattern is a metavariable. Supply its explicit arguments."
  unless ← isProp expression do
    throwError "A relation rewrite requires a proposition. Data values can only be rewritten by equality."
  let abstracted ← withConfig (fun old => { config, old with }) <| kabstract expression pattern config.occs
  unless abstracted.hasLooseBVars do
    throwError "No occurrence of the relation rewrite pattern was found."
  let replacement ← instantiateMVars replacement
  let R ← instantiateMVars R
  if R.hasExprMVar || replacement.hasExprMVar then
    throwError "Relation parameters or the replacement are unresolved. Supply their explicit arguments."
  let updated ← instantiateMVars (abstracted.instantiate1 replacement)
  let carrier ← inferType pattern
  let predicate := mkLambda `_rewrite_value .default carrier abstracted
  try check predicate catch error =>
    throwError "The relation rewrite context is dependent or ill-typed.\n{error.toMessageData}"
  let mut obligations := []
  for arg in args do
    let arg ← instantiateMVars arg
    if arg.isMVar then
      unless ← isProp (← inferType arg) do
        throwError "A relation rewrite argument is unresolved. Supply its explicit value."
      obligations := obligations ++ [arg.mvarId!]
  let forwardLeft := if reverse then updated else expression
  let forwardRight := if reverse then expression else updated
  let proof ← match context? with
    | some context =>
      let expected ← mkAppM ``Ample.RewriteContext #[R, predicate, predicate]
      let witness ← elabTerm context (some expected)
      let condition ← whnf (← mkAppM ``Ample.RewriteContext.Condition #[witness])
      let conditionProof ← if ← isDefEq condition (mkConst ``True) then pure (mkConst ``True.intro)
        else match ← assumption? condition with
          | some h => pure h
          | none =>
            let h ← mkFreshExprMVar condition .syntheticOpaque
            obligations := obligations ++ [h.mvarId!]
            pure h
      mkAppM ``Ample.RewriteContext.transport #[witness, conditionProof, source]
    | none =>
      let statement := mkIff forwardLeft forwardRight
      let certificateGoal ← mkFreshExprMVar statement
      let budget ← IO.mkRef (ample.rewrite.maxSteps.get (← getOptions))
      let missing ← IO.mkRef #[]
      let result ← proveComparison certificateGoal.mvarId!
        (ample.rewrite.maxDepth.get (← getOptions)) budget source missing
      let some pending := result | do
        if (← budget.get) == 0 then
          throwError "Relation rewrite search exhausted 'ample.rewrite.maxSteps'. Increase the limit or supply an explicit context with 'using'."
        let operations := "\n".intercalate (← missing.get).toList
        if operations.isEmpty then
          throwError "No reversible relation context was found. The required relation laws or argument comparisons could not be established. Supply the missing proofs or an explicit context with 'using'."
        else
          throwError "No reversible relation context was found. No registered preserving action was found for:\n{operations}\nRegister a relation action or supply an explicit context with 'using'."
      obligations := obligations ++ pending
      instantiateMVars certificateGoal
  let proof ← if reverse then mkAppM ``Iff.symm #[proof] else pure proof
  let equality ← mkAppM ``propext #[proof]
  return some { eNew := updated, eqProof := equality, mvarIds := obligations }

end Ample.Automation.Relational
