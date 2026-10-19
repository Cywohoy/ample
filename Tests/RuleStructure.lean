import Ample.Tactic.Ext

open Course

theorem merge_pair (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (a, c) = (b, d) := by
  ext : 1 with first second
  indisc goals first second with combined
  guard_target =ₛ (a, c) = (b, d)
  ext : 1 with first second
  case first => exact hab
  case second => exact hcd

theorem merge_three (a b c d e f : Nat) (hab : a = b) (hcd : c = d) (hef : e = f) :
    a = b ∧ c = d ∧ e = f := by
  constructor with first ⟨second, third⟩
  indisc goals first second third with combined
  guard_target =ₛ (a, (c, e)) = (b, (d, f))
  ext! with first second third
  case first => exact hab
  case second => exact hcd
  case third => exact hef

theorem partial_selection (a b c d e f : Nat) (hab : a = b) (hcd : c = d) (hef : e = f) :
    a = b ∧ c = d ∧ e = f := by
  constructor with first ⟨second, third⟩
  indisc goals first second with combined
  case combined =>
    ext : 1
    · exact hab
    · exact hcd
  case third => exact hef

theorem assemble_pair (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (a, c) = (b, d) := by
  ext at hab hcd with whole
  guard_hyp hab :ₛ a = b
  guard_hyp hcd :ₛ c = d
  guard_hyp whole :ₛ (a, c) = (b, d)
  exact whole

theorem pair_observe {A B : Type} (p q : A × B) (h : p = q) :
    p.1 = q.1 := by
  indisc : 1 at h with first second
  guard_hyp first :ₛ p.1 = q.1
  guard_hyp second :ₛ p.2 = q.2
  exact first

theorem separate_outputs_reject_tuple {A B : Type} (p q : A × B) (h : p = q) :
    p = q := by
  fail_if_success indisc at h with ⟨first, second⟩
  guard_hyp h :ₛ p = q
  exact h

structure PackedRecord where
  x : Nat
  y : Nat

@[ext (iff := false)] theorem packed_record_ext {p q : PackedRecord}
    (fields : p.x = q.x ∧ p.y = q.y) : p = q := by
  cases p
  cases q
  rcases fields with ⟨hx, hy⟩
  cases hx
  cases hy
  rfl

theorem packed_record_ext_iff {p q : PackedRecord} :
    p = q ↔ p.x = q.x ∧ p.y = q.y := by
  constructor
  · intro h
    cases h
    constructor <;> rfl
  · exact packed_record_ext

theorem grouped_output (p q : PackedRecord) (h : p = q) :
    p.x = q.x := by
  fail_if_success indisc at h with hx hy
  indisc : 1 at h with ⟨hx, hy⟩
  guard_hyp hx :ₛ p.x = q.x
  guard_hyp hy :ₛ p.y = q.y
  exact hx

theorem grouped_goal (p q : PackedRecord)
    (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  ext : 1 with ⟨first, second⟩
  case first => exact hx
  case second => exact hy

theorem grouped_goal_reject_flat (p q : PackedRecord) (h : p = q) : p = q := by
  fail_if_success ext with first second
  guard_target =ₛ p = q
  exact h

theorem one_layer (n : Nat) (s t : Fin n) (h : s = t) :
    (s, s) = (t, t) := by
  ext : 1 with first second
  case first =>
    guard_target =ₛ s = t
    exact h
  case second =>
    guard_target =ₛ s = t
    exact h

theorem one_layer_hyp (n : Nat) (p q : Fin n × Nat) (h : p = q) : p.1 = q.1 := by
  indisc : 1 at h with first second
  guard_hyp first :ₛ p.1 = q.1
  exact first

theorem apply_forward (P Q R : Prop) (r : P → Q → R) (hp : P) (hq : Q) : R := by
  apply (r hp) at hq with hr
  guard_hyp hq :ₛ Q
  guard_hyp hr :ₛ R
  exact hr

theorem apply_partial (P Q R : Prop) (r : P → Q → R) (hp : P) (hq : Q) : R := by
  apply r at hp
  guard_hyp hp :ₛ Q → R
  exact hp hq

theorem apply_named_goals (P Q R : Prop) (r : P → Q → R) (hp : P) (hq : Q) : R := by
  apply r with first second
  case first => exact hp
  case second => exact hq

theorem apply_grouped (P Q R : Prop) (r : (P ∧ Q) → R) (hp : P) (hq : Q) : R := by
  fail_if_success apply r with first second
  apply r with ⟨first, second⟩
  case first => exact hp
  case second => exact hq

theorem apply_result (P Q R : Prop) (r : P → Q ∧ R) (hp : P) : Q := by
  fail_if_success apply r at hp with hq hr
  apply r at hp with ⟨hq, hr⟩
  guard_hyp hp :ₛ P
  exact hq

theorem apply_existential (A : Type) (P : A → Prop)
    (r : True → ∃ x, P x) (ht : True) : ∃ x, P x := by
  apply r at ht with ⟨a, ha⟩
  guard_hyp ha :ₛ P a
  exists a

theorem reject_contexts (a b c d : Nat) (h : a = b) (k : c = d) :
    (True → a = b) ∧ (True → c = d) := by
  constructor with first second
  all_goals intro ht
  fail_if_success indisc goals first second
  case first => exact h
  case second => exact k

theorem reject_missing_name (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor with first second
  fail_if_success indisc goals first missing
  case first => exact hp
  case second => exact hq

theorem reject_non_eq (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor with first second
  fail_if_success indisc goals first second
  case first => exact hp
  case second => exact hq

theorem no_injectivity_inference (f : Nat → Nat) (a b : Nat) (h : f a = f b) : True := by
  fail_if_success indisc at h
  guard_hyp h :ₛ f a = f b
  trivial

#print axioms merge_pair
#print axioms merge_three
#print axioms pair_observe
#print axioms grouped_output


theorem apply_prefix_obligation (P Q R : Prop)
    (r : P → Q → R) (hp : P) (hq : Q) : R := by
  apply r at hq with hr
  exact hp
  exact hr

theorem reject_dependent_goals : (∃ n : Nat, n = n) ∧ True := by
  constructor with ⟨value, property⟩ other
  fail_if_success indisc goals property other
  case value => exact 0
  case property => rfl
  case other => trivial

theorem recursive_assembly (n : Nat) (p q : Fin n × Fin n)
    (h1 : p.1.val = q.1.val) (h2 : p.2.val = q.2.val) : p = q := by
  fail_if_success ext : 1 at h1 h2 with whole : p = q
  ext! at h1 h2 with whole : p = q
  exact whole

theorem grouped_input_boundary (p q : PackedRecord)
    (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  fail_if_success ext : 1 at hx hy with whole : p = q
  have fields : p.x = q.x ∧ p.y = q.y := And.intro hx hy
  ext at fields with whole : p = q
  exact whole

theorem recursive_group_boundary (p q : PackedRecord) (h : p = q) :
    p.x = q.x ∧ p.y = q.y := by
  indisc! at h
  assumption

theorem recursive_goal_compare (n : Nat) (p q : Fin n × Nat)
    (h : p = q) : p.1.val = q.1.val := by
  indisc!
  guard_target =ₛ p = q
  exact h


def equalitySetoidForRule : Setoid Nat where
  r := Eq
  iseqv := { refl := fun _ => rfl, symm := Eq.symm, trans := Eq.trans }

theorem quotient_comparison (a b : Nat)
    (h : Quotient.mk equalitySetoidForRule a = Quotient.mk equalitySetoidForRule b) :
    a = b := by
  indisc : 1 at h
  guard_hyp h :ₛ a = b
  exact h

@[ext] structure DependentRecordForRule where
  index : Nat
  value : Fin (index + 1)

theorem dependent_comparison (p q : DependentRecordForRule) (h : p = q) :
    HEq p.value q.value := by
  indisc : 1 at h with hi hv
  guard_hyp hi :ₛ p.index = q.index
  guard_hyp hv :ₛ HEq p.value q.value
  exact hv

def reject_proposition_witness (h : ∃ n : Nat, n = 0) : Nat := by
  fail_if_success apply (fun proof : ∃ n : Nat, n = 0 => proof) at h with ⟨n, hn⟩
  exact 0

theorem injectivity_rule (f : Nat → Nat)
    (hf : ∀ {x y}, f x = f y → x = y)
    (a b : Nat) (h : f a = f b) : a = b := by
  apply hf at h
  exact h

#print axioms quotient_comparison
#print axioms dependent_comparison

theorem named_constructor_dependencies : ∃ n : Nat, n = n := by
  constructor with value property
  case value => exact 0
  case property => rfl

theorem named_apply_dependencies : ∃ n : Nat, n = n := by
  apply Exists.intro with property value
  case value => exact 0
  case property => rfl

theorem reject_ambiguous_constructor : True ∨ True := by
  fail_if_success constructor with chosen
  left
  trivial

-- Ext
-- apply to goal
example (a b c d : Nat) (h1 : a = c) (h2 : b = d)
    : (a, b) = (c, d) := by
  ext : 1 with left right
  case left => exact h1
  case right => exact h2

-- have & apply to goal
example (a b c d : Nat) (h1 : a = c) (h2 : b = d)
    : (a, b) = (c, d) := by
  have h : (a, b) = (c, d) := by
    ext : 1 with left right
    case left => exact h1
    case right => exact h2
  exact h

-- apply to hypothesis
example (a b c d : Nat) (h1 : a = c) (h2 : b = d)
    : (a, b) = (c, d) := by
  ext at h1 h2 with h
  exact h

-- Constructor
-- apply to goal
example (P Q : Prop) (hP : P) (hQ : Q)
    : P ∧ Q := by
  constructor with left right
  case left => exact hP
  case right => exact hQ

-- have & apply to goal
example (P Q : Prop) (hP : P) (hQ : Q)
    : P ∧ Q := by
  have h : P ∧ Q := by
    constructor with left right
    case left => exact hP
    case right => exact hQ
  exact h

-- apply to hypothesis
example (P Q : Prop) (hP : P) (hQ : Q)
    : P ∧ Q := by
  constructor at hP hQ with h
  exact h

-- Rcases
-- apply to goal
example (P Q : Prop) (hPQ : P ∧ Q)
    : P ∧ Q := by
  constructor with left right
  unpack goals left right with combined
  exact hPQ

-- have & apply to goal
example (P Q : Prop) (hPQ : P ∧ Q)
    : P ∧ Q := by
  have h : P ∧ Q := by
    constructor with left right
    unpack goals left right with combined
    exact hPQ
  exact h

-- apply to hypothesis
example (P Q : Prop) (hPQ : P ∧ Q)
    : P ∧ Q := by
  rcases hPQ with ⟨hP, hQ⟩
  constructor with left right
  case left => exact hP
  case right => exact hQ


-- Goal combination requires a proof of the newly grouped goal.
example (P Q : Prop) (hPQ : P ∧ Q) : P ∧ Q := by
  constructor with left right
  rcases goals left right with combined
  guard_target =ₛ P ∧ Q
  exact hPQ
