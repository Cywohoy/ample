import Ample.Tactic.Rule

open Ample

theorem constructor_forward (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor at hp hq with h
  guard_hyp h :ₛ P ∧ Q
  exact h

theorem constructor_explicit_result (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : R := by
  constructor at hp hq with h : P ∧ Q
  guard_hyp h :ₛ P ∧ Q
  guard_hyp hp :ₛ P
  exact hr

theorem rcases_backward (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor with first second
  rcases goals first second with combined
  guard_target =ₛ P ∧ Q
  exact h

theorem rcases_forward (P Q : Prop) (h : P ∧ Q) : Q := by
  rcases at h with ⟨hp, hq⟩
  exact hq

def rcases_data_goals (p : Nat × Bool) : Nat × Bool := by
  constructor with number flag
  rcases goals number flag with pair
  guard_target =ₛ Nat × Bool
  exact p

def constructor_data (n : Nat) (b : Bool) : Nat × Bool := by
  constructor at n b with p
  exact p

theorem constructor_dependent (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ k, P k := by
  constructor at n hn with h
  exact h

theorem constructor_group_preserved (P Q R : Prop) (hpq : P ∧ Q) (hr : R) :
    (P ∧ Q) ∧ R := by
  constructor at hpq hr with h
  guard_hyp h :ₛ (P ∧ Q) ∧ R
  exact h

theorem rcases_unselected (P Q R : Prop) (hp : P) (hq : Q) (hr : R) :
    P ∧ Q ∧ R := by
  constructor with first ⟨second, third⟩
  rcases goals first second with combined
  case combined =>
    constructor at hp hq with h
    exact h
  case third => exact hr

theorem reject_constructor_inputs (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  fail_if_success constructor at hq hp with h : P ∧ Q
  guard_hyp hp :ₛ P
  constructor at hp hq with h
  exact h

theorem reject_disjunction_grouping (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor with first second
  fail_if_success rcases goals first second with combined : P ∨ Q
  case first => exact hp
  case second => exact hq

theorem reject_dependent_grouping : ∃ n : Nat, n = n := by
  constructor with value property
  fail_if_success rcases goals value property with combined
  case value => exact 0
  case property => rfl

def reject_prop_extraction (n : Nat) (hn : n = n) : Nat × (n = n → Nat) := by
  constructor with first second
  fail_if_success rcases goals first second : ∃ k : Nat, k = k
  case first => exact n
  case second => intro _; exact n

structure ThreeFields where
  first : Nat
  second : Bool
  third : String

def explicit_record_goals (x : ThreeFields) : ThreeFields := by
  constructor with first second third
  rcases goals first second third with whole : ThreeFields
  exact x

#print axioms constructor_forward
#print axioms rcases_backward
#print axioms rcases_data_goals
#print axioms constructor_dependent
theorem cases_at_one_level (P Q R : Prop) (h : P ∧ (Q ∧ R)) : Q ∧ R := by
  cases at h with
  | intro hp hqr =>
    guard_hyp hqr :ₛ Q ∧ R
    exact hqr

theorem cases_at_branches (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases at h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

theorem cases_at_false (P : Prop) (h : False) : P := by
  cases at h

theorem cases_goal_one_level (P Q R : Prop) (h : P ∧ (Q ∧ R)) : P ∧ (Q ∧ R) := by
  constructor with first rest
  cases goals first rest with combined
  guard_target =ₛ P ∧ (Q ∧ R)
  exact h

theorem rcases_goal_recursive (P Q R : Prop) (h : P ∧ Q ∧ R) : P ∧ Q ∧ R := by
  constructor with first ⟨second, third⟩
  fail_if_success cases goals first second third
  rcases goals first second third with combined
  guard_target =ₛ P ∧ Q ∧ R
  exact h

theorem rcases_recursive_at (P Q R : Prop) (h : P ∧ Q ∧ R) : R := by
  rcases at h with ⟨hp, hq, hr⟩
  exact hr

def rcases_recursive_data (p : Nat × Bool × String) : Nat × Bool × String := by
  constructor with number ⟨flag, word⟩
  rcases goals number flag word with combined
  guard_target =ₛ Nat × Bool × String
  exact p

theorem reordered_goal_names (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor with first second
  rcases goals second first with combined
  guard_target =ₛ Q ∧ P
  constructor at hq hp with h
  exact h

#print axioms cases_goal_one_level
#print axioms rcases_goal_recursive
#print axioms rcases_recursive_data

theorem unpack_one_layer (P Q R : Prop) (h : P ∧ Q ∧ R) : Q ∧ R := by
  unpack h with ⟨hp, hqr⟩
  guard_hyp hqr :ₛ Q ∧ R
  exact hqr

theorem unpack_backward (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor with first second
  unpack goals first second with combined
  guard_target =ₛ P ∧ Q
  exact h

theorem unpack_dependent (n : Nat) (x : Fin n) : ∃ k : Nat, k < n := by
  unpack x with ⟨value, bound⟩
  exists value

theorem unpack_exists (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n := by
  unpack h with ⟨n, hn⟩
  exists n

theorem reject_unpack_sum (P Q : Prop) (h : P ∨ Q) : P ∨ Q := by
  fail_if_success unpack h with ⟨hp, hq⟩
  guard_hyp h :ₛ P ∨ Q
  exact h

theorem reject_unpack_pattern (P Q R : Prop) (h : P ∧ Q ∧ R) : P ∧ Q ∧ R := by
  fail_if_success unpack h with ⟨hp, ⟨hq, hr⟩⟩
  fail_if_success unpack h with ⟨hp, hq, hr⟩
  fail_if_success unpack h with hp
  guard_hyp h :ₛ P ∧ Q ∧ R
  exact h

def unpack_data_goals (p : Nat × Bool) : Nat × Bool := by
  constructor with number flag
  unpack goals number flag with combined
  exact p

#print axioms unpack_backward
#print axioms unpack_dependent

theorem left_forward (P Q : Prop) (hp : P) : P ∨ Q := by
  left at hp with h
  guard_hyp h :ₛ P ∨ Q
  exact h

theorem right_forward (P Q : Prop) (hq : Q) : P ∨ Q := by
  right at hq with h
  guard_hyp h :ₛ P ∨ Q
  exact h

theorem left_explicit (P Q R : Prop) (hp : P) (hr : R) : R := by
  left at hp with h : P ∨ Q
  guard_hyp h :ₛ P ∨ Q
  exact hr

theorem left_metavariable_inferred (P Q R : Prop) (hp : P) (step : P ∨ Q → R) : R := by
  left at hp with h
  apply step at h with result
  exact result

theorem right_metavariable_inferred (P Q R : Prop) (hq : Q) (step : P ∨ Q → R) : R := by
  right at hq with h
  apply step at h with result
  exact result

theorem explicit_alternative_goal (P Q : Prop) (hp : P) : True := by
  left at hp with h
  trivial
  case alternative => exact Q

theorem reject_wrong_disjunct (P Q : Prop) (hp : P) (hq : Q) : P ∨ Q := by
  fail_if_success left at hq with h : P ∨ Q
  guard_hyp hq :ₛ Q
  right at hq with h
  exact h

theorem conjunction_forward (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R := by
  and_intros at hp hq hr with h
  guard_hyp h :ₛ P ∧ Q ∧ R
  exact h

theorem conjunction_input_group (P Q R : Prop) (hpq : P ∧ Q) (hr : R) : (P ∧ Q) ∧ R := by
  and_intros at hpq hr with h
  guard_hyp h :ₛ (P ∧ Q) ∧ R
  exact h

theorem existence_forward (A : Type) (P : A → Prop) (a : A) (ha : P a) : ∃ x, P x := by
  exists a at ha with h
  exact h

theorem existence_explicit (A : Type) (P : A → Prop) (a : A) (ha : P a) : True := by
  exists a at ha with h : ∃ x, P x
  guard_hyp h :ₛ ∃ x, P x
  trivial

#print axioms left_forward
#print axioms right_forward
#print axioms left_metavariable_inferred
#print axioms conjunction_forward
#print axioms existence_forward

theorem reject_tuple_disjunction_output (P Q : Prop) (hp : P) : P ∨ Q := by
  fail_if_success left at hp with ⟨first, second⟩ : P ∨ Q
  left at hp with h
  exact h

theorem named_existential_unpack (P : Nat → Prop) (n : Nat) (hn : P n) : ∃ x, P x := by
  exists n at hn with ⟨value, property⟩
  exists value

theorem left_elimination_conditions (P Q : Prop) (h : P ∨ Q) (step : Q → P) : P := by
  cases h with
  | inl hp => exact hp
  | inr hq =>
    apply step at hq with hp
    exact hp


theorem multiple_application (P Q R : Prop) (r : P → Q → R) (hp : P) (hq : Q) : R := by
  apply r at hp hq with hr
  guard_hyp hr :ₛ R
  exact hr

theorem application_group_preserved (P Q R : Prop)
    (r : (P ∧ Q) → R) (hpq : P ∧ Q) : R := by
  apply r at hpq with hr
  exact hr

theorem application_too_many (P Q : Prop) (r : P → Q) (hp : P) (hq : Q) : Q := by
  fail_if_success apply r at hp hq with result
  guard_hyp hp :ₛ P
  apply r at hp with result
  exact result

theorem case_rule_backward (P Q R : Prop) (h : P ∨ Q)
    (leftProof : P → R) (rightProof : Q → R) : R := by
  cases goal (P ∨ Q) with source leftBranch rightBranch
  case source => exact h
  case leftBranch => exact leftProof
  case rightBranch => exact rightProof

theorem case_rule_forward (P Q R : Prop) (h : P ∨ Q)
    (leftProof : P → R) (rightProof : Q → R) : R := by
  cases at h leftProof rightProof with result
  exact result

theorem case_rule_dependent_fields (A : Type) (P : A → Prop) (R : Prop)
    (h : ∃ x, P x) (step : ∀ x, P x → R) : R := by
  cases at h step with result
  exact result

def data_case_rule (b : Bool) (rFalse rTrue : Nat) : Nat := by
  cases goal Bool with value falseBranch trueBranch
  case value => exact b
  case falseBranch => exact rFalse
  case trueBranch => exact rTrue

theorem case_rule_reject_handlers (P Q R : Prop) (h : P ∨ Q)
    (leftProof : P → R) (wrong : Q → P) (hr : R) : R := by
  fail_if_success cases at h leftProof wrong with result
  guard_hyp h :ₛ P ∨ Q
  exact hr

#print axioms case_rule_backward
#print axioms case_rule_forward
#print axioms case_rule_dependent_fields
#print axioms data_case_rule
theorem contradiction_forward (P : Prop) (counter : ¬ P → False) : P := by
  by_contra at counter with h
  exact h

theorem classical_cases_forward (P R : Prop) (positive : P → R) (negative : ¬ P → R) : R := by
  by_cases at positive negative with h
  exact h

theorem induction_forward (P : Nat → Prop) (zero : P 0)
    (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  induction at zero step with h
  exact h

theorem induction_source_wrong (P : Nat → Prop) (zero : P 0)
    (wrong : ∀ n, P (n + 1) → P n) : P 0 := by
  fail_if_success induction at zero wrong with h : ∀ n, P n
  exact zero

theorem wlog_forward (P R : Prop) (restricted : P → R)
    (reduction : (P → R) → ¬ P → R) : R := by
  wlog at restricted reduction with h
  exact h

theorem wlog_generalized_forward (P R : Nat → Prop)
    (restricted : ∀ n, P n → R n)
    (reduction : (∀ n, P n → R n) → ∀ n, ¬ P n → R n) : ∀ n, R n := by
  wlog at restricted reduction with h
  exact h

#print axioms contradiction_forward
#print axioms classical_cases_forward
#print axioms induction_forward
#print axioms wlog_generalized_forward
theorem implication_introduction_forward (P Q : Prop) (hq : Q) : P → Q := by
  intro at hq with h
  exact h

theorem universal_introduction_forward (A : Type) (P : A → Prop)
    (h : ∀ x, P x) : ∀ x, P x := by
  intro at h with whole
  exact whole

theorem unknown_application_rule (P Q : Prop) (r : P → Q) (hp : P) : Q := by
  apply goal (P → Q) with rule premise
  case rule => exact r
  case premise => exact hp

theorem unknown_universal_rule (A : Type) (P : A → Prop) (a : A) (h : ∀ x, P x) : P a := by
  apply goal (∀ x, P x) with all
  exact h

theorem reject_unsound_universal (A : Type) (P : A → Prop) (a : A) (ha : P a) : P a := by
  fail_if_success intro at ha with all : ∀ x, P x
  exact ha

#print axioms implication_introduction_forward
#print axioms unknown_application_rule
#print axioms unknown_universal_rule

theorem unpack_pair_substitutes_projections (p : Nat × Nat)
    (h : p.1 = p.2) : p.2 = p.1 := by
  unpack p with ⟨first, second⟩
  fail_if_success guard_hyp p :ₛ Nat × Nat
  guard_hyp h : first = second
  guard_target = second = first
  exact h.symm

theorem unpack_fin_substitutes_projections (n : Nat) (x : Fin n)
    (h : x.val = 2) : x.val + 1 = 3 := by
  unpack x with ⟨a, ha⟩
  fail_if_success guard_hyp x :ₛ Fin n
  guard_hyp ha :ₛ a < n
  guard_hyp h : a = 2
  guard_target = a + 1 = 3
  rw [h]

theorem unpack_subtype_substitutes_projections (P : Nat → Prop)
    (x : {a : Nat // P a}) (h : x.val = 2) : P x.val := by
  unpack x with ⟨a, ha⟩
  fail_if_success guard_hyp x :ₛ {a : Nat // P a}
  guard_hyp ha :ₛ P a
  guard_hyp h : a = 2
  guard_target = P a
  exact ha

def projection_data_constructor (n : Nat) (b : Bool) : Nat × Bool := by
  constructor at n b with p
  have hp : p = (n, b) := by rfl
  exact p

theorem unpack_expression (P Q : Prop) (h : P ∧ Q) : Q := by
  unpack (id h) with ⟨hp, hq⟩
  exact hq

theorem unpack_expression_dependent (n : Nat) (x : Fin n) : x.val < n := by
  unpack (id x) with ⟨value, bound⟩
  exact bound
