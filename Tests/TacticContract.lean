import Ample.Tactic

open Ample

namespace TacticContract

def identNat (n : Nat) := n

theorem expansion_finishes (n : Nat) : identNat n = n := by
  expand

theorem dsimp_finishes (n : Nat) : identNat n = n := by
  dsimp [identNat]

theorem unfold_finishes (n : Nat) : identNat n = n := by
  unfold identNat

theorem symmetry_finishes (n : Nat) : n = n := by
  symm

theorem merging_only_finishes_selected_goals :
    ((1 = 1) ∧ (2 = 2)) ∧ (3 = 3) := by
  constructor with ⟨first, second⟩ pending
  indisc goals first second with combined
  guard_target =ₛ 3 = 3
  rfl

theorem change_finishes (n : Nat) : identNat n = n := by
  change n = n

theorem rewrite_finishes (a b : Nat) (h : a = b) : a = b := by
  rw [h]

theorem rewrite_finishes_iff (P Q : Prop) (h : P ↔ Q) : P ↔ Q := by
  rw [h]

theorem failed_rewrite_restores_the_entire_step (a b : Nat)
    (h : a = b) (ha : a = 4) : b = 4 := by
  fail_if_success rw [h, Nat.add_comm] at ha
  guard_hyp ha :ₛ a = 4
  rw [h] at ha
  exact ha

theorem conditional_rewrite_keeps_its_condition (a m : Nat) (h : a < m) :
    a % m = a := by
  rw [Nat.mod_eq_of_lt]
  guard_target =ₛ a < m
  exact h

theorem hypothesis_transform_finishes (a b : Nat)
    (h : a = b) (ha : identNat a = a) : a = a := by
  expand at ha

theorem pending_goal_is_untouched : (identNat 1 = 1) ∧ (2 = 2) := by
  constructor
  expand
  guard_target =ₛ 2 = 2
  rfl

theorem zero_results_do_not_run_on_a_sibling : (1 + 0 = 1) ∧ (2 = 2) := by
  constructor
  rw [Nat.add_zero]
  guard_target =ₛ 2 = 2
  rfl

theorem normal_apply_order : ∃ n : Nat, n = 7 := by
  apply Exists.intro
  rfl

theorem named_apply_order : ∃ n : Nat, n = 7 := by
  apply Exists.intro with certificate value
  case certificate => rfl

theorem reflexivity_does_not_choose_data : ∃ n : Nat, n = 7 := by
  apply Exists.intro with certificate value
  expand
  -- The automatic check must leave both the constraint and the data choice.
  case value => exact 7
  case certificate => rfl

theorem recursive_ext_reaches_values (p q : Fin 3 × Fin 4)
    (h₁ : p.1.val = q.1.val) (h₂ : p.2.val = q.2.val) : p = q := by
  ext! with first second
  case first => exact h₁
  case second => exact h₂

theorem bare_ext_preserves_components (p q : Fin 3 × Fin 4)
    (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q := by
  ext with first second
  case first =>
    guard_target =ₛ p.1 = q.1
    exact h₁
  case second =>
    guard_target =ₛ p.2 = q.2
    exact h₂

theorem explicit_ext_depth_reaches_values (p q : Fin 3 × Fin 4)
    (h₁ : p.1.val = q.1.val) (h₂ : p.2.val = q.2.val) : p = q := by
  ext : 2 with first second
  case first =>
    guard_target =ₛ p.1.val = q.1.val
    exact h₁
  case second => exact h₂

theorem function_comparison_keeps_the_codomain (f g : Nat → Fin 3)
    (h : ∀ x, f x = g x) : f = g := by
  ext x
  guard_target =ₛ f x = g x
  exact h x

theorem solved_outputs_keep_the_other_name (a b c : Nat) (h : b = c) :
    (a, b) = (a, c) := by
  ext : 1 with unchanged changed
  case changed => exact h

theorem recursive_indisc_names_leaves (p q : Fin 3 × Fin 4) (h : p = q) :
    p.1.val = q.1.val := by
  indisc : 2 at h with first second
  guard_hyp h :ₛ p = q
  guard_hyp first :ₛ p.1.val = q.1.val
  guard_hyp second :ₛ p.2.val = q.2.val
  exact first

theorem bare_indisc_names_components (p q : Fin 3 × Fin 4) (h : p = q) :
    p.1 = q.1 := by
  indisc at h with first second
  guard_hyp h :ₛ p = q
  guard_hyp first :ₛ p.1 = q.1
  guard_hyp second :ₛ p.2 = q.2
  exact first

theorem observations_and_depth_are_distinct (f g : Nat → Fin 3) (h : f = g) :
    f 2 = g 2 := by
  indisc (2 : Nat) : 1 at h with value
  exact value

theorem constructor_comparison_is_one_layer (m n : Nat)
    (h : Nat.succ (Nat.succ m) = Nat.succ (Nat.succ n)) :
    Nat.succ m = Nat.succ n := by
  indisc at h
  guard_hyp h :ₛ m + 1 = n + 1
  exact h

theorem integer_cast_comparison_is_one_layer (m n : Nat)
    (h : (m : Int) = (n : Int)) : m = n := by
  indisc at h with naturals
  guard_hyp h :ₛ (m : Int) = (n : Int)
  guard_hyp naturals :ₛ m = n
  exact naturals

theorem names_do_not_select_depth (p q : Fin 3 × Fin 4) (h : p = q) :
    p.1 = q.1 := by
  fail_if_success indisc at h with onlyOneName
  guard_hyp h :ₛ p = q
  indisc : 1 at h with first second
  exact first

theorem duplicate_names_restore_the_goal (a b c d : Nat)
    (h₁ : a = b) (h₂ : c = d) : (a, c) = (b, d) := by
  fail_if_success ext : 1 with repeated repeated
  ext : 1 with first second
  case first => exact h₁
  case second => exact h₂

theorem congr_depth (f : Nat → Nat) (g : Nat → Nat) (x y : Nat) :
    f (g (x + y)) = f (g (y + x)) := by
  congr : 2
  exact Nat.add_comm x y

theorem ext_at (P : Prop) (a b c d : Nat) (h₁ : a = b) (h₂ : c = d)
    (use : (a, c) = (b, d) → P) : P := by
  ext : 1 at h₁ h₂ with pair
  exact use pair

theorem ext_at_obeys_depth (p q : Fin 3 × Fin 4)
    (h₁ : p.1.val = q.1.val) (h₂ : p.2.val = q.2.val) : p = q := by
  fail_if_success ext at h₁ h₂ with pair : p = q
  ext : 2 at h₁ h₂ with pair : p = q
  exact pair

theorem indisc_goal_obeys_depth (p q : Fin 3 × Fin 4)
    (h : p = q) : p.1.val = q.1.val := by
  indisc
  guard_target =ₛ p.1 = q.1
  indisc
  guard_target =ₛ p = q
  exact h

theorem side_conditions_before_result (C P Q : Prop) (r : C → P → Q)
    (hc : C) (hp : P) : Q := by
  apply r at hp with result
  · fail_if_success exact result
    exact hc
  · exact result

theorem explicit_holes_are_obligations (C P Q : Prop) (r : C → P → Q)
    (hc : C) (hp : P) : Q := by
  apply (r ?_) at hp with result
  · exact hc
  · exact result

class Chosen (A : Type) where
  value : A

theorem explicit_class_values_are_data (P Q : Prop)
    (r : Chosen Nat → P → Q) (hp : P) : Q := by
  apply r at hp with result
  · exact { value := 4 }
  · exact result

theorem instance_failure_rolls_back (P Q : Prop)
    (r : [Chosen Nat] → P → Q) (hp : P) : Q := by
  fail_if_success apply r at hp with result
  guard_hyp hp :ₛ P
  letI : Chosen Nat := { value := 4 }
  apply r at hp with result
  exact result

open scoped Ample.Auto in
theorem normalization_and_finishing (n : Nat) : identNat n = n := by
  expand

open scoped Ample.Auto in
theorem normalization_of_a_combined_result (a b c d : Nat)
    (h : (a, c) = (b, d)) : a = b ∧ c = d := by
  constructor with first second
  indisc goals first second with pair
  guard_target =ₛ (a, c) = (b, d)
  exact h

open scoped Ample.Auto in
theorem normalization_preserves_reflexive_pending_goals (n m : Nat) :
    (n + 0 = n) ∧ (m = m) := by
  constructor with first second
  rw [Nat.add_zero]
  guard_target =ₛ m = m
  rfl

end TacticContract
