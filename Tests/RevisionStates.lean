import Ample.Math.Groups.Order
import Ample.Tactic.Auto

open Ample

theorem rejected_unpack_retains_hypothesis (P Q : Prop)
    (h : P ∨ Q) : Q ∨ P := by
  fail_if_success unpack h with ⟨hp, hq⟩
  guard_hyp h :ₛ P ∨ Q
  guard_target =ₛ Q ∨ P
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

theorem insufficient_function_comparison
    (f g : Nat → Nat) (h : f 0 = g 0) : True := by
  fail_if_success ext at h : f = g
  guard_hyp h :ₛ f 0 = g 0
  guard_target =ₛ True
  trivial

theorem rejected_goal_combination (P Q : Prop)
    (hp : P) (hq : Q) : (True → P) ∧ (True → Q) := by
  constructor with first second
  all_goals intro ht
  fail_if_success unpack goals first second
  case first =>
    guard_hyp ht :ₛ True
    guard_target =ₛ P
    exact hp
  case second =>
    guard_hyp ht :ₛ True
    guard_target =ₛ Q
    exact hq

theorem explicit_disjunction (P Q : Prop) (hp : P) : P ∨ Q := by
  left at hp with result : P ∨ Q
  guard_hyp hp :ₛ P
  guard_hyp result :ₛ P ∨ Q
  exact result

theorem product_numbering_reused {A B : Type} {m n : Nat}
    (hA : cardinal A = m) (hB : cardinal B = n) :
    cardinal (A × B) = m * n := by
  unpack (cardinal_eq_iff (Fin m) A).mp hA.symm with ⟨f, hf⟩
  unpack (cardinal_eq_iff (Fin n) B).mp hB.symm with ⟨g, hg⟩
  symm
  ext : 1
  exists productMap f g ∘ finProduct m n
  apply bijective_compose
  · exact finProduct_bijective m n
  · exact productMap_bijective f g hf hg
