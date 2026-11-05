import Ample.Math.Cardinality

open Ample
open scoped Ample Classical

-- Both notation forms describe existence and uniqueness, not an executable witness.
theorem uniqueFour : ∃! n : Nat, n = 4 := by
  exists 4
  constructor
  · rfl
  · intro n hn
    exact hn

example : ExistsUnique (fun n : Nat => n = 4) := uniqueFour
example : uniqueValue (fun n : Nat => n = 4) uniqueFour = 4 := by
  apply uniqueValue_eq
  rfl
example : (fun n : Nat => n = 4)
    (uniqueValue (fun n => n = 4) uniqueFour) := by
  exact uniqueValue_property uniqueFour

-- A lift may return functions. Inference must work without supplying proof arguments.
section
variable {A B C : Type} (R : Relation A) [hR : IsEquivalence R]
  (g : A → B → C) (hg : ∀ a b, R a b → g a = g b)
noncomputable def functionLift : QuotientType R → B → C :=
  quotientLift R g hg
example (a : A) : functionLift R g hg (classOf R a) = g a := by
  exact quotientLift_classOf
example (a : A) : functionLift R g hg (classOf R a) = g a := by
  rw [functionLift, quotientLift_classOf]
end

-- Existence of a lift does not imply injectivity: a constant function also descends.
private noncomputable def constantParity : Parity → Int :=
  quotientLift (Congruent 2)
    (fun _ => 0) (by intros; rfl)
theorem constantParity_not_injective : ¬ Injective constantParity := by
  intro h
  apply parityClass_zero_ne_one
  apply h
  unfold constantParity
  rw [quotientLift_classOf, quotientLift_classOf]

-- Finite choice is proved by induction; it does not import Classical.choice.
#print axioms fin_choice
#print axioms uniqueFour
#print axioms uniqueValue
#print axioms quotient_value_unique
#print axioms quotientLift_classOf
