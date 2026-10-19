import Ample.Math.Cardinality
import Ample.Tactic.Auto

open Ample

variable {A B C : Type} {m n : Nat}

-- Counting and countable infinitude are equalities of cardinal classes.
example : IsFinite A ↔ ∃ n : Nat, cardinal A = n := by rfl
example (m n : Nat) : (m : Cardinal) = (n : Cardinal) ↔ m = n := by
  exact Cardinal.ofNat_eq_iff m n
example : cardinal (Fin 3) = 3 := by rfl
example : IsCountablyInfinite A ↔ cardinal Nat = cardinal A := by rfl

example (f : Fin n → A) (hf : Bijective f) : cardinal A = n := by
  symm
  ext : 1
  guard_target =ₛ SameCardinality (Fin n) A
  exists f

example (h : cardinal A = n) : ∃ f : Fin n → A, Bijective f := by
  exact (cardinal_eq_iff _ _).mp h.symm

-- Cardinal order is characterized by injections between representatives.
example : cardinal A ≤ cardinal B ↔ CardinalityLE A B := by
  exact cardinal_le_iff A B
example (f : A → B) (hf : Injective f) : cardinal A ≤ cardinal B := by
  apply (cardinal_le_iff A B).mpr
  exists f

example (a b : Cardinal) (h : a ≤ b) : a < b ↔ a ≠ b := by
  constructor
  · intro hlt
    exact hlt.right
  · intro hne
    exact ⟨h, hne⟩

-- Changing either quotient representative preserves the same comparison.
example (hA : cardinal A = cardinal C) (h : cardinal A ≤ cardinal B) :
    cardinal C ≤ cardinal B := by
  rw [← hA]
  exact h

example (hB : cardinal B = cardinal C) (h : cardinal A ≤ cardinal B) :
    cardinal A ≤ cardinal C := by
  rw [← hB]
  exact h

example (a : A) (b : B) :
    cardinal (Elem (singleton a)) = cardinal (Elem (singleton b)) := by
  exact (singleton_cardinal a).trans (singleton_cardinal b).symm

example (hAB : cardinal A = cardinal B) : cardinal A = n ↔ cardinal B = n := by
  rw [hAB]

example (hA : IsInfinite A) (hAB : cardinal A = cardinal B) : IsInfinite B := by
  intro hB
  rcases hB with ⟨n, hn⟩
  apply hA
  exists n
  exact hAB.trans hn

example (A : Type) : cardinal A < cardinal (Set A) := by
  exact cardinal_lt_powerSet A

example : ¬ IsCountablyInfinite (Set Nat) := by
  exact nat_powerSet_not_countablyInfinite

-- Automation is introduced after the direct constructions, in its own rule set.
example (hAB : cardinal A ≤ cardinal B) (hBC : cardinal B ≤ cardinal C) :
    cardinal A ≤ cardinal C := by card

example (a b c : Cardinal) (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c := by card

example (a b c : Cardinal) (hAB : a = b) (hBC : b ≤ c) : a ≤ c := by card

example (a b c : Cardinal) (hAB : a ≤ b) (hBC : b = c) : a ≤ c := by card

example (a b : Cardinal) (h : a ≤ b) : a ≤ b := by
  fail_if_success (clear h; card)
  exact h

example (hAB : cardinal A = cardinal B) (hA : cardinal A = n) :
    cardinal B = n := by card

example (hAB : cardinal A = cardinal B) (hA : IsCountablyInfinite A) :
    IsCountablyInfinite B := by card

example (h : cardinal A = n) : cardinal (Fin n) = cardinal A := by card

example (h : cardinal (Fin n) = cardinal A) : cardinal A = n := by card

section

open scoped Ample.Auto

-- Automatic expression cleanup must retain the explicit quotient comparison step.
example (f : Fin n → A) (hf : Bijective f) : cardinal A = n := by
  symm
  ext : 1
  guard_target =ₛ SameCardinality (Fin n) A
  exists f

example (f : Nat → A) (hf : Bijective f) : IsCountablyInfinite A := by
  ext : 1
  exists f

end
