import Ample.Math.Cardinality

open Ample

variable {A B C : Type} {m n : Nat}

example (h : SameCardinality A B) : SameCardinality B A := by card
example (h : SameCardinality A B) : cardinal A = cardinal B := by card
example (h : cardinal A = cardinal B) : SameCardinality A B := by card
example (hAB : cardinal A = cardinal B) (hBC : cardinal B = cardinal C) :
    cardinal A = cardinal C := by card
example (hAB : SameCardinality A B) (hBC : SameCardinality B C) :
    SameCardinality A C := by card
example (hBA : SameCardinality B A) (hA : cardinal A = n) : cardinal B = n := by card
example (hAB : SameCardinality A B) (hBC : SameCardinality B C)
    (hA : cardinal A = n) : cardinal C = n := by card
example (hA : cardinal A = n) : IsFinite A := by card
example (hA : IsInfinite A) (hAB : SameCardinality A B) : IsInfinite B := by card
example (hA : IsCountablyInfinite A) (hAB : SameCardinality A B) :
    IsCountablyInfinite B := by card
example (a : A) : cardinal (Elem (singleton a)) = 1 := by card
example (hA : IsFinite A) (hn : cardinal A = n) : cardinality A hA = n := by card

example (P : Prop) (h : P) : P := by
  fail_if_success (clear h; card)
  exact h

example (n : Nat) (h : cardinal A = n) : cardinal A = n := by
  fail_if_success (clear h; card)
  exact h

example (f : A → B) (hf : Bijective f) (y : B) :
    f (inverseMap f hf y) = y := by
  exact inverseMap_right f

example (hA : IsFinite A) : cardinal A = (cardinalityData A hA).val := by
  exact (cardinalityData A hA).property

example (A : Type) : CardinalityLT A (Set A) := by
  exact cardinality_lt_powerSet A

example (f : A → Set A) : ¬ Surjective f := by
  exact cantor_not_surjective f
