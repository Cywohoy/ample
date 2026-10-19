import Ample.Math.Cardinality
import Ample.Tactic.Auto

open Course

example (A B : Type) :
    cardinal A = cardinal B ↔ SameCardinality A B := by
  exact cardinal_eq_iff A B

example : cardinal Nat = cardinal (Elem positives) := by
  ext : 1
  guard_target =ₛ SameCardinality Nat (Elem positives)
  exact (cardinal_eq_iff _ _).mp Course.positives_countablyInfinite

example (A B : Type) (h : SameCardinality A B) :
    cardinal A = cardinal B := by
  ext1
  guard_target =ₛ SameCardinality A B
  exact h

example (f g : Nat → Type) (h : ∀ x, SameCardinality (f x) (g x)) :
    (fun x => cardinal (f x)) = (fun x => cardinal (g x)) := by
  ext x : 1
  guard_target =ₛ cardinal (f x) = cardinal (g x)
  ext : 1
  guard_target =ₛ SameCardinality (f x) (g x)
  exact h x

example (A B : Type) (a b : Int)
    (hAB : SameCardinality A B) (hab : Congruent 2 a b) :
    (cardinal A, parityClass a) = (cardinal B, parityClass b) := by
  ext : 1
  · guard_target =ₛ cardinal A = cardinal B
    ext : 1
    guard_target =ₛ SameCardinality A B
    exact hAB
  · guard_target =ₛ parityClass a = parityClass b
    ext : 1
    guard_target =ₛ Congruent 2 a b
    exact hab

example : cardinal (Fin 2) ≠ cardinal (Fin 3) := by
  intro h
  have hSame : SameCardinality (Fin 2) (Fin 3) := by
    exact (cardinal_eq_iff _ _).mp h
  have hEq : 2 = 3 := fin_sameCardinality_eq hSame
  contradiction

example : parityClass 0 = parityClass 4 := by
  ext
  exists (-2)

example (a b : Int) (h : parityClass a = parityClass b) :
    Congruent 2 a b := by
  exact (parityClass_eq_iff a b).mp h

section

open scoped Course.Auto

example (A B : Type) (h : SameCardinality A B) :
    cardinal A = cardinal B := by
  ext : 1
  exact h

example (a b : Int) (h : Congruent 2 a b) :
    parityClass a = parityClass b := by
  ext : 1
  exact h

end
