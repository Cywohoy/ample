import Ample.Math.Cardinality

open Ample

namespace CardinalityArithmetic

variable {A B : Type} {m n : Nat}

def splitIndex (m n : Nat) (x : Fin (m * n)) : Fin m × Fin n :=
  let a : Fin m := by
    exists (x.val % m)
    by_cases hz : 0 < m
    · arith
    · arith
  let b : Fin n := by
    exists (x.val / m)
    by_cases hz : 0 < n
    · arith
    · arith
  (a, b)

theorem splitIndex_bijective (m n : Nat) : Bijective (splitIndex m n) := by
  constructor
  · intro x y hxy
    injections
    arith
  · intro y
    -- 두 성분의 경계로 조합한 자연수의 경계를 확인한다.
    exists ⟨y.1 + y.2 * m, ?_⟩
    · arith
    · ext
      · expand
        arith
      · expand
        arith

example (hA : cardinal A = m) (hB : cardinal B = n) :
    cardinal (A × B) = ((m * n : Nat) : Cardinal) := by
  rcases (cardinal_eq_iff _ _).mp hA.symm with ⟨fA, hA⟩
  rcases (cardinal_eq_iff _ _).mp hB.symm with ⟨fB, hB⟩
  symm
  ext : 1
  let g (x : Fin m × Fin n) : A × B :=
    let (a, b) := x
    (fA a, fB b)
  exists g ∘ (splitIndex m n)
  apply bijective_compose _ _ (splitIndex_bijective m n)
  constructor
  · intro x y hxy
    expand at hxy
    injections
    ext : 1
    · apply hA.inj
      assumption
    · apply hB.inj
      arith
  · rintro ⟨yA, yB⟩
    exists (inverseMap fA hA yA, inverseMap fB hB yB)
    ext : 1
    · apply inverseMap_right fA
    · apply inverseMap_right fB

end CardinalityArithmetic
