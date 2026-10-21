import Ample.Math

open Ample
open scoped Ample Classical

namespace CardinalConstructions

-- Empty families and zero exponents exercise the boundary conventions.
example : cardinal (Fin 0 → Fin 0) = 1 := by
  rw [cardinal_fin_arrow]
  rfl

example : (0 : Cardinal) ^ (0 : Cardinal) = 1 := by
  exact cardinal_nat_pow 0 0

example : cardinal (Σ i : Fin 0, Fin (i.val + 1)) = 0 := by
  rw [cardinal_finiteSigma (fun i => Fin (i + 1)) 0]
  rfl

example : cardinal ((i : Fin 0) → Fin (i.val + 1)) = 1 := by
  rw [cardinal_finitePi (fun i => Fin (i + 1)) 0]
  rfl

-- Replacing either representative preserves each operation.
example {A B C D : Type}
    (hAC : cardinal A = cardinal C)
    (hBD : cardinal B = cardinal D) :
    cardinal (A → B) = cardinal (C → D) := by
  rw [cardinal_arrow, cardinal_arrow, hAC, hBD]

example {A B : Type} :
    cardinal (Sum A B) = cardinal A + cardinal B := by
  exact cardinal_sum A B

example {A B : Type} :
    cardinal (A × B) = cardinal A * cardinal B := by
  rw [cardinal_product]

example (f : Fin 0 → Fin 0) : Injective f ↔ Surjective f := by
  apply finite_injective_iff_surjective f (fin_isFinite 0)
  rfl

example : cardinal (Set (Fin 3)) = 8 := by
  rw [cardinal_set, cardinal_fin]
  exact cardinal_nat_pow 3 2

-- Explicit Nat annotations keep arithmetic below the coercion unambiguous.
example (m n : Nat) :
    cardinal (Fin m × Fin n) = ((m * n : Nat) : Cardinal) := by
  rw [cardinal_product, cardinal_fin, cardinal_fin, cardinal_nat_mul]

#print axioms Ample.cardinal_finiteSigma
#print axioms Ample.cardinal_finitePi
#print axioms Ample.finite_injective_iff_surjective
#print axioms Ample.cardinal_set

end CardinalConstructions
