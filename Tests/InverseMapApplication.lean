import Ample.Math.Functions

open Ample

variable {A B : Type} {m n : Nat}

-- Applying the law without proof arguments leaves bijectivity obligations.
example (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Surjective (fun x : Fin m × Fin n => (fA x.1, fB x.2)) := by
  rintro ⟨yA, yB⟩
  exists (inverseMap fA hA yA, inverseMap fB hB yB)
  ext : 1
  · apply inverseMap_right
    guard_target = Bijective fA
    exact hA
  · apply inverseMap_right
    guard_target = Bijective fB
    exact hB

-- Explicit proof arguments remain supported independently of inference.
example (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Surjective (fun x : Fin m × Fin n => (fA x.1, fB x.2)) := by
  rintro ⟨yA, yB⟩
  exists (inverseMap fA hA yA, inverseMap fB hB yB)
  ext : 1
  · apply inverseMap_right _ hA
  · apply inverseMap_right _ hB
