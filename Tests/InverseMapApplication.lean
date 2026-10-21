import Ample.Math.Functions

open Ample

variable {A B : Type} {m n : Nat}

-- The inverse-map expression determines its proof and value arguments.
example (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Surjective (fun x : Fin m × Fin n => (fA x.1, fB x.2)) := by
  rintro ⟨yA, yB⟩
  exists (inverseMap fA hA yA, inverseMap fB hB yB)
  ext : 1
  · dsimp
    exact inverseMap_right fA
  · dsimp
    exact inverseMap_right fB

-- Rewriting uses the same interface and infers the packaged evidence.
example (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Surjective (fun x : Fin m × Fin n => (fA x.1, fB x.2)) := by
  rintro ⟨yA, yB⟩
  exists (inverseMap fA hA yA, inverseMap fB hB yB)
  ext : 1
  · rw [inverseMap_right fA]
  · rw [inverseMap_right fB]
