import Ample.Math.Cardinality

open Ample
open scoped Ample Classical

-- Constructing objects still takes the mathematical data explicitly.
-- Their specification lemmas infer only what their rewrite patterns contain.
section Inverse
variable {A B : Type} (f : A → B) (hf : Bijective f)

example (x : A) : inverseMap f hf (f x) = x := by
  exact inverseMap_left f
example (x : A) : inverseMap f hf (f x) = x := by
  rw [inverseMap_left f]
example (y : B) : f (inverseMap f hf y) = y := by
  exact inverseMap_right f
example (y : B) : f (inverseMap f hf y) = y := by
  rw [inverseMap_right f]

-- Implicit point arguments are introduced before proving a universal law.
example : ∀ x, inverseMap f hf (f x) = x := by
  intro x
  exact inverseMap_left f
end Inverse

section Representatives
variable {A : Type _} (R : Relation A) (q : QuotientType R)

example : q = classOf R (quotientRepr R q) := by
  exact quotientRepr_spec q
example (P : QuotientType R → Prop)
    (h : P (classOf R (quotientRepr R q))) : P q := by
  rw [quotientRepr_spec q]
  exact h
end Representatives

section Lift
variable {A B : Type _} (R : Relation A) (hR : IsEquivalence R)
  (f : A → B) (hf : ∀ a b, R a b → f a = f b) (a : A)

example : quotientLift R hR f hf (classOf R a) = f a := by
  exact quotientLift_classOf
example : quotientLift R hR f hf (classOf R a) = f a := by
  rw [quotientLift_classOf]
end Lift

section Finite
variable (A : Type) (hA : IsFinite A)

example : cardinal A = cardinality A hA := by
  exact cardinality_spec hA
example : cardinal A = cardinality A hA := by
  rw [cardinality_spec hA]
end Finite
