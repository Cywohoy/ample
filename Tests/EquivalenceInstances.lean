import Ample.Math.Cardinality

open Ample
open scoped Ample Classical

namespace EquivalenceInstancesTests

-- Ordinary implicit arguments do not trigger instance synthesis, even when
-- an instance for the required proposition is already registered.
private theorem implicit_symm {A : Type} (R : Relation A)
    {hR : IsEquivalence R} (a b : A) : R a b → R b a := by
  intro hab
  apply hR.symm
  exact hab

example : Congruent 7 (-5) 23 := by
  apply implicit_symm (Congruent 7) 23 (-5)
  · guard_target =ₛ Congruent 7 23 (-5)
    exact congruent_twenty_three_neg_five
  · guard_target =ₛ IsEquivalence (Congruent 7)
    exact congruent_equivalence 7

-- The relation is explicit; only its laws are synthesized.
theorem local_laws {A : Type} (R : Relation A)
    [hR : IsEquivalence R] (a b : A) (hab : R a b) :
    equivalenceClass R a = equivalenceClass R b := by
  apply equivalenceClass_eq R a b
  guard_target =ₛ R a b
  exact hab

-- A class-typed local binder is available even when its call-site binder is explicit.
theorem register_local_laws {A : Type} (R : Relation A)
    (hR : IsEquivalence R) (a b : A) (hab : R a b) :
    equivalenceClass R a = equivalenceClass R b := by
  have : IsEquivalence R := inferInstance
  apply equivalenceClass_eq R a b
  exact hab

-- A named theorem is not globally registered by theorem declaration alone.
private def equalValues (f : Nat → Nat) : Relation Nat := fun a b => f a = f b

private theorem equalValues_laws (f : Nat → Nat) : IsEquivalence (equalValues f) :=
  { refl := fun _ => rfl
    symm := Eq.symm
    trans := Eq.trans }

example (f : Nat → Nat) (a b : Nat) (hab : f a = f b) :
    equivalenceClass (equalValues f) a = equivalenceClass (equalValues f) b := by
  fail_if_success have : IsEquivalence (equalValues f) := inferInstance
  letI : IsEquivalence (equalValues f) := equalValues_laws f
  apply equivalenceClass_eq (equalValues f) a b
  exact hab

-- Global registration is indexed by the relation, including its modulus.
example : IsEquivalence (Congruent 2) := inferInstance
example : IsEquivalence (Congruent 3) := inferInstance
example : IsEquivalence (Congruent 0) := inferInstance
example : IsEquivalence SameCardinality := inferInstance

-- Neither a relation on the same carrier nor an arbitrary relation is selected.
example {A : Type} (R S : Relation A) [IsEquivalence R] : True := by
  fail_if_success have : IsEquivalence S := inferInstance
  trivial

example : True := by
  fail_if_success have : IsEquivalence (fun a b : Nat => a < b) := inferInstance
  trivial

-- The caller can still explicitly supply the proof by its binder name.
example {A : Type} (R : Relation A) (hR : IsEquivalence R)
    (a b : A) (hab : R a b) :
    equivalenceClass R a = equivalenceClass R b := by
  apply equivalenceClass_eq R (hR := hR) a b
  exact hab

-- The map's invariance remains a separate, required mathematical argument.
theorem lift_exact {A B : Type} (R : Relation A)
    [IsEquivalence R] (f : A → B)
    (hf : ∀ a b, R a b → f a = f b) (a : A) :
    quotientLift R f hf (classOf R a) = f a := by
  exact quotientLift_classOf

theorem lift_rewrite {A B : Type} (R : Relation A)
    [IsEquivalence R] (f : A → B)
    (hf : ∀ a b, R a b → f a = f b) (a : A) :
    quotientLift R f hf (classOf R a) = f a := by
  rw [quotientLift_classOf]

-- Both concrete relations can be used together without changing a default.
example (a b : Int) (h2 : Congruent 2 a b) (h3 : Congruent 3 a b) :
    classOf (Congruent 2) a = classOf (Congruent 2) b ∧
    classOf (Congruent 3) a = classOf (Congruent 3) b := by
  constructor
  · apply (classOf_eq_iff (Congruent 2) a b).mpr
    exact h2
  · apply (classOf_eq_iff (Congruent 3) a b).mpr
    exact h3

#print axioms local_laws
#print axioms register_local_laws
#print axioms lift_exact
#print axioms lift_rewrite

end EquivalenceInstancesTests
