import Ample.Math.CardinalArithmetic

open Ample

-- A quotient requires equivalence laws even before a lift is constructed.
example : True := by
  fail_if_success let q : Nat / (fun _ _ => False) := ⟦0⟧
  trivial

example {A : Type u} (R : Relation A) [IsEquivalence R] (a b : A)
    (h : R a b) : (classOf R a : A / R) = classOf R b := by
  exact classOf_sound R h

example {A : Type u} (R : Relation A) [IsEquivalence R] (a b : A)
    (h : classOf R a = classOf R b) : R a b := by
  exact classOf_exact R h

-- Laws are shared with relational rewriting; there is no second law record.
example {A : Type u} (R : Relation A) [hR : IsEquivalence R]
    (a b c : A) (hab : R a b) (hbc : R b c) : R a c := by
  rw [hab]
  exact hbc

example {A : Type u} {B : Type v} {S : Set A} {T : Set B}
    (f : A → B) (hf : ∀ x, x ∈ S → f x ∈ T) (x : Elem S) :
    (Elem.map f hf x).val = f x.val := by
  exact Elem.map_val

example {A : Type u} {B : Type v} {S : Set A} {T : Set B}
    (f : A → B) (hf : ∀ x, x ∈ S → f x ∈ T) (x : Elem S) :
    (Elem.map f hf x).val = f x.val := by
  rw [Elem.map_val]

def interfaceSwap (A : Type u) (B : Type v) : Equiv (A × B) (B × A) :=
  { toFun := fun p => (p.2, p.1), invFun := fun p => (p.2, p.1)
    left_inv := fun _ => rfl, right_inv := fun _ => rfl }

example {A : Type u} {B : Type v} (e : Equiv A B) :
    e.trans e.symm = Equiv.refl A := by
  apply Equiv.ext
  intro a
  exact e.left_inv a

example {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    (e : Equiv A B) (d : Equiv C D) :
    Bijective (e.arrow d).toFun := (e.arrow d).bijective

example {A : Type u} {B : Type v} (f : A → B) (hf : Bijective f) :
    (Equiv.ofBijective f hf).toFun = f := rfl

section
variable {A : Type u} {B : Type v} {C : Type w}
variable (R : Relation A) (S : Relation B)
variable [IsEquivalence R] [IsEquivalence S]
variable (f : A → B → C)
variable (hf : ∀ a a' b b', R a a' → S b b' → f a b = f a' b')

example (a : A) (b : B) :
    quotientLift₂ R S f hf ⟦a⟧ ⟦b⟧ = f a b := by
  exact quotientLift₂_classOf

example (a : A) (b : B) :
    quotientLift₂ R S f hf ⟦a⟧ ⟦b⟧ = f a b := by
  rw [quotientLift₂_classOf]

example (p : A / R) (q : B / S) :
    ∃ a b, p = ⟦a⟧ ∧ q = ⟦b⟧ := by
  apply quotientInductionOn₂ R S p q
  intro a b
  exists a, b

end

example {A : Type u} {B : Type v} (R : Relation A) (S : Relation B)
    [IsEquivalence R] [IsEquivalence S]
    (f : A → B) (hf : Rewriting.Action R S f) (a : A) :
    quotientMap R S f hf ⟦a⟧ = classOf S (f a) := by
  exact quotientMap_classOf

example {A : Type u} {B : Type v} (R : Relation A) (S : Relation B)
    [IsEquivalence R] [IsEquivalence S]
    (f : A → B) (hf : Rewriting.Action R S f) (a : A) :
    quotientMap R S f hf ⟦a⟧ = classOf S (f a) := by
  rw [quotientMap_classOf]

example (A B : Type) : cardinal (A ⊕ B) = cardinal A + cardinal B := by
  exact cardinal_sum A B
example (A B : Type) : cardinal (A ⊕ B) = cardinal A + cardinal B := by
  rw [cardinal_sum]
example (A B : Type) : cardinal (A × B) = cardinal A * cardinal B := by
  rw [cardinal_product]
example (A B : Type) : cardinal (A → B) = cardinal B ^ cardinal A := by
  rw [cardinal_arrow]

#print axioms quotientLift₂_classOf
#print axioms quotientMap_compose
#print axioms Equiv.ext

-- Cardinal addition is constructed with two unary lifts. The binary helper
-- must give the same operation, independently of proof arguments.
example (A B : Type) :
    Cardinal.addToType A (cardinal B) = cardinal (A ⊕ B) := by
  exact Cardinal.addToType_cardinal A B

example (A B : Type) :
    Cardinal.addToType A (cardinal B) = cardinal (A ⊕ B) := by
  rw [Cardinal.addToType_cardinal]

example :
    Cardinal.add =
      quotientLift₂ SameCardinality SameCardinality
        (fun A B : Type => cardinal (A ⊕ B))
        (by
          intro A C B D hAC hBD
          ext
          apply sameCardinality_sum hAC hBD) := by
  apply quotient_funext SameCardinality
  intro A
  apply quotient_funext SameCardinality
  intro B
  rw [Cardinal.add, quotientLift_classOf]
  rw [Cardinal.addToType, quotientLift_classOf,
    quotientLift₂_classOf]

#print axioms Cardinal.addToType_respects
#print axioms cardinal_sum
