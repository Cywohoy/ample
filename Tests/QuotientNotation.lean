import Ample.Math.Cardinality

/-- info: fun q => q : Ample.QuotientType Eq → Ample.QuotientType Eq -/
#guard_msgs in
#check fun (q : Ample.QuotientType (A := Nat) Eq) => q

-- The scoped notation can be enabled without opening mathematical names.
section
open scoped Ample

/-- info: fun q => q : Nat / Eq → Nat / Eq -/
#guard_msgs in
#check fun (q : Nat / Eq) => q

/-- info: fun q => q = ⟦0⟧ : Nat / Eq → Prop -/
#guard_msgs in
#check fun (q : Nat / Eq) => q = ⟦0⟧

/-- info: fun q => q : Ample.QuotientType Eq → Ample.QuotientType Eq -/
#guard_msgs in
set_option pp.notation false in
#check fun (q : Nat / Eq) => q

example {A : Type} (R : Ample.Relation A) [Ample.IsEquivalence R] :
    (A / R) = Ample.QuotientType R := rfl
example (m n : Nat) : m / n + 1 = Nat.div m n + 1 := rfl

end

open Ample

-- The left operand determines the carrier, including larger universes.
example {A : Type u} (R : Relation A) [IsEquivalence R] :
    (A / R) = QuotientType (A := A) R := rfl
example : (Type / SameCardinality) = Cardinal := rfl
example : (Int / Congruent 2) = Parity := rfl

-- Quotients bind more tightly than arrows and products and associate left.
example {A B : Type} (R : Relation A) [IsEquivalence R] :
    (A / R → B) = (QuotientType R → B) := rfl
example {A B : Type} (R : Relation A) [IsEquivalence R] :
    (A / R × B) = (QuotientType R × B) := rfl
example {A B : Type} (R : Relation A) [IsEquivalence R] (S : Relation B) [IsEquivalence S] :
    (A / R × B / S) = (QuotientType R × QuotientType S) := rfl
example {A : Type} (R : Relation A) [IsEquivalence R] (S : Relation (A / R)) [IsEquivalence S] :
    (A / R / S) = QuotientType (A := QuotientType R) S := rfl

-- Existing quotient constructions and comparison rules need no conversions.
example {A : Type} (R : Relation A) [IsEquivalence R] (a : A) :
    A / R := classOf R a
example {A : Type u} (R : Relation A) [IsEquivalence R] (a : A) :
    (⟦a⟧ : A / R) = classOf R a := rfl
example {A B : Type} (R : Relation A) [IsEquivalence R] (F : A / R → B) (a : A) :
    F ⟦a⟧ = F (classOf R a) := rfl
example {A : Type} (R S : Relation A) [IsEquivalence R] [IsEquivalence S] (a : A) :
    ((⟦a⟧ : A / R), (⟦a⟧ : A / S)) = (classOf R a, classOf S a) := rfl
example {A : Type} (R : Relation A) [IsEquivalence R] (q : A / R) :
    ∃ a : A, q = ⟦a⟧ := quotient_exists_classOf R q
example (A : Type) : (⟦A⟧ : Cardinal) = cardinal A := rfl
example (a : Int) : (⟦a⟧ : Parity) = parityClass a := rfl
example {A : Type} (R : Relation A)
    [hR : IsEquivalence R]
    (a b : A)
    (hab : R a b) :
    (classOf R a : A / R) = classOf R b := by
  ext : 1
  exact equivalenceClass_eq R a b hab
example {A : Type} (R : Relation A) [IsEquivalence R] (q : A / R) :
    ∃ a, q = classOf R a := quotient_exists_classOf R q

-- Overloading must preserve arithmetic precedence and associativity.
example : 8 / 2 + 1 = 5 := by decide
example : 8 / 2 / 2 = 2 := by decide
example : 8 / (2 + 2) = 2 := by decide
example : (8 : Int) / 2 + 1 = 5 := by decide
example : (8 : Int) / 2 / 2 = 2 := by decide
example (m n : Nat) : m / n + 1 = Nat.div m n + 1 := rfl
example (m n : Int) : m / n + 1 = Int.ediv m n + 1 := rfl
