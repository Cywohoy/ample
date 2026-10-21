import Ample.Math.Cardinality
import Ample.Tactic.Auto

open Ample

-- The quotient set contains sets; its element type packages membership evidence.
example {A : Type} (R : Relation A) (a : A) :
    equivalenceClass R a ∈ quotientSet R := by
  exact equivalenceClass_mem_quotientSet R a

-- A quotient element supplies all the evidence needed to select a representative.
example {A : Type} (R : Relation A) (q : QuotientType R) :
    q = classOf R (quotientRepr R q) := by
  exact quotientRepr_spec q

-- A class-constant function has the prescribed value for any representative of the class.
example {A B : Type} (R : Relation A) (hR : IsEquivalence R)
    (q : QuotientType R) (a : A)
    (hqa : q = classOf R a)
    (f : A → B) (hf : ∀ a b, R a b → f a = f b) :
    f (quotientRepr R q) = f a := by
  let chosen := quotientRepr R q
  have hab : R chosen a := by
    apply (classOf_eq_iff R hR chosen a).mp
    exact (quotientRepr_spec q).symm.trans hqa
  exact hf chosen a hab

example {A : Type} (R : Relation A) (a : A) :
    (classOf R a).val = equivalenceClass R a := by rfl

example {A : Type} (R : Relation A) (q : QuotientType R) :
    ∃ a : A, q = classOf R a := by
  exact quotient_exists_classOf R q

example {A : Type} (R : Relation A) (hR : IsEquivalence R) (a b : A) :
    classOf R a = classOf R b ↔ R a b := by
  exact classOf_eq_iff R hR a b

-- Class comparison is one registered rule in either direction.
example (a b : Int) (hab : Congruent 2 a b) :
    parityClass a = parityClass b := by
  ext : 1
  guard_target =ₛ Congruent 2 a b
  exact hab

example (a b : Int) (h : parityClass a = parityClass b) :
    Congruent 2 a b := by
  indisc : 1 at h with hab
  guard_hyp hab :ₛ Congruent 2 a b
  exact hab

example (a b : Int) (hab : Congruent 2 a b) :
    parityClass a = parityClass b := by
  ext at hab with equality : parityClass a = parityClass b
  exact equality

example (a b : Int) (h : parityClass a = parityClass b) :
    Congruent 2 a b := by
  indisc (parityClass a = parityClass b)
  exact h

-- Natural numerals and arbitrary representatives retain the cardinal interface.
example (n : Nat) : cardinal (Fin n) = n := by
  ext : 1
  guard_target =ₛ SameCardinality (Fin n) (Fin n)
  exact sameCardinality_refl _

example (A B : Type) (h : SameCardinality A B) : cardinal A = cardinal B := by
  ext at h with equality : cardinal A = cardinal B
  exact equality

example (a b : Cardinal) (h : a = b) : a ≤ b := by
  exact Cardinal.le_of_eq h

-- Class invariance establishes the prescribed value at every representative.
example (f : Int → Nat) (hf : ∀ a b, Congruent 2 a b → f a = f b) (a : Int) :
    quotientLift (Congruent 2) (congruent_equivalence 2) f hf (parityClass a) = f a := by
  exact quotientLift_classOf

-- Any representative selector yields the same lifted function, including
-- quotients over a larger universe than the codomain.
example {A : Type 1} {B : Type}
    (R : Relation A) (hR : IsEquivalence R)
    (f : A → B) (hf : ∀ a b, R a b → f a = f b)
    (pick : (q : QuotientType R) → {a : A // q = classOf R a}) :
    (fun q => f (pick q).val) = quotientLift R hR f hf := by
  apply quotientLift_unique R f
  · intro a
    apply hf
    apply (classOf_eq_iff R hR _ a).mp
    exact (pick (classOf R a)).property.symm
  · intro a
    exact quotientLift_classOf

-- A non-invariant map cannot be extended with the prescribed equation.
example : ¬ ∃ F : Parity → Int, ∀ a : Int, F (parityClass a) = a := by
  rintro ⟨F, h⟩
  have h0 := h 0
  rw [parityClass_zero_two, h 2] at h0
  arith

-- Matching must not select unresolved inputs of an existing goal.
open Lean Meta in
run_meta do
  let input ← mkFreshExprMVar (mkConst ``Int)
  let lhs ← mkAppM ``Ample.parityClass #[input]
  let zero := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
  let rhs ← mkAppM ``Ample.parityClass #[zero]
  let comparison ← Ample.Automation.registeredComparison? (← mkEq lhs rhs)
  unless comparison.isNone do throwError "A comparison matched an unresolved input."
  if ← input.mvarId!.isAssigned then throwError "Comparison matching assigned an existing input."

#print axioms quotient_exists_classOf
#print axioms quotientLiftData
#print axioms quotientLift_unique

-- Relation is a transparent carrier alias. Rewriting a representative equation
-- must compose with computation rules whose arguments use a named quotient.
private noncomputable def nextParity : Parity → Parity :=
  quotientLift
    (Congruent 2)
    (congruent_equivalence 2)
    (fun a => parityClass (a + 1))
    (by
      intro a b hab
      apply (parityClass_eq_iff (a + 1) (b + 1)).mpr
      unpack hab with ⟨k, hk⟩
      exists k
      arith)

private theorem nextParity_class (a : Int) :
    nextParity (parityClass a) = parityClass (a + 1) := by
  exact quotientLift_classOf

open scoped Ample Classical in
example (q : Parity) : nextParity (nextParity q) = q := by
  unpack quotient_exists_classOf (Congruent 2) q with ⟨a, ha⟩
  rw [ha, nextParity_class, nextParity_class]
  ext
  exists 1
  arith
