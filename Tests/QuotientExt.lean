import Ample.Tactic.Ext

def equalitySetoid : Setoid Nat where
  r := Eq
  iseqv := { refl := fun _ => rfl, symm := Eq.symm, trans := Eq.trans }

-- Importing the module alone keeps native ext.
example (a b : Nat) (h : a = b) :
    Quotient.mk equalitySetoid a = Quotient.mk equalitySetoid b := by
  fail_if_success ext
  apply Quotient.sound
  exact h

open Ample

example (a b : Nat) (h : a = b) :
    Quotient.mk equalitySetoid a = Quotient.mk equalitySetoid b := by
  ext : 1
  guard_target =ₛ a = b
  exact h

example (a b : Nat) (h : a = b) :
    Quotient.mk equalitySetoid a = Quotient.mk equalitySetoid b := by
  ext1
  exact h

example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (Quotient.mk equalitySetoid a, Quotient.mk equalitySetoid c) =
      (Quotient.mk equalitySetoid b, Quotient.mk equalitySetoid d) := by
  ext!
  · guard_target =ₛ a = b
    exact hab
  · guard_target =ₛ c = d
    exact hcd

example (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    (fun x => Quotient.mk equalitySetoid (f x)) =
      (fun x => Quotient.mk equalitySetoid (g x)) := by
  ext! x
  guard_target =ₛ f x = g x
  exact h x

example (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    (fun x => Quotient.mk equalitySetoid (f x)) =
      (fun x => Quotient.mk equalitySetoid (g x)) := by
  ext x : 1
  guard_target = Quotient.mk equalitySetoid (f x) = Quotient.mk equalitySetoid (g x)
  ext : 1
  exact h x

example (f g : Nat × Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext ⟨x, y⟩ : 1
  exact h (x, y)

example (a b : Nat) (h : a = b) : a = b := by
  fail_if_success ext
  exact h

example (q r : Quotient equalitySetoid) (h : q = r) : q = r := by
  fail_if_success ext
  exact h

example : True := by
  fail_if_success ext
  trivial

example (a b : Nat) (h : a = b) : a = b := by
  ext : 0
  exact h
