import Ample

open Ample

theorem composition_notation_from_another_project {A B C : Type}
    (f : A → B) (g : B → C) : g ∘ f = compose g f := by
  rfl

theorem composition_simp_from_another_project {A B : Type}
    (f : A → B) : f ∘ identity A = f := by
  simp

theorem native_composition_from_another_project {A B : Type}
    (f : A → B) : Function.comp f (identity A) = f := by
  change compose f (identity A) = f
  simp

theorem equality_from_another_project (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  apply_fun (fun x => x + 1) at h
  exact h

theorem arithmetic_from_another_project (n : Nat) : n + 1 > n := by
  arith

theorem quotient_from_another_project {A : Type} (R : Relation A) :
    (A / R) = QuotientType R := rfl

def quotient_element_from_another_project {A : Type} (R : Relation A) (a : A) :
    A / R := ⟦a⟧

theorem group_from_another_project {A : Type} (G : Group A) (a : A) :
    G.op a (G.inv a) = G.id := by
  group_calc G

def main : IO Unit := IO.println "External Ample import checked without textbook dependencies."
