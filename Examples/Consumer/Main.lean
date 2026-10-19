import Ample

open Ample

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
