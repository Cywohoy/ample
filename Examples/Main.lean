import Ample

open Course
open scoped Course.Auto

theorem odd_double (n : Int) : 2 * n ≠ 5 := by
  arith

theorem pair_comparison (a b c d : Nat) (h : (a, b) = (c, d)) : a = c := by
  indisc at h with h₁ h₂
  exact h₁

theorem inverse_of_inverse {A : Type} (G : Group A) (a : A) : G.inv (G.inv a) = a := by
  group_calc G

def main : IO Unit := IO.println "Ample: arithmetic, equality comparison, and group calculation checked."
