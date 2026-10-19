import Ample.Tactic.GroupRules
import Ample.Tactic.Group
import Ample.Tactic.Auto

open Ample

section
variable {A : Type} (G H : Group A)

example (a b c : A) :
    G.op (G.op a b) (G.op (G.inv b) c) = G.op a c := by
  group_calc G

example (a b : A) :
    G.inv (G.op (G.inv a) b) = G.op (G.inv b) a := by
  group_calc G

example (a : A) (m n : Nat) :
    G.op (power G a m) (power G a n) = power G a (n + m) := by
  group_calc G

example (a : A) (z : Int) : integerPower G a (z - z) = G.id := by
  group_calc G

example (a b : A) (h : G.op a b = G.op b a) (n : Nat) :
    power G (G.op a b) n = G.op (power G a n) (power G b n) := by
  group_calc G

example (a b : A) (h : a = b) : a = b := by
  fail_if_success group_calc (0 : Nat)
  guard_hyp h : a = b
  exact h

example (a b : A) (h : a = b) : a = b := by
  group_calc G

example (a : A) : H.inv (H.inv a) = a := by
  fail_if_success group_calc G
  group_calc H

example (a b : A) : G.op a b = G.op a b := by
  fail_if_success have wrong : G.op a b = G.op b a := by group_calc G
  rfl

-- Group rules never enter arithmetic's restricted rule set.
example (a : A) : G.inv (G.inv a) = a := by
  fail_if_success arith
  group_calc G

end
