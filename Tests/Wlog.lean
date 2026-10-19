import Ample.Tactic.Wlog
import Lean.Elab.Tactic.Omega

open Ample

theorem wlog_swap (a b : Int) : a + b = b + a := by
  wlog hab : a ≤ b generalizing a b with ordered
  · have hba : b ≤ a := by omega
    symm
    exact ordered b a hba
  · exact Int.add_comm a b

theorem wlog_dependencies (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    0 < a + b ∧ a + b = b + a := by
  wlog hab : a ≤ b generalizing a b with ordered
  · have hba : b ≤ a := by omega
    have reverse := ordered b a hb ha hba
    constructor
    · omega
    · exact reverse.right.symm
  · constructor
    · omega
    · exact Int.add_comm a b

theorem wlog_default (P : Prop) : P ∨ ¬ P := by
  wlog hp : P
  · right
    exact hp
  · left
    exact hp

theorem wlog_restore (n : Nat) : n = n := by
  fail_if_success wlog h : (0 : Nat) generalizing n
  rfl

#print axioms wlog_swap
#print axioms wlog_default

