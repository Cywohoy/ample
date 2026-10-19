import Ample.Tactic.Arithmetic

open Ample

example (n : Nat) : 3 / n ≤ 3 := by arith
example (n : Int) : 3 / n ≤ 3 := by arith
example (a n : Nat) : a / n ≤ a := by arith
example (a n : Int) (ha : 0 ≤ a) : a / n ≤ a := by arith

example (m n : Nat) (h : m ≤ 3 / n) : m ≤ 3 := by
  suffices hSuffices : (m ≤ 3 / n) by arith
  exact h

example (m n : Int) (h : m ≤ 3 / n) : m ≤ 3 := by
  suffices hSuffices : (m ≤ 3 / n) by arith
  exact h

example (a m n : Int) (ha : 0 ≤ a) (h : m ≤ a / n) : m ≤ a := by
  arith

example (a m n : Nat) (h : m ≤ a / n) : m ≤ a := by arith

example (n m : Nat) (h : n * m = 3) : m ≤ 3 / n := by arith
example (n m : Int) (h : n * m = 3) : m ≤ 3 / n := by arith
example (n m : Int) (h : n * m = 3) : m = 3 / n := by arith
example (n m : Nat) (h : m * n = 3) : m = 3 / n := by arith

example (a b c : Nat) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by arith
example (a b c : Int) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by arith
example (a b c : Nat) (hc : 0 < c) (h : a < (b + 1) * c) : a / c ≤ b := by arith
example (a b c : Int) (hc : 0 < c) (h : a < (b + 1) * c) : a / c ≤ b := by arith

example (a b c : Nat) (h : a ≤ b) : a / c ≤ b / c := by arith
example (a b c : Int) (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by arith
example (a b c : Nat) (h : c ≤ b) (hc : 0 < c) : a / b ≤ a / c := by arith

example (a b : Int) (hb : b < 0) : a % b < -b := by arith
example (a b : Int) (hb : b ≠ 0) : a / b * b ≤ a := by arith
example (a b : Int) (hb : 0 < b) : a < (a / b + 1) * b := by arith
example (a b : Nat) : a / b * b ≤ a := by arith
example (a b : Int) (hb : b ≠ 0) : (a * b) / b = a := by arith
example (a b : Nat) (hb : 0 < b) : (a * b) / b = a := by arith

example (a b c : Int) (hc : 0 < c) (h : a ≤ b / c) : a * c ≤ b := by arith
example (a b c : Int) (hc : 0 < c) (h : a / c ≤ b) : a < (b + 1) * c := by arith
example (a b c : Nat) (hc : 0 < c) (h : a ≤ b / c) : a * c ≤ b := by arith
example (a b c : Nat) (hc : 0 < c) (h : a / c ≤ b) : a < (b + 1) * c := by arith

example (m n : Nat) (hn : 0 < n) (h : m * n ≤ 3 / n * n) : m ≤ 3 / n := by
  suffices hSuffices : (m * n ≤ 3 / n * n) by arith
  exact h

example (m n : Int) (hn : 0 < n) (h : m * n ≤ 3 / n * n) : m ≤ 3 / n := by
  suffices hSuffices : (m * n ≤ 3 / n * n) by arith
  exact h

example : True := by
  fail_if_success (have bad : (-3 : Int) / 2 ≤ -3 := by arith)
  fail_if_success (have bad : (3 : Nat) / 0 = 3 := by arith)
  trivial

example (h : (-2 : Int) * (-1) ≤ (-3) * (-1))
    (hGoal : (-2 : Int) ≤ -3) : (-2 : Int) ≤ -3 := by
  fail_if_success (clear hGoal; arith)
  exact hGoal

example (n m : Nat) (h : n * m = 3) (hn : n ≠ 0) : m ≤ 3 := by arith
example (n m : Nat) (h : n * m = 3) (hn : n ≠ 0) (hm : 3 < m) : False := by arith
example (n m : Int) (h : n * m = 3) (hn : 0 < n) (hm : 3 < m) : False := by arith
