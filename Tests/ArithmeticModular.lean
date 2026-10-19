import Ample.Tactic.Arithmetic

open Course

-- 자연수와 정수에서 연산 전후의 나머지를 비교한다.

example (a b c d n : Nat) (ha : a % n = b % n) (hc : c % n = d % n) :
    (a + c) % n = (b + d) % n := by
  arith

example (a b c d n : Nat) (ha : a % n = b % n) (hc : c % n = d % n) :
    (a * c) % n = (b * d) % n := by
  arith

example (a b c d n : Int) (ha : a % n = b % n) (hc : c % n = d % n) :
    (a + c) % n = (b + d) % n := by
  arith

example (a b c d n : Int) (ha : a % n = b % n) (hc : c % n = d % n) :
    (a * c) % n = (b * d) % n := by
  arith

example (a b c d n : Int) (ha : a % n = b % n) (hc : c % n = d % n) :
    (a - c) % n = (b - d) % n := by
  arith

example (a b n k : Nat) (ha : a % n = b % n) :
    a ^ k % n = b ^ k % n := by
  arith

example (a b n : Nat) : ((a % n) + (b % n)) % n = (a + b) % n := by
  arith

example (a b n : Nat) : ((a % n) * (b % n)) % n = (a * b) % n := by
  arith

example (a b n : Int) : ((a % n) - (b % n)) % n = (a - b) % n := by
  arith

example (a b n : Int) : ((a % n) * (b % n)) % n = (a * b) % n := by
  arith

example (a b n : Int) (h : a % n = b % n) : (-a) % n = (-b) % n := by
  arith

example (a n : Int) : a % (-n) = a % n := by
  arith

example (a n : Nat) (h : n ∣ a) : a % n = 0 := by
  arith

example (a n : Nat) (h : a % n = 0) : n ∣ a := by
  arith

example (a n : Int) (h : n ∣ a) : a % n = 0 := by
  arith

example (a n : Int) (h : a % n = 0) : n ∣ a := by
  arith

example (a b c d n : Int) (ha : a % n = b % n) (hc : c % n = d % n) :
    (a + c) % n = (b + d) % n := by
  suffices hSuffices : (a % n = b % n ∧ c % n = d % n) by arith
  constructor
  · exact ha
  · exact hc

-- 자연수의 뺄셈에는 정수와 같은 나머지 보존 법칙을 적용하지 않는다.
example (a b c d n : Nat) (_ha : a % n = b % n) (_hc : c % n = d % n)
    (hGoal : (a - c) % n = (b - d) % n) :
    (a - c) % n = (b - d) % n := by
  fail_if_success (clear hGoal; arith)
  exact hGoal
