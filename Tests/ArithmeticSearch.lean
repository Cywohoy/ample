import Ample.Tactic.Arithmetic

open Course

set_option maxHeartbeats 60000

-- Fin의 경계와 몫의 계산을 함께 사용한다.
example (m n : Nat) (y : Fin m × Fin n) :
    (y.1.val + y.2.val * m) / m = y.2.val := by
  arith

example (m n : Nat) (y : Fin m × Fin n) :
    (y.1.val + y.2.val * m) % m = y.1.val := by
  arith

-- 원소를 만드는 데 필요한 경계를 중간 suffices 없이 확인한다.
example (m n : Nat) (y : Fin m × Fin n) :
    y.1.val + y.2.val * m < m * n := by
  arith

example (m n : Nat) (y : Fin m × Fin n) :
    y.2.val * m + y.1.val < n * m := by
  arith

-- 나머지의 정리가 만든 부등식에 다시 몫의 정리를 적용한다.
example (i j m n : Nat) (hi : i < m) (hj : j < n) :
    (i + j * m) % (m * n) = i + j * m := by
  arith

example (i j m n : Int) (hi0 : 0 ≤ i) (hi : i < m)
    (hj : j < n) : i + j * m < m * n := by
  arith

-- 한 목표를 해결한 뒤에도 나머지 목표를 유지한다.
example (m n : Nat) (y : Fin m × Fin n) :
    y.1.val + y.2.val * m < m * n ∧
    (y.1.val + y.2.val * m) / m = y.2.val := by
  constructor
  · arith
  · arith

example (a b c : Nat) (h : a < b) : a * c ≤ (b - 1) * c := by
  arith

example (a b c : Nat) (h : a + 2 ≤ b) : a * c ≤ (b - 2) * c := by
  arith

example (a b c : Int) (h : a + 2 ≤ b) (hc : 0 ≤ c) :
    a * c ≤ (b - 2) * c := by
  arith

-- 필요한 조건이 없는 목표에서는 실패하고 기존 가정을 보존한다.
example (a b c : Int) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  fail_if_success (clear hc; arith)
  arith

example (i j m n : Nat) (hi : i < m) (hj : j < n) : i + j * m < m * n := by
  fail_if_success (clear hi; arith)
  fail_if_success (clear hj; arith)
  arith
