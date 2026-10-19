import Ample.Tactic.Arithmetic
import Ample.Tactic.Auto

open Ample

-- 다항식, 자연수의 뺄셈, 몫과 나머지를 같은 산술 전술로 다룬다.

example (m n : Nat) : m * (1 + n) = m + n * m := by
  arith

example (m n : Nat) (hn : 1 ≤ n) : m * n = m + (n - 1) * m := by
  arith

example (m n : Nat) (ym : Fin m) (yn : Fin n) :
    ym.val + yn.val * m < m * n := by
  have hm := ym.isLt
  have hn := yn.isLt
  calc
    ym.val + yn.val * m < m + yn.val * m := by arith
    _ = (yn.val + 1) * m := by arith
    _ ≤ n * m := by arith
    _ = m * n := by arith

example (k m n : Nat) (hk : k < m * n) : k / m < n := by
  arith

example (k m : Nat) (hm : 0 < m) : k % m < m := by
  arith

example (i j m : Nat) (hi : i < m) : (i + j * m) / m = j := by
  arith

example (i j m : Nat) (hi : i < m) : (i + j * m) % m = i := by
  arith

example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  arith

example (ym : Fin m) : ym.val % m = ym.val := by
  suffices hSuffices : (ym.val < m) by arith
  guard_target =ₛ ym.val < m
  exact ym.isLt

example (k m n : Nat) (hk : k < m * n) : k / m < n := by
  suffices hSuffices : (k < m * n) by arith
  exact hk

example (i j : Nat) (hij : i = j) : i + 2 = j + 2 := by
  suffices hSuffices : (i = j) by arith
  exact hij

example (P : Prop) (h : P) : P := by
  fail_if_success (clear h; suffices hSuffices : True by arith)
  exact h

-- 한 명제로 입력한 논리곱은 자동으로 나누지 않는다.
example (a b c d : Nat) (ha : a < b) (hc : c ≤ d) : a + c < b + d := by
  suffices hSuffices : (a < b ∧ c ≤ d) by arith
  guard_target =ₛ a < b ∧ c ≤ d
  constructor
  · exact ha
  · exact hc

-- 자연수의 몫과 나머지가 모두 같으면 원래 수도 같다.
example (x y m : Nat)
    (h : x % m = y % m ∧ x / m = y / m) : x = y := by
  arith

example (x y m : Nat)
    (hr : x % m = y % m) (hq : x / m = y / m) : x = y := by
  fail_if_success (clear hq; suffices hSuffices : (x % m = y % m) by arith)
  suffices hSuffices : (x % m = y % m /\ x / m = y / m) by arith
  guard_target =ₛ x % m = y % m ∧ x / m = y / m
  constructor
  · exact hr
  · exact hq

example (x y : Nat) (h : x % 0 = y % 0 ∧ x / 0 = y / 0) : x = y := by
  arith

-- 정수에도 같은 비교를 사용하며 나누는 수의 부호는 가정하지 않는다.
example (x y m : Int)
    (h : x % m = y % m ∧ x / m = y / m) : x = y := by
  arith

example (x y m : Int)
    (hr : x % m = y % m) (hq : x / m = y / m) : x = y := by
  suffices hSuffices : (x % m = y % m ∧ x / m = y / m) by arith
  constructor
  · exact hr
  · exact hq

-- 정수의 나머지와 몫의 경계·계산에 필요한 가정을 확인한다.
example (a m : Int) (hm : 0 < m) : a % m < m := by
  arith

example (a m : Int) (hm : m ≠ 0) : 0 ≤ a % m := by
  arith

example (a m : Int) (ha : 0 ≤ a) (hm : a < m) : a % m = a := by
  fail_if_success (clear ha; suffices hSuffices : (a < m) by arith)
  arith

example (a m : Int) (ha : 0 ≤ a) (hm : a < m) : a / m = 0 := by
  arith

example (a b m : Int) (hm : m ≠ 0) : (a + b * m) / m = a / m + b := by
  arith

example (a b m : Int) : (a + b * m) % m = a % m := by
  arith

example (a b m : Int) (hm : 0 < m) (ha : a < b * m) : a / m < b := by
  arith

example (a b m : Int) (h : a ≤ b) (hm : 0 ≤ m) : a * m ≤ b * m := by
  arith

example (a m : Int) : a % m + m * (a / m) = a := by
  arith

-- Lean의 기존 suffices 선언도 같은 범위에서 사용할 수 있다.
example (m : Nat) (ym : Fin m) : ym.val % m = ym.val := by
  suffices h : ym.val < m by
    exact Nat.mod_eq_of_lt h
  exact ym.isLt

example (m : Nat) (ym : Fin m) : ym.val % m = ym.val := by
  suffices h : ym.val < m from Nat.mod_eq_of_lt h
  exact ym.isLt

example (m : Nat) (ym : Fin m) : ym.val % m = ym.val := by
  suffices ym.val < m by
    exact Nat.mod_eq_of_lt this
  exact ym.isLt

namespace WithAuto

open scoped Ample.Auto

example (m : Nat) (ym : Fin m) :
    ym.val % m = ym.val ∧ ym.val / m = 0 := by
  constructor
  · suffices hSuffices : (ym.val < m) by arith
    exact ym.isLt
  · suffices hSuffices : (ym.val < m) by arith
    exact ym.isLt

example (P : Prop) (h : P) : P := by
  fail_if_success (clear h; suffices hSuffices : True by arith)
  exact h

example (x y m : Nat)
    (h : x % m = y % m ∧ x / m = y / m) : x = y := by
  suffices hSuffices : (x % m = y % m ∧ x / m = y / m) by arith
  constructor
  · exact h.left
  · exact h.right

end WithAuto

-- The removed shorthand must not be accepted, even when its bridge is easy.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  if env.contains `Ample.ampleSuffices then
    throwError "The implicit suffices extension must not be registered."
  for input in ["suffices True", "suffices (0 < 1)"] do
    match Parser.runParserCategory env `tactic input with
    | .ok _ => throwError "'{input}' must require an explicit connecting proof."
    | .error _ => pure ()
