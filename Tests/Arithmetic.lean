import Ample.Tactic.Arithmetic
import Ample.Math.Functions

/-! 원소 표기의 자동 정리, 전술의 범위와 기본 옵션 전달을 검사한다. -/

-- Ample를 열지 않은 곳에서는 Lean의 기본 전술을 유지한다.
example (x : Nat) : Ample.Elem (fun n : Nat => 2 ≤ n) := by
  exists (x + 2)
  fail_if_success omega
  dsimp
  omega

namespace ArithmeticTests

open Ample

example (x : Nat) : Elem (fun n : Nat => 2 ≤ n) := by
  exists (x + 2)
  omega

example (x : Nat) : Elem positives := by
  exists (x + 1)
  omega

example (s : Elem positives) : s.val - 1 + 1 = s.val := by
  have hs := s.property
  omega

-- 증명 성분이 목표에 들어 있어도 값 계산과 원소 조건을 차례로 정리한다.
example (s : Elem (fun n : Nat => 2 ≤ n)) :
    s.val - 2 + 2 = s.val := by
  rcases s with ⟨y, hy⟩
  omega

example (y : Nat) : y - 2 + 2 = y ↔ 2 ≤ y := by
  constructor
  · intro h
    omega
  · intro hy
    -- 하한 조건이 없으면 이 등식은 성립하지 않는다.
    fail_if_success (clear hy; omega)
    omega

example (x : Nat) : x + 0 = x := by
  omega

example (x y : Int) (h : x ≤ y) : x ≤ y := by
  omega (config := { splitDisjunctions := false })

example (x : Int) : 2 * x ≠ 5 := by
  intro h
  omega

end ArithmeticTests

-- scoped 전술은 위 namespace를 닫으면 비활성화된다.
example (x : Nat) : Ample.Elem (fun n : Nat => 2 ≤ n) := by
  exists (x + 2)
  fail_if_success omega
  dsimp
  omega
