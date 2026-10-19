import Ample.Math.GroupBasics

open Ample

-- 등식의 대입과 가정으로 주어진 사실의 사용은 공통 추론에 속한다.
example (A : Type) (f : A → A) (x y : A) (h : x = y) : f x = f y := by
  arith

example (A : Type) (op : A → A → A) (a b c : A)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z)) :
    op (op a b) c = op a (op b c) := by
  arith

-- 군의 구조에 들어 있는 연산 법칙은 산술 전술이 자동으로 가져오지 않는다.
example (A : Type) (G : Group A) (a b c : A) :
    G.op (G.op a b) c = G.op a (G.op b c) := by
  fail_if_success arith
  exact G.assoc a b c

example (A : Type) (G : Group A) (a : A) : G.op G.id a = a := by
  fail_if_success arith
  exact G.id_left a

@[irreducible] def numericCode (n : Nat) : Nat := n + n

@[grind =] theorem numericCode_eq (n : Nat) : numericCode n = n + n := by
  unfold numericCode

-- 일반 grind 규칙으로 등록한 정리는 arith의 산술 규칙에 추가되지 않는다.
example (n : Nat) : numericCode n = n + n := by
  fail_if_success arith
  exact numericCode_eq n

example (n : Nat) (h : numericCode n = n + n) : numericCode n = n + n := by
  arith
