import Ample.Math.Cardinality
import Ample.Tactic.Auto

open Ample

private def fromTwo : Set Nat := fun n => 2 ≤ n

-- 같은 모듈을 가져와도 자동 정리 범위를 열기 전의 증명에는 영향을 주지 않는다.
example (x : Nat) (h : x ∈ fromTwo) : 2 ≤ x := by
  guard_hyp h : x ∈ fromTwo
  exact h

namespace AutoNormalizeTests

open scoped Ample.Auto

-- 이름 붙인 집합의 원소 표기는 명시적으로 펼칠 때까지 유지한다.
example (x : Nat) (h : x ∈ fromTwo) : 2 ≤ x := by
  guard_hyp h :ₛ x ∈ fromTwo
  expand at h
  guard_hyp h :ₛ 2 ≤ x
  exact h

example {A : Type} (S : Set A) (x : A) (h : x ∈ S) : x ∈ S := by
  guard_hyp h :ₛ x ∈ S
  guard_target =ₛ x ∈ S
  exact h

example (a : Int) (h : ¬ a < 0) : 0 ≤ a := by
  guard_hyp h :ₛ 0 ≤ a
  exact h

example (a : Int) (h : 0 ≤ a) : ¬ a < 0 := by
  guard_target =ₛ 0 ≤ a
  exact h

example (n : Nat) (h : ¬ n < 0) : ¬ n < 0 := by
  guard_hyp h :ₛ 0 ≤ n
  guard_target =ₛ 0 ≤ n
  exact h

-- 이중 부정은 고전논리를 명시한 범위에서만 정리한다.
example (P : Prop) (h : ¬¬ P) : P := by
  guard_hyp h :ₛ ¬¬ P
  classical
  guard_hyp h :ₛ P
  exact h

example (P : Prop) (h : P) : ¬¬ P := by
  guard_target =ₛ ¬¬ P
  classical
  guard_target =ₛ P
  exact h

example (P Q : Prop) (h : ¬¬ P → ¬¬ Q) : ¬¬ P → ¬¬ Q := by
  classical
  guard_hyp h :ₛ P → Q
  guard_target =ₛ P → Q
  exact h

-- 한 분기의 classical은 다른 분기와 뒤의 선언으로 넘어가지 않는다.
example (P : Prop) (h : ¬¬ P) : P ∧ ¬¬ P := by
  constructor
  · classical
    guard_hyp h :ₛ P
    exact h
  · guard_hyp h :ₛ ¬¬ P
    guard_target =ₛ ¬¬ P
    exact h

example (P : Prop) (h : ¬¬ P) : ¬¬ P := by
  guard_hyp h :ₛ ¬¬ P
  guard_target =ₛ ¬¬ P
  exact h

-- 경우를 나눈 뒤에는 새 가정과 목표의 이중 부정도 정리한다.
example (P : Prop) (h : ¬¬ P) : P := by
  by_cases hp : P
  · guard_hyp h :ₛ P
    have hn : ¬¬ P := by
      guard_target =ₛ P
      exact h
    guard_hyp hn :ₛ P
    exact hn
  · guard_hyp h :ₛ P
    exact False.elim (hp h)

example (P : Prop) (h : ¬¬ P) : P ∧ ¬¬ P := by
  constructor
  · by_cases hp : P
    · exact h
    · exact False.elim (hp h)
  · guard_hyp h :ₛ ¬¬ P
    guard_target =ₛ ¬¬ P
    exact h

example (P Q : Prop) (h : ¬¬ P) : P := by
  by_cases Q <;> exact h

example (P Q : Prop) (hp : ¬¬ P) (hq : ¬¬ Q) : P ∧ Q := by
  constructor
  all_goals by_cases h : True
  all_goals first | exact hp | exact hq

example (P : Prop) (h : ¬¬ P) : P := by
  by_contra hn
  guard_hyp h :ₛ P
  exact hn h

set_option ample.autoNormalize false in
example (P : Prop) (h : ¬¬ P) : ¬¬ P := by
  classical
  guard_hyp h :ₛ ¬¬ P
  guard_target =ₛ ¬¬ P
  exact h

set_option ample.autoNormalize false in
example (P : Prop) (h : ¬¬ P) : P := by
  by_cases hp : P
  · guard_hyp h :ₛ ¬¬ P
    exact hp
  · guard_hyp h :ₛ ¬¬ P
    exact False.elim (h hp)

section
open scoped Classical

example (P : Prop) (h : ¬¬ P) : P := by
  guard_hyp h :ₛ P
  exact h

example (P : Prop) (h : P) : ¬¬ P := by
  guard_target =ₛ P
  exact h

example (P : Nat → Prop) (h : ∀ n, ¬¬ P n) : ∀ n, P n := by
  guard_hyp h :ₛ ∀ n, P n
  intro n
  exact h n

-- 원소 표기를 이미 정리했어도 여집합의 정의를 한 층씩 펼칠 수 있다.
example {A : Type} (S : Set A) : Sᶜᶜ ⊆ S := by
  intro x hxScc
  expand at hxScc
  guard_hyp hxScc :ₛ ¬ (x ∈ Sᶜ)
  expand at hxScc
  guard_hyp hxScc :ₛ x ∈ S
  exact hxScc

end

example (P : Prop) (h : ¬¬ P) : ¬¬ P := by
  guard_hyp h :ₛ ¬¬ P
  guard_target =ₛ ¬¬ P
  exact h

-- intro와 have로 새로 생긴 가정도 다음 단계에서 정리된다.
example (a : Int) : ¬ a < 0 → 0 ≤ a := by
  intro h
  guard_hyp h :ₛ 0 ≤ a
  exact h

example (s : Elem (fun n : Nat => 2 ≤ n)) : 2 ≤ s.val := by
  have h := s.property
  guard_hyp h : 2 ≤ s.val
  exact h

-- 지역 함수의 정의와 부분타입의 값 계산은 자동으로 정리한다.
theorem countably_fromTwo :
    IsCountablyInfinite (Elem (fun n : Nat => 2 ≤ n)) := by
  ext : 1
  let f (x : Nat) : Elem (fun n : Nat => 2 ≤ n) := by
    exists x + 2
    omega
  exists f
  constructor
  · intro x y hxy
    omega
  · intro y
    exists y.val - 2
    ext : 1
    have hy := y.property
    omega

-- 함수나 순서쌍의 등식을 보이는 논증에는 여전히 명시적으로 ext를 쓴다.
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext x : 1
  exact h x

example (a b c d : Nat) (ha : a = c) (hb : b = d) :
    (a, b) = (c, d) := by
  ext : 1
  · exact ha
  · exact hb

-- 순서쌍의 성분이 Fin이면 깊이를 지정하여 성분의 등식에서 멈출 수 있다.
example {A B : Type} {m n : Nat}
    (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Injective (fun p : Fin m × Fin n => (fA p.1, fB p.2)) := by
  intro x y hxy
  have ha := congrArg Prod.fst hxy
  have hb := congrArg Prod.snd hxy
  ext : 1
  · apply hA.left
    exact ha
  · apply hB.left
    exact hb

-- 자동 정리가 이미 참인 목표를 닫아 뒤의 증명 단계를 없애지는 않는다.
example (x : Nat) : x = x := by
  rfl

example (S : Set Nat) (s t : Elem S) (h : s = t) : s = t := by
  guard_hyp h : s = t
  exact h

example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP hPQ
  apply hPQ
  exact hP

-- 중첩된 증명과 세미콜론, 모든 목표에 적용하는 전술도 보통의 문법으로 쓴다.
example (a : Int) (h : ¬ a < 0) : 0 ≤ a ∧ 0 ≤ a := by
  constructor <;> exact h

example (a : Int) : (¬ a < 0 → 0 ≤ a) ∧ (¬ a < 0 → 0 ≤ a) := by
  constructor <;> (intro h; guard_hyp h : 0 ≤ a; exact h)

example (s : Elem (fun n : Nat => 2 ≤ n)) :
    s.val - 2 + 2 = s.val := by
  rcases s with ⟨y, hy⟩
  guard_hyp hy :ₛ 2 ≤ y
  omega

example (a : Int) (h : ¬ a < 0) : 0 ≤ a := by
  have ha : 0 ≤ a := by
    exact h
  exact ha

example (a : Int) (h : ¬ a < 0) : 0 ≤ a := by {
  guard_hyp h : 0 ≤ a
  exact h
}

-- 이름 붙인 술어의 정의도 명시적으로 펼칠 때까지 남긴다.
example (n : Nat) (h : n ∈ positives) : 0 < n := by
  guard_hyp h :ₛ n ∈ positives
  expand at h
  guard_hyp h :ₛ positive n
  expand at h
  guard_hyp h :ₛ 0 < n
  exact h

-- 특정 증명에서는 정리를 끌 수 있다.
set_option ample.autoNormalize false in
example (a : Int) (h : ¬ a < 0) : 0 ≤ a := by
  guard_hyp h : ¬ a < 0
  omega

end AutoNormalizeTests

-- 범위를 벗어나면 원래의 증명 환경으로 돌아간다.
example (a : Int) (h : ¬ a < 0) : 0 ≤ a := by
  guard_hyp h : ¬ a < 0
  omega
