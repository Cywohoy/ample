import Ample.Math.Preliminaries
import Ample.Tactic.Unfold
import Ample.Tactic.Auto

open Ample

private def bounded (x : Nat) : Prop := x < 3 ∧ True
private def boundedAlias (x : Nat) : Prop := bounded x
private def shifted (x : Nat) : Nat := x + 2
private def recursiveDouble : Nat → Nat
  | 0 => 0
  | n + 1 => recursiveDouble n + 2

-- 기호 연결 선언만 건너뛰고 여집합의 정의는 한 층씩 펼친다.
example {A : Type} (S : Set A) (x : A) (h : x ∈ Sᶜᶜ) : ¬¬ (x ∈ S) := by
  expand at h
  guard_hyp h :ₛ ¬ (x ∈ Sᶜ)
  expand at h
  guard_hyp h :ₛ ¬¬ (x ∈ S)
  exact h

example {A : Type} (f : A → Set A) (x : A) : True := by
  let D : Set A := fun a => a ∉ f a
  have h : x ∈ D → x ∉ f x := by
    expand
    guard_target =ₛ ¬ (x ∈ f x) → ¬ (x ∈ f x)
    intro hx
    exact hx
  trivial

-- 원소 조건을 정의에서 계산하며 논리곱을 나누는 단계는 명시적으로 쓴다.
example (A B : Type) (S : Set A) (T : Set B) (a : A) (b : B)
    (h : (a, b) ∈ setProduct S T) : a ∈ S := by
  expand at h
  guard_hyp h :ₛ a ∈ S ∧ b ∈ T
  rcases h with ⟨ha, hb⟩
  exact ha

example (A B : Type) (S : Set A) (T : Set B) (a : A) (b : B)
    (ha : a ∈ S) (hb : b ∈ T) : (a, b) ∈ setProduct S T := by
  expand at *
  guard_target =ₛ a ∈ S ∧ b ∈ T
  constructor
  · exact ha
  · exact hb

example {A B : Type} (f : A → B) (S : Set A) (y : B)
    (h : y ∈ image f S) : ∃ x, S x ∧ f x = y := by
  expand at h
  guard_hyp h :ₛ ∃ x, x ∈ S ∧ f x = y
  exact h

example {A B : Type} (f : A → B) (T : Set B) (x : A)
    (h : x ∈ preimage f T) : T (f x) := by
  expand at h
  guard_hyp h :ₛ f x ∈ T
  exact h

-- 처음에는 바깥의 이름만 펼치고 새로 나타난 정의는 다음 단계까지 유지한다.
example (x : Nat) (h : boundedAlias x) : x < 3 := by
  expand at h
  guard_hyp h :ₛ bounded x
  expand at h
  guard_hyp h :ₛ x < 3 ∧ True
  exact h.left

example (x : Nat) (h : shifted x = 5) : x = 3 := by
  expand at h
  omega

example : shifted 3 = 5 := by
  expand

example : recursiveDouble 3 = 6 := by
  expand
  guard_target = recursiveDouble 2 + 2 = 6
  rfl

example (n : Nat) : recursiveDouble n = recursiveDouble n := by
  expand

-- 함수 적용과 성분 접근만 계산하며 외연성이나 부등식의 정리는 사용하지 않는다.
example (x : Nat) (h : ¬ x < 3) : ¬ x < 3 := by
  expand at *
  guard_hyp h :ₛ ¬ x < 3
  exact h

example (P : Prop) (x : Nat) (h : P) : P ∧ x = x := by
  expand
  guard_target =ₛ P ∧ x = x
  constructor
  · exact h
  · rfl

example (x : Nat) : (fun p : Nat × Nat => p.1 + p.2) (x, 2) = x + 2 := by
  expand

example (f g : Nat → Nat) (h : f = g) : f = g := by
  expand at *
  guard_target =ₛ f = g
  exact h

-- 집합의 곱의 정의에서 새로 나타난 역상의 정의는 같은 단계에서 펼치지 않는다.
example {A B C : Type} (f : A → B) (S : Set B) (T : Set C)
    (a : A) (c : C) (h : (a, c) ∈ setProduct (preimage f S) T) : f a ∈ S := by
  expand at h
  guard_hyp h :ₛ a ∈ preimage f S ∧ c ∈ T
  expand at h
  guard_hyp h :ₛ f a ∈ S ∧ c ∈ T
  exact h.left

-- 정의를 함수의 인수로 넣은 경우에도 바깥 함수만 한 번 펼친다.
example (x : Nat) : shifted (shifted x) = x + 4 := by
  expand
  guard_target =ₛ shifted x + 2 = x + 4
  expand

example (x : Nat) (h : boundedAlias x) : x < 3 := by
  let p (n : Nat) := boundedAlias n
  have hp : p x := h
  expand at hp
  guard_hyp hp :ₛ boundedAlias x
  expand at hp
  guard_hyp hp :ₛ bounded x
  expand at hp
  guard_hyp hp :ₛ x < 3 ∧ True
  exact hp.left

namespace WithAuto

open scoped Ample.Auto

example (x : Nat) (h : boundedAlias x) : x < 3 := by
  expand at h
  guard_hyp h :ₛ bounded x
  exact h.left

end WithAuto
