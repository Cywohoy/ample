import Ample.Tactic.Injection

set_option linter.unusedVariables false

-- 범위를 열지 않은 곳에서는 Lean의 기본 전술을 사용한다.
example (a b c d : Nat) (h : (a, b) = (c, d)) : True := by
  injection h with ha hb
  fail_if_success guard_hyp h : (a, b) = (c, d)
  trivial

open Ample

example (a b c d : Nat) (h : (a, b) = (c, d)) : True := by
  injection h with ha hb
  guard_hyp h :ₛ (a, b) = (c, d)
  guard_hyp ha :ₛ a = c
  guard_hyp hb :ₛ b = d
  trivial

example (n : Nat) (i j : Fin n) (h : i = j) : True := by
  injection h with hv
  guard_hyp h :ₛ i = j
  guard_hyp hv : i.val = j.val
  trivial

example (P : Nat → Prop) (s t : Subtype P) (h : s = t) : True := by
  injection h with hv
  guard_hyp h :ₛ s = t
  trivial

example (n : Nat) (i j : Fin n) (h : i = j) : i.val = j.val := by
  injection h

-- 꺼낸 값의 등식은 그대로 rw에도 사용할 수 있다.
example (n : Nat) (i j : Fin n) (h : i = j) :
    i.val + 1 = j.val + 1 := by
  injection h with hv
  rw [hv]

example (P : Nat → Prop) (s t : Subtype P) (h : s = t) :
    s.val + 1 = t.val + 1 := by
  injection h with hv
  rw [hv]

example (x y : Nat × Nat) (h : x = y) : x.1 + 1 = y.1 + 1 := by
  injection h with hFirst hSecond
  rw [hFirst]

example (A B : Type) (x y : A × B) (h : x = y) : True := by
  injection h with ha hb
  guard_hyp ha : x.1 = y.1
  guard_hyp hb : x.2 = y.2
  trivial

-- 원래 등식과 각 단계의 성분 등식을 함께 유지한다.
example (n : Nat) (P : Nat → Prop)
    (x y : Fin n × (Nat × Subtype P)) (h : x = y) : True := by
  injections
  guard_hyp h :ₛ x = y
  have hFin : x.1 = y.1 := by assumption
  have hFinValue : x.1.val = y.1.val := by assumption
  have hPair : x.2 = y.2 := by assumption
  have hSubtype : x.2.2 = y.2.2 := by assumption
  have hSubtypeValue : x.2.2.val = y.2.2.val := by assumption
  run_tac
    let before := (← Lean.getLCtx).getFVarIds.size
    Lean.Elab.Tactic.evalTactic (← `(tactic| injections))
    let after := (← Lean.getLCtx).getFVarIds.size
    unless before == after do throwError "Repeated injections added duplicate facts."
  trivial

example (f : Nat → Nat) (x y : Nat) (h : f x = f y) : True := by
  fail_if_success injection h
  guard_hyp h :ₛ f x = f y
  trivial

-- 임의의 함수값이어도 순서쌍의 성분은 비교할 수 있다.
example (f : Nat → Nat × Nat) (x y : Nat) (h : f x = f y) : True := by
  injection h with hFirst hSecond
  guard_hyp h : f x = f y
  guard_hyp hFirst : (f x).1 = (f y).1
  guard_hyp hSecond : (f x).2 = (f y).2
  trivial

example (a b : Nat) (h : Nat.succ a = Nat.succ b) : True := by
  injection h with hab
  guard_hyp h :ₛ Nat.succ a = Nat.succ b
  guard_hyp hab : a = b
  trivial

example (a : Nat) (h : some a = (none : Option Nat)) : False := by
  injection h

example (a b c d : Nat) (h : (a, b) = (c, d)) : True := by
  fail_if_success injection h with ha hb extra
  guard_hyp h :ₛ (a, b) = (c, d)
  trivial
