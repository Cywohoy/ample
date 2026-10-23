import Ample.Tactic
import Ample.Math.Sets
open scoped Ample

example (P : Nat → Prop) (x : Nat) (h : P x) : P x ∧ P x := by
  set Q : Prop := P x with hQ
  guard_hyp h :ₛ Q
  guard_hyp hQ : Q = P x
  guard_target =ₛ Q ∧ Q
  exact ⟨h, h⟩

example (x : Nat) (h : x + 1 = 3) : x + 1 = 3 := by
  set y := x + 1 with ← hy
  guard_hyp hy : x + 1 = y
  guard_hyp h :ₛ y = 3
  guard_target =ₛ y = 3
  exact h

example (P : Prop) (h : P) : P := by
  set unused : Nat := 3
  exact h

-- A presentation abbreviation must not automatically solve reflexive goals.
example (x : Nat) : x + 1 = x + 1 := by
  set y := x + 1
  guard_target =ₛ y = y
  rfl

example (P : Nat → Prop) (x : Nat) (h : P x) : P x := by
  fail_if_success set bad : Nat := P x
  guard_hyp h :ₛ P x
  exact h

section
open scoped Ample.Auto

example (P : Nat → Prop) (x : Nat) (h : P x) : P x ∧ P x := by
  set Q := P x
  guard_hyp h :ₛ Q
  guard_target =ₛ Q ∧ Q
  have hQ : Q := h
  guard_hyp hQ :ₛ Q
  constructor
  · exact h
  · exact hQ

-- Ordinary local lets still compute, including when an abbreviation is present.
example (x : Nat) (h : x = 3) : x = 3 := by
  set y := x
  let z := y + 0
  have hz : z = 3 := by
    dsimp [z]
    exact h
  exact h

example (P : Nat → Prop) (x : Nat) (h : P x) : P x := by
  set Q := P x
  unfold Q at h ⊢
  guard_hyp h :ₛ P x
  exact h

end

-- An explicit carrier annotation survives lambda elaboration.
example (x : Nat) : True := by
  set S : Ample.Set Nat := fun n => n = x with hS
  guard_hyp S :ₛ Ample.Set Nat := fun n => n = x
  guard_hyp hS : S = (fun n => n = x)
  have hx : x ∈ S := by rfl
  trivial

section
open scoped Ample.Auto

-- Membership must remain available after normalization as well.
example : True := by
  set S : Ample.Set Nat := fun x => x = 0
  guard_hyp S :ₛ Ample.Set Nat := fun x => x = 0
  have h : 0 ∈ S := by rfl
  guard_hyp h :ₛ 0 ∈ S
  trivial

end
