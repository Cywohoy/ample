import Ample.Tactic.Classical

-- This import supplies the tactic without a Batteries module.
example (P : Prop) (h : ¬¬ P) : P := by
  by_contra hn
  exact h hn

example (P : Prop) (h : ¬¬ P) : P := by
  by_contra
  exact h this

example (P : Prop) (h : ¬¬ P) : P := by
  by_contra hn : ¬ P
  exact h hn

example (P : Prop) (h : ¬ P) : ¬ P := by
  by_contra hp
  guard_hyp hp : P
  guard_target = False
  exact h hp

example : ¬ False := by
  by_contra ⟨⟩

example (P Q : Prop) (hp : ¬ P) (hq : ¬ Q) : ¬ (P ∨ Q) := by
  by_contra hP | hQ
  · exact hp hP
  · exact hq hQ

example (P Q : Prop) (h : ¬ (P ∧ Q)) : ¬ (P ∧ Q) := by
  by_contra ⟨hp, hq⟩
  exact h ⟨hp, hq⟩

example (P : Prop) (h : False) : P := by
  by_contra _
  exact h

example : 1 + 1 = (2 : Nat) := by
  by_contra h
  exact h rfl

-- A negative goal only introduces its premise; no classical choice is needed.
theorem constructiveNegation (P : Prop) (h : ¬ P) : ¬ P := by
  by_contra hp
  exact h hp

#print axioms constructiveNegation
