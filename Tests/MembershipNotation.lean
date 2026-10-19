import Ample.Math.Sets

open Ample

variable {A : Type} (S : Set A) (x : A) (P : Prop)

/-- info: x ∉ S : Prop -/
#guard_msgs in
#check (¬ (x ∈ S))

/-- info: x ∈ Sᶜ : Prop -/
#guard_msgs in
#check (x ∈ Sᶜ)

/-- info: x ∉ Sᶜ : Prop -/
#guard_msgs in
#check (¬ (x ∈ Sᶜ))

/-- info: ¬P : Prop -/
#guard_msgs in
#check (¬ P)

/-- info: ¬S x : Prop -/
#guard_msgs in
#check (¬ S x)

/-- info: x ∉ S ∧ P : Prop -/
#guard_msgs in
#check (¬ (x ∈ S) ∧ P)

/-- info: ¬x ∉ S : Prop -/
#guard_msgs in
#check (¬ ¬ (x ∈ S))

/-- info: 0 ∉ [1, 2] : Prop -/
#guard_msgs in
#check (¬ ((0 : Nat) ∈ [1, 2]))

-- Displaying non-membership must not change its expression or unfold a complement.
example (h : ¬ (x ∈ S)) : ¬ (x ∈ S) := by
  guard_hyp h :ₛ Not (Membership.mem S x)
  guard_target =ₛ Not (Membership.mem S x)
  exact h

example (h : x ∈ Sᶜ) : x ∈ Sᶜ := by
  guard_hyp h :ₛ x ∈ Sᶜ
  guard_target =ₛ x ∈ Sᶜ
  exact h

section
open scoped Ample.Auto Classical

example (h : ¬ (x ∈ S)) : ¬ (x ∈ S) := by
  guard_hyp h :ₛ Not (Membership.mem S x)
  guard_target =ₛ Not (Membership.mem S x)
  exact h

example (h : x ∈ Sᶜ) : x ∈ Sᶜ := by
  guard_hyp h :ₛ x ∈ Sᶜ
  guard_target =ₛ x ∈ Sᶜ
  expand at h
  guard_hyp h :ₛ Not (Membership.mem S x)
  exact h

end

example (n : Nat) (h : 0 < n) : n ∈ positives := by
  dsimp [positives]
  guard_target =ₛ positive n
  dsimp [positive]
  guard_target =ₛ 0 < n
  exact h

example (n : Nat) (h : n ∈ positives) : 0 < n := by
  dsimp [positives] at h
  guard_hyp h :ₛ positive n
  dsimp [positive] at h
  guard_hyp h :ₛ 0 < n
  exact h
