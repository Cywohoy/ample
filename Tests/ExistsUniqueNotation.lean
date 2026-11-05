import Ample.Math.Functions

open Ample
open scoped Ample

/- Display is independent of whether the predicate was written as a lambda. -/
section
variable (A : Type) (P : A → Prop) (x : A) (R : A → A → Prop)

/-- info: ∃! x : A, P x : Prop -/
#guard_msgs in
#check ExistsUnique P

/-- info: ∃! x_1 : A, R x x_1 : Prop -/
#guard_msgs in
#check ExistsUnique (R x)

/-- info: ∃! x : A, ∃! y : A, R x y : Prop -/
#guard_msgs in
#check ∃! x : A, ∃! y : A, R x y

-- The printed binding must not capture the fixed first argument.
example : (∃! x_1 : A, R x x_1) = ExistsUnique (R x) := rfl

/-- info: ExistsUnique P : Prop -/
#guard_msgs in
set_option pp.notation false in
#check ExistsUnique P

/-- info: @ExistsUnique A P : Prop -/
#guard_msgs in
set_option pp.explicit true in
#check ExistsUnique P
end

/-- info: ∃! n : Nat, n = 4 : Prop -/
#guard_msgs in
#check ∃! n : Nat, n = 4

-- Unapplied constants keep their ordinary function type.
/-- info: Ample.ExistsUnique.{u_1} {A : Type u_1} (P : A → Prop) : Prop -/
#guard_msgs in
#check ExistsUnique

-- Showing notation must not fold an explicitly expanded expression back up.
/--
trace: A : Type
P : A → Prop
h : ∃! x : A, P x
⊢ ∃! x : A, P x
---
trace: A : Type
P : A → Prop
h : ∃ x, P x ∧ ∀ (y : A), P y → y = x
⊢ ∃! x : A, P x
---
trace: A : Type
P : A → Prop
h : ∃ x, P x ∧ ∀ (y : A), P y → y = x
⊢ ∃ x, P x ∧ ∀ (y : A), P y → y = x
-/
#guard_msgs in
example (A : Type) (P : A → Prop) (h : ExistsUnique P) : ExistsUnique P := by
  trace_state
  expand at h
  guard_hyp h : ∃ x, P x ∧ ∀ y, P y → y = x
  trace_state
  expand
  trace_state
  exact h

-- Explicit unfolding and the ordinary proof rules still use the same definition.
example (A : Type) (P : A → Prop) (h : ExistsUnique P) : ExistsUnique P := by
  unfold ExistsUnique at h ⊢
  exact h

example (A : Type) (P : A → Prop) :
    (∃! x : A, P x) → ∃ x, P x := by
  intro h
  unpack h with ⟨x, hx⟩
  exists x
  exact hx.left

-- Auto normalization must leave the quantifier intact until an explicit expansion.
open scoped Ample.Auto in
example (A : Type) (P : A → Prop) (h : ExistsUnique P) : ExistsUnique P := by
  guard_target = ExistsUnique P
  guard_hyp h : ExistsUnique P
  exact h
