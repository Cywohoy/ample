import Ample.Math.Groups.Permutations
import Ample.Tactic.Auto

/-!
군의 예와 거듭제곱: 연습문제
각 sorry를 자신의 증명으로 바꾸어 완성하라.
2.3부터 2.6까지의 정의와 정리로 각 연습문제를 검증한다.
-/

open Ample
open scoped Ample.Auto Classical

-- These exercises precede group automation and the return to cardinality.
open Lean Elab Command in
run_cmd do
  for name in [`Ample.Cardinal, `Ample.Relation, `Ample.evalGroupCalc] do
    if (← getEnv).contains name then
      throwError "The group exercise route unexpectedly imports {name}."

namespace ExerciseChecks.GroupExamples
variable {A B : Type}

-- Calculations 1
theorem exercise_op_reverse_identity (G : Group A) (a b : A)
    (h : G.op a b = G.id) : G.op b a = G.id := by
  have ha : a = G.inv b := by
    exact inverse_unique G b a h
  rw [ha, G.inv_right]

-- Calculations 2
theorem exercise_conjugate_identity (G : Group A) (a x : A)
    (h : G.op (G.op a x) (G.inv a) = G.id) : x = G.id := by
  have hx : G.op a x = a := by
    apply op_right_cancel G (G.inv a)
    rw [h, G.inv_right]
  apply op_left_cancel G a
  rw [G.id_right]
  exact hx

-- Calculations 3
theorem exercise_inverse_injective (G : Group A) (a b : A)
    (h : G.inv a = G.inv b) : a = b := by
  calc
    a = G.inv (G.inv a) := by rw [inv_inv]
    _ = G.inv (G.inv b) := by rw [h]
    _ = b := by rw [inv_inv]

-- Powers 1
theorem exercise_power_identity (G : Group A) (n : Nat) :
    power G G.id n = G.id := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power_succ, ih, G.id_left]

-- Powers 2
theorem exercise_square_identity_abelian (G : Group A)
    (h : ∀ a : A, G.op a a = G.id) : IsAbelian G := by
  have hi : ∀ a : A, a = G.inv a := by
    intro a
    exact inverse_unique G a a (h a)
  intro a b
  calc
    G.op a b = G.inv (G.op a b) := hi (G.op a b)
    _ = G.op (G.inv b) (G.inv a) := inv_op G a b
    _ = G.op b a := by rw [← hi b, ← hi a]

-- Powers 3
theorem exercise_power_commuting_element (G : Group A) (a
  b : A)
    (hab : G.op a b = G.op b a) (n : Nat) :
    G.op (power G a n) b = G.op b (power G a n) := by
  symm
  apply op_power_comm G b a hab.symm

-- TwoElement 1
theorem exercise_bool_power_even (n : Nat) :
    power twoElementGroup true (2 * n) = false := by
  rw [power_mul, bool_power_two]
  exact exercise_power_identity twoElementGroup n

theorem exercise_bool_power_odd (n : Nat) :
    power twoElementGroup true (2 * n + 1) = true := by
  rw [power_succ, exercise_bool_power_even]
  rfl

-- TwoElement 2
theorem exercise_bool_inverse (b : Bool) :
  twoElementGroup.inv b = b := by
  rfl

theorem exercise_bool_cube (b : Bool) : power
  twoElementGroup b 3 = b := by
  cases b with
  | false => rfl
  | true => rfl

-- Products 1
theorem exercise_product_abelian_factors (G : Group A) (H
  : Group B)
    (h : IsAbelian (productGroup G H)) : IsAbelian G ∧
      IsAbelian H := by
  constructor
  · intro a b
    have hp := h (a, H.id) (b, H.id)
    indisc : 1 at hp with ha hb
    exact ha
  · intro a b
    have hp := h (G.id, a) (G.id, b)
    indisc : 1 at hp with ha hb
    exact hb

-- Products 2
theorem exercise_product_power (G : Group A) (H : Group B)
    (a : A) (b : B) (n : Nat) :
    power (productGroup G H) (a, b) n = (power G a n,
      power H b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [power_succ, ih]
      rfl

-- Permutations 1
theorem exercise_transposition_square :
    power (permutationGroup (Fin 3)) transposition01 2 =
      permutationIdentity (Fin 3) := by
  ext : 1
  ext x : 1
  exact swapThree_twice 0 1 x

-- Permutations 2
theorem exercise_threeCycle_cube :
    power (permutationGroup (Fin 3)) threeCycle 3 =
      permutationIdentity (Fin 3) := by
  ext! x
  have hx : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by arith
  rcases hx with h0 | h1 | h2
  · have hx0 : x = 0 := by
      ext : 1
      exact h0
    rw [hx0]
    rfl
  · have hx1 : x = 1 := by
      ext : 1
      exact h1
    rw [hx1]
    rfl
  · have hx2 : x = 2 := by
      ext : 1
      exact h2
    rw [hx2]
    rfl

-- Permutations 3
theorem exercise_threeCycle_inverse :
    (permutationGroup (Fin 3)).inv threeCycle =
      power (permutationGroup (Fin 3)) threeCycle 2 := by
  symm
  apply inverse_unique
  rw [← power_succ]
  exact exercise_threeCycle_cube

end ExerciseChecks.GroupExamples
