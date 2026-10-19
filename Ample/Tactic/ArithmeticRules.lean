import Ample.Tactic.Rules
import Init.Data.Nat.Div.Lemmas
import Init.Data.Int.DivMod.Lemmas

/-!
Register Lean's natural-number and integer arithmetic lemmas for arithmetic automation.
This module introduces no new axioms or mathematical definitions.
-/

attribute [course_arith_apply]
  Nat.mod_lt Nat.div_lt_of_lt_mul
  Nat.mod_eq_of_lt Nat.div_eq_of_lt
  Nat.div_le_self Int.ediv_le_self
  Nat.div_le_div_right Nat.div_le_div_left
  Int.ediv_le_ediv Int.le_ediv_of_mul_le
  Int.ediv_nonneg Int.ediv_nonpos_of_nonneg_of_nonpos
  Int.emod_lt_of_neg Int.emod_lt
  Nat.div_eq_of_eq_mul_left Nat.div_eq_of_eq_mul_right
  Int.ediv_eq_of_eq_mul_left Int.ediv_eq_of_eq_mul_right
  Nat.mul_le_mul_left Nat.mul_le_mul_right
  Nat.le_mul_of_pos_left Nat.le_mul_of_pos_right
  Nat.mul_lt_mul_of_pos_left Nat.mul_lt_mul_of_pos_right
  Nat.le_of_mul_le_mul_left Nat.le_of_mul_le_mul_right
  Int.le_of_mul_le_mul_left Int.le_of_mul_le_mul_right
  Nat.succ_le_of_lt Nat.zero_lt_of_lt
  Int.emod_nonneg Int.emod_lt_of_pos
  Int.emod_eq_of_lt Int.ediv_eq_zero_of_lt
  Int.ediv_lt_of_lt_mul
  Int.mul_le_mul_of_nonneg_left Int.mul_le_mul_of_nonneg_right
  Int.mul_le_mul_of_nonpos_left Int.mul_le_mul_of_nonpos_right
  Int.mul_lt_mul_of_pos_left Int.mul_lt_mul_of_pos_right
  Nat.mod_eq_zero_of_dvd Nat.dvd_of_mod_eq_zero
  Int.emod_eq_zero_of_dvd Int.dvd_of_emod_eq_zero

namespace Course.Automation

-- Support division bounds for either ordering of a product.
private theorem nat_lt_mul_of_div_lt_left {a b c : Nat}
    (h : a / b < c) (hb : 0 < b) : a < b * c := by
  rw [Nat.mul_comm]
  exact Nat.lt_mul_of_div_lt h hb

private theorem int_lt_mul_of_ediv_lt_left {a b c : Int}
    (h : a / b < c) (hb : 0 < b) : a < b * c := by
  rw [Int.mul_comm]
  exact Int.lt_mul_of_ediv_lt hb h

private theorem nat_mul_add_div_right (a c : Nat) {b : Nat}
    (hb : 0 < b) : (a * b + c) / b = a + c / b := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.add_comm]

private theorem nat_le_div_of_mul_le {a b c : Nat}
    (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c :=
  (Nat.le_div_iff_mul_le hc).2 h

private theorem nat_div_le_of_lt_mul {a b c : Nat}
    (hc : 0 < c) (h : a < (b + 1) * c) : a / c ≤ b := by
  apply (Nat.div_le_iff_le_mul hc).2
  have heq : (b + 1) * c = b * c + c := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [heq] at h
  omega

private theorem int_ediv_le_of_lt_mul {a b c : Int}
    (hc : 0 < c) (h : a < (b + 1) * c) : a / c ≤ b := by
  have := Int.ediv_lt_of_lt_mul hc h
  omega

private theorem nat_mul_le_of_le_div {a b c : Nat}
    (hc : 0 < c) (h : a ≤ b / c) : a * c ≤ b :=
  (Nat.le_div_iff_mul_le hc).1 h

private theorem nat_lt_mul_of_div_le {a b c : Nat}
    (hc : 0 < c) (h : a / c ≤ b) : a < (b + 1) * c := by
  apply Nat.lt_mul_of_div_lt
  · omega
  · exact hc

private theorem int_lt_mul_of_ediv_le {a b c : Int}
    (hc : 0 < c) (h : a / c ≤ b) : a < (b + 1) * c := by
  exact Int.lt_mul_of_ediv_lt hc (by omega)

private theorem int_mul_le_mul_iff_pos_left {a b c : Int}
    (hc : 0 < c) : c * a ≤ c * b ↔ a ≤ b := by
  rw [Int.mul_comm c a, Int.mul_comm c b]
  exact Int.mul_le_mul_iff_of_pos_right hc

private theorem int_le_mul_of_pos_left {a b : Int}
    (ha : 0 < a) (hb : 0 ≤ b) : b ≤ a * b := by
  have hOne : 1 ≤ a := by omega
  have h := Int.mul_le_mul_of_nonneg_right hOne hb
  simpa only [Int.one_mul] using h

private theorem int_le_mul_of_pos_right {a b : Int}
    (ha : 0 ≤ a) (hb : 0 < b) : a ≤ a * b := by
  rw [Int.mul_comm]
  exact int_le_mul_of_pos_left hb ha

attribute [course_arith_apply]
  Nat.lt_mul_of_div_lt nat_lt_mul_of_div_lt_left
  Int.lt_mul_of_ediv_lt int_lt_mul_of_ediv_lt_left
  nat_le_div_of_mul_le nat_div_le_of_lt_mul int_ediv_le_of_lt_mul
  nat_mul_le_of_le_div nat_lt_mul_of_div_le int_lt_mul_of_ediv_le
  int_le_mul_of_pos_left int_le_mul_of_pos_right

attribute [course_arith_simp] nat_mul_add_div_right
attribute [course_arith_simp] int_mul_le_mul_iff_pos_left

end Course.Automation

grind_pattern [course_arith_grind] Nat.le_mul_of_pos_left => n * m
grind_pattern [course_arith_grind] Nat.le_mul_of_pos_right => n * m
grind_pattern [course_arith_grind] Course.Automation.int_le_mul_of_pos_left => a * b
grind_pattern [course_arith_grind] Course.Automation.int_le_mul_of_pos_right => a * b

attribute [course_arith_simp]
  Nat.add_mul_mod_self_left Nat.add_mul_mod_self_right
  Nat.add_mul_div_left Nat.add_mul_div_right
  Nat.mul_add_mod_self_left Nat.mul_add_mod_self_right Nat.mul_add_div
  Nat.mod_eq_of_lt Nat.div_eq_of_lt Nat.mod_add_div
  Nat.mul_div_cancel Nat.mul_div_cancel_left
  Nat.div_zero Nat.div_one Nat.div_self Nat.zero_div
  Nat.mul_le_mul_left_iff Nat.mul_le_mul_right_iff
  Nat.le_div_iff_mul_le Nat.div_lt_iff_lt_mul
  Nat.div_le_iff_le_mul
  Nat.zero_add Nat.add_zero Nat.zero_mul Nat.mul_zero
  Nat.one_mul Nat.mul_one Nat.sub_zero Nat.sub_self
  Nat.mod_mod Nat.mod_zero Nat.mod_one Nat.mod_self
  Nat.mod_add_mod Nat.add_mod_mod Nat.mod_mul_mod Nat.mul_mod_mod
  Nat.add_mod_left Nat.add_mod_right Nat.mul_mod_left Nat.mul_mod_right
  Int.add_mul_emod_self_left Int.add_mul_emod_self_right
  Int.add_mul_ediv_left Int.add_mul_ediv_right
  Int.mul_add_emod_self_left Int.mul_add_emod_self_right
  Int.mul_add_ediv_left Int.mul_add_ediv_right
  Int.emod_eq_of_lt Int.ediv_eq_zero_of_lt
  Int.mul_ediv_cancel Int.mul_ediv_cancel_left
  Int.ediv_zero Int.ediv_one Int.ediv_self Int.zero_ediv Int.ediv_minus_one
  Int.sub_mul_ediv_left Int.sub_mul_ediv_right
  Int.le_ediv_iff_mul_le Int.ediv_lt_iff_lt_mul
  Int.ediv_le_iff_le_mul Int.mul_le_mul_iff_of_pos_right
  Int.emod_add_mul_ediv Int.emod_add_ediv_mul
  Int.zero_add Int.add_zero Int.zero_mul Int.mul_zero
  Int.one_mul Int.mul_one Int.sub_zero Int.sub_self
  Int.emod_emod Int.emod_zero Int.emod_one Int.emod_self Int.emod_neg
  Int.emod_add_emod Int.add_emod_emod Int.emod_sub_emod Int.sub_emod_emod
  Int.sub_mul_emod_self_left Int.sub_mul_emod_self_right
  Int.mul_sub_emod_self_left Int.mul_sub_emod_self_right
  Int.mul_emod_left Int.mul_emod_right

-- Recover equalities from division, remainder, and natural-number subtraction bounds.
attribute [course_arith_grind .]
  Nat.ext_div_mod Int.ext_ediv_emod Nat.sub_add_cancel

-- Use bounds for division and remainder expressions occurring in the goal.
grind_pattern [course_arith_grind] Nat.div_le_self => n / k
grind_pattern [course_arith_grind] Int.ediv_le_self => a / b
grind_pattern [course_arith_grind] Nat.mod_lt => x % y
grind_pattern [course_arith_grind] Int.emod_nonneg => a % b
grind_pattern [course_arith_grind] Int.emod_lt_of_pos => a % b
grind_pattern [course_arith_grind] Int.emod_lt_of_neg => a % b
grind_pattern [course_arith_grind] Nat.div_mul_le_self => m / n
grind_pattern [course_arith_grind] Int.ediv_mul_le => a / b
grind_pattern [course_arith_grind] Int.lt_ediv_add_one_mul_self => a / b
grind_pattern [course_arith_grind] Nat.div_eq_of_eq_mul_left => m / n, k * n
  where guard m = k * n
grind_pattern [course_arith_grind] Nat.div_eq_of_eq_mul_right => m / n, n * k
  where guard m = n * k
grind_pattern [course_arith_grind] Int.ediv_eq_of_eq_mul_left => a / b, c * b
  where guard a = c * b
grind_pattern [course_arith_grind] Int.ediv_eq_of_eq_mul_right => a / b, b * c
  where guard a = b * c

-- Normalize operations modulo a common modulus and use known remainder equalities.
attribute [course_arith_grind =]
  Nat.add_mod Nat.mul_mod Nat.pow_mod
  Int.add_emod Int.mul_emod Int.sub_emod Int.neg_emod_eq_sub_emod

attribute [course_arith_grind →]
  Nat.mod_eq_zero_of_dvd Nat.dvd_of_mod_eq_zero
  Int.emod_eq_zero_of_dvd Int.dvd_of_emod_eq_zero
  Nat.le_of_mul_le_mul_left Nat.le_of_mul_le_mul_right
  Int.le_of_mul_le_mul_left Int.le_of_mul_le_mul_right
  Int.mul_le_of_le_ediv
  Course.Automation.nat_mul_le_of_le_div
  Course.Automation.nat_lt_mul_of_div_le
  Course.Automation.int_lt_mul_of_ediv_le
