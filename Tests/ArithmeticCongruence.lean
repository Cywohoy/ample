import Ample.Math.Numbers

open Ample
set_option maxHeartbeats 80000

namespace CongruenceTests

theorem constant : Congruent 7 23 2 := by arith

theorem negative_modulus : Congruent (-7) 23 2 := by arith

theorem unit_modulus (a b : Int) : Congruent 1 a b := by arith

theorem zero_modulus (a b : Int) (h : Congruent 0 a b) : a=b := by arith

theorem symmetry (n a b : Int) (h : Congruent n a b) : Congruent n b a := by arith

theorem transitivity (n a b c : Int) (h : Congruent n a b) (h2 : Congruent n b c) : Congruent n a c := by arith

theorem add (n a b c d : Int) (h : Congruent n a b) (h2 : Congruent n c d) : Congruent n (a+c) (b+d) := by arith

theorem mul (n a b c d : Int) (h : Congruent n a b) (h2 : Congruent n c d) : Congruent n (a*c) (b*d) := by arith

theorem sub (n a b c d : Int) (h : Congruent n a b) (h2 : Congruent n c d) : Congruent n (a-c) (b-d) := by arith

theorem polynomial (n a b : Int) (h : Congruent n a b) : Congruent n (3*a*a+2*a+1) (3*b*b+2*b+1) := by arith

theorem pow_variable (n a b : Int) (k : Nat) (h : Congruent n a b) : Congruent n (a^k) (b^k) := by arith

theorem pow_product (n a b c d : Int) (k l : Nat) (h : Congruent n a b) (h2 : Congruent n c d) : Congruent n ((a^k)*(c^l)) ((b^k)*(d^l)) := by arith

theorem cancel_add (n a b c : Int) (h : Congruent n (a+c) (b+c)) : Congruent n a b := by arith

theorem weaken_product (n d a b : Int) (h : Congruent (n*d) a b) : Congruent n a b := by arith

theorem weaken_dvd (m n a b : Int) (hd : n ∣ m) (h : Congruent m a b) : Congruent n a b := by arith

theorem to_dvd (n a b : Int) (h : Congruent n a b) : n ∣ a-b := by arith

theorem from_dvd (n a b : Int) (h : n ∣ a-b) : Congruent n a b := by arith

theorem to_mod (n a b : Int) (h : Congruent n a b) : a%n=b%n := by arith

theorem from_mod (n a b : Int) (h : a%n=b%n) : Congruent n a b := by arith

theorem no_cancel_counterexample : ¬ Congruent 6 1 4 ∧ Congruent 6 (1*2) (4*2) := by constructor <;> arith

theorem division_counterexample : Congruent 2 0 2 ∧ ¬ Congruent 2 (0/2) (2/2) := by constructor <;> arith

theorem coprime_constant (a b : Int) (h : Congruent 5 (2*a) (2*b)) : Congruent 5 a b := by arith

theorem existing_division (n : Nat) : 3/n ≤ 3 := by arith

theorem existing_product (m n : Nat) (h : m*n=3) (hn : n≠0) : m≤3 := by arith

theorem negative_variable_modulus (n a b : Int) (h : Congruent (-n) a b) : Congruent n a b := by arith

theorem range_equality (n a b : Int) (h : Congruent n a b) (ha0 : 0≤a) (han : a<n) (hb0 : 0≤b) (hbn : b<n) : a=b := by arith

theorem nested_power (n a b c d : Int) (k : Nat) (h : Congruent n a b) (h2 : Congruent n c d) : Congruent n ((a*c+1)^k) ((b*d+1)^k) := by arith

theorem to_dvd_then_bound (n a b : Int) (h : Congruent n a b) (hd : a-b<n) (hpos : 0≤a-b) : a=b := by arith

theorem zero_counterexample : ¬ Congruent 0 1 2 := by arith

theorem exact_multiple (n a k : Int) : Congruent n (a+n*k) a := by arith

theorem different_modulus_rejected (a b : Int) (h : Congruent 3 a b) (known : Congruent 6 a b) : Congruent 6 a b := by
  fail_if_success (clear known; arith)
  exact known

theorem noncoprime_cancel_rejected (a b : Int) (h : Congruent 6 (2*a) (2*b)) (known : Congruent 6 a b) : Congruent 6 a b := by
  fail_if_success (clear known; arith)
  exact known

end CongruenceTests

#print axioms CongruenceTests.constant
#print axioms CongruenceTests.negative_modulus
#print axioms CongruenceTests.unit_modulus
#print axioms CongruenceTests.zero_modulus
#print axioms CongruenceTests.symmetry
#print axioms CongruenceTests.transitivity
#print axioms CongruenceTests.add
#print axioms CongruenceTests.mul
#print axioms CongruenceTests.sub
#print axioms CongruenceTests.polynomial
#print axioms CongruenceTests.pow_variable
#print axioms CongruenceTests.pow_product
#print axioms CongruenceTests.cancel_add
#print axioms CongruenceTests.weaken_product
#print axioms CongruenceTests.weaken_dvd
#print axioms CongruenceTests.to_dvd
#print axioms CongruenceTests.from_dvd
#print axioms CongruenceTests.to_mod
#print axioms CongruenceTests.from_mod
#print axioms CongruenceTests.no_cancel_counterexample
#print axioms CongruenceTests.division_counterexample
#print axioms CongruenceTests.coprime_constant
#print axioms CongruenceTests.existing_division
#print axioms CongruenceTests.existing_product
#print axioms CongruenceTests.negative_variable_modulus
#print axioms CongruenceTests.range_equality
#print axioms CongruenceTests.nested_power
#print axioms CongruenceTests.to_dvd_then_bound
#print axioms CongruenceTests.zero_counterexample
#print axioms CongruenceTests.exact_multiple
#print axioms CongruenceTests.different_modulus_rejected
#print axioms CongruenceTests.noncoprime_cancel_rejected
