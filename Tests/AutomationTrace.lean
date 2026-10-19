import Ample.Math.Groups.Order
import Ample.Math.InfiniteCardinality

open Ample

-- No trace is emitted for this ordinary declaration.
theorem trace_disabled (n : Nat) : n ≤ n + 1 := by
  arith

set_option trace.Ample.arith true in
theorem trace_arithmetic (m n : Nat) (hn : 0 < n) :
    m / n ≤ m := by
  arith

set_option trace.Ample.card true in
theorem trace_cardinality (A B : Type)
    (h : cardinal A = cardinal B) (hA : IsInfinite A) :
    IsInfinite B := by
  card

set_option trace.Ample.group true in
theorem trace_group (A : Type) (G : Group A) (a : A) :
    G.op (G.inv a) a = G.id := by
  group_calc G

set_option trace.Ample.arith true in
theorem failed_search_restores_state (n : Nat) : n = n := by
  fail_if_success
    have impossible : n < n := by arith
  guard_target =ₛ n = n
  rfl
