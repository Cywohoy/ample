import Ample.Math.Sets
import Ample.Tactic.Auto
open Ample
open scoped Ample.Auto Classical

theorem normalized_counter (P : Prop) (counter : ¬ P → False) : P := by
  by_contra at counter with h
  exact h

theorem normalized_cases (P R : Prop) (positive : P → R) (negative : ¬ P → R) : R := by
  by_cases at positive negative with h
  exact h
