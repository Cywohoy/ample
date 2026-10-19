import Ample.Math.Preliminaries

open Course

example : ¬ (∃ n m : Int, Course.Divides 2 n ∧ Course.Divides 2 m ∧ n * m = 3) := by
  rintro ⟨n, m, ⟨k, hn⟩, ⟨l, hm⟩, h⟩
  suffices hnot : ¬ (2 ∣ n * m) by arith
  arith

example : ¬ (∃ n m : Int, Course.Divides 2 n ∧ Course.Divides 2 m ∧ n * m = 3) := by
  rintro ⟨n, m, ⟨k, hn⟩, ⟨l, hm⟩, h⟩
  rw [hn, hm] at h
  arith
