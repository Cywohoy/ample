import Ample.Math.Preliminaries

open Ample

-- 새로 펼칠 정의가 없어도 직접 만든 원소의 성분은 계산한다.
example (n k : Nat) (hk : k < n) :
    (((⟨k, hk⟩, ⟨k, hk⟩) : Fin n × Fin n).fst : Nat) = k := by
  expand

example (m n : Nat) (ym : Fin m) (yn : Fin n)
    (hm : (ym.val + yn.val * m) % m < m)
    (hn : (ym.val + yn.val * m) / m < n) :
    (((⟨(ym.val + yn.val * m) % m, hm⟩,
      ⟨(ym.val + yn.val * m) / m, hn⟩) : Fin m × Fin n).fst : Nat) =
      ((ym, yn).fst : Nat) := by
  expand
  guard_target =ₛ (ym.val + yn.val * m) % m = ym.val
  have hy := ym.isLt
  arith

example (m n : Nat) (ym : Fin m) (yn : Fin n)
    (hm : (ym.val + yn.val * m) % m < m)
    (hn : (ym.val + yn.val * m) / m < n) :
    (((⟨(ym.val + yn.val * m) % m, hm⟩,
      ⟨(ym.val + yn.val * m) / m, hn⟩) : Fin m × Fin n).snd : Nat) =
      ((ym, yn).snd : Nat) := by
  expand
  guard_target =ₛ (ym.val + yn.val * m) / m = yn.val
  have hy := ym.isLt
  arith

example (a b c d : Nat) (h : (a, b).fst = (c, d).fst) : a = c := by
  expand at h
  guard_hyp h :ₛ a = c
  exact h

example (a b c : Nat) : ((a, b), c).fst.snd = b := by
  expand
