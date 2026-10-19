import Ample.Math.Preliminaries

open Ample

example {A B : Type} {m n : Nat}
    (fA : Fin m → A) (fB : Fin n → B)
    (fAinv : A → Fin m) (fBinv : B → Fin n)
    (yA : A) (yB : B)
    (hA : fA (fAinv yA) = yA) (hB : fB (fBinv yB) = yB) :
    (match (fAinv yA, fBinv yB) with
      | (a, b) => (fA a, fB b)) = (yA, yB) := by
  expand
  guard_target = (fA (fAinv yA), fB (fBinv yB)) = (yA, yB)
  run_tac
    let target ← Lean.Elab.Tactic.getMainTarget
    let some (_, lhs, _) := target.consumeMData.eq?
      | throwError "Expected an equality."
    unless lhs.consumeMData.getAppFn.consumeMData.isConstOf ``Prod.mk do
      throwError "Expected the match to reduce to a pair."
  ext : 1
  · exact hA
  · exact hB

example {A B : Type} {m n : Nat}
    (fA : Fin m → A) (fB : Fin n → B)
    (fAinv : A → Fin m) (fBinv : B → Fin n)
    (yA : A) (yB : B)
    (hA : fA (fAinv yA) = yA) (hB : fB (fBinv yB) = yB) : True := by
  let g (p : Fin m × Fin n) : A × B :=
    let (a, b) := p
    (fA a, fB b)
  have h : g (fAinv yA, fBinv yB) = (yA, yB) := by
    expand
    guard_target =ₐ (fA (fAinv yA), fB (fBinv yB)) = (yA, yB)
    ext : 1
    · exact hA
    · exact hB
  trivial

private def successorName (n : Nat) := n + 1
private def matchedName (n : Nat) :=
  match some n with
  | none => 0
  | some k => successorName k

-- 패턴 매칭은 계산하지만 그 결과에 나타난 이름 붙인 정의는 남긴다.
example (n : Nat) : matchedName n = n + 1 := by
  expand
  guard_target = successorName n = n + 1
  rfl

example (n : Nat) :
    (match (successorName n, n) with | (a, _) => a) = n + 1 := by
  expand
  guard_target = successorName n = n + 1
  rfl

example (n : Nat) :
    (match some n with | none => 0 | some k => k) = n := by
  expand

example (n : Nat) :
    (match Nat.succ n with | 0 => 0 | Nat.succ k => k) = n := by
  expand

example (a b c : Nat) :
    (match (a, (b, c)) with | (x, (y, z)) => (z, (y, x))) =
      (c, (b, a)) := by
  expand

example {A B : Type} (f : A → A) (g : B → B) (a : A) (b : B)
    (h : (match (a, b) with | (x, y) => (f x, g y)) = (a, b)) :
    f a = a ∧ g b = b := by
  expand at h
  injection h with ha hb
  constructor
  · exact ha
  · exact hb
