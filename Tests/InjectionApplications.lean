import Ample.Math.Functions
import Ample.Tactic.Auto

open Ample

-- 단사성으로 얻은 원소의 등식을 값 비교에도 사용할 수 있다.
example {A B : Type} {m n : Nat}
    (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Injective (fun x : Fin m × Fin n => (fA x.1, fB x.2)) := by
  intro x y hxy
  injection hxy with hAxy hBxy
  have hx : x.1 = y.1 := hA.injective _ _ hAxy
  have hy : x.2 = y.2 := hB.injective _ _ hBxy
  injections
  ext : 1
  · assumption
  · assumption

namespace WithAuto

open scoped Ample.Auto

example {A B : Type} {m n : Nat}
    (fA : Fin m → A) (fB : Fin n → B)
    (hA : Bijective fA) (hB : Bijective fB) :
    Injective (fun x : Fin m × Fin n => (fA x.1, fB x.2)) := by
  intro x y hxy
  injection hxy with hAxy hBxy
  have hx : x.1 = y.1 := hA.injective _ _ hAxy
  have hy : x.2 = y.2 := hB.injective _ _ hBxy
  injections
  ext : 1
  · assumption
  · assumption

-- 표현을 정리한 뒤에도 원래 타입의 등식을 유지한다.
example (n a b : Nat) (ha : a < n) (hb : b < n)
    (h : ({ val := a, isLt := ha } : Fin n) =
      { val := b, isLt := hb }) : True := by
  guard_hyp h : ({ val := a, isLt := ha } : Fin n) = { val := b, isLt := hb }
  have hVal : a = b := by assumption
  run_tac
    let before := (← Lean.getLCtx).getFVarIds.size
    Ample.Automation.normalizeGoals
    let after := (← Lean.getLCtx).getFVarIds.size
    unless before == after do throwError "Repeated normalization added duplicate facts."
  trivial

end WithAuto

example {A B : Type} (f : A → B) (hf : Bijective f) : Bijective f := by
  constructor
  · exact hf.injective
  · exact hf.surjective
