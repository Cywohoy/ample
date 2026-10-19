import Ample.Math.Groups.Automation

open Course Lean Elab Command

run_cmd do
  for name in [`Course.Cardinal, `Course.Relation, `Course.IsCountablyInfinite] do
    if (← getEnv).contains name then
      throwError "The early group route unexpectedly imports {name}."

theorem early_group_example (A : Type) (G : Group A) (a : A) :
    G.op (G.inv a) a = G.id := by
  group_calc G

def early_finite_domain : Fin 3 :=
  { val := 2, isLt := by decide }
