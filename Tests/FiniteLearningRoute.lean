import Ample.Math.Groups.Order

open Course Lean Elab Command

run_cmd do
  for name in [`Course.IsCountablyInfinite, `Course.powerSet,
      `Course.Cardinal.le] do
    if (← getEnv).contains name then
      throwError "Finite group order unexpectedly imports {name}."

theorem finite_order_example :
    groupOrder twoElementGroup (by
      apply isFinite_of_cardinal_eq bool_cardinal) = 2 := by
  exact cardinality_eq _ bool_cardinal
