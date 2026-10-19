import Ample.Tactic

open Lean Elab Command

-- Lean's hover handler reads the parser declaration's docstring, rather
-- than the implementation function's. Check aliases and new forms too.
run_elab do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    unless name.getPrefix == `Ample && info.type.isConstOf ``ParserDescr do
      continue
    checked := checked + 1
    let some doc ← findDocString? env name
      | throwError "Tactic syntax '{name}' has no hover documentation. Add a docstring to the syntax declaration or inherit one."
    if doc.trimAscii.toString.isEmpty then
      throwError "Tactic syntax '{name}' has empty hover documentation."
    if doc.toList.any (fun (c : Char) => decide (0xAC00 <= c.toNat ∧ c.toNat <= 0xD7A3)) then
      throwError "Tactic syntax '{name}' must have English hover documentation."
  unless checked >= 40 do
    throwError "Only {checked} tactic parser declarations were checked; check the parser filter."
