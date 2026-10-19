import Ample
import Lean.Util.CollectAxioms

open Lean Elab Command

-- The public entry point must remain independent of the textbook,
-- document generator, external mathematics packages, and CTT archive.
run_cmd do
  let env ← getEnv
  unless env.contains `Ample.Set && env.contains `Ample.Group && env.contains `Ample.Cardinal do
    throwError "The public mathematical declarations must belong to Ample."
  if env.isNamespace `Course then
    throwError "A standalone Ample import must not introduce the textbook's legacy namespace."
  for moduleName in env.header.moduleNames do
    unless #[`Init, `Std, `Lean, `Ample].any (·.isPrefixOf moduleName) do
      throwError "Unexpected Ample dependency: {moduleName}."
    if (`Ample.Cubical).isPrefixOf moduleName || (`Ample.Metatheory).isPrefixOf moduleName then
      throwError "The library imports the archived CTT implementation: {moduleName}."
  for (name, declaration) in env.constants.toList do
    if (`Course).isPrefixOf name then
      throwError "Legacy textbook declaration leaked into Ample: {name}."
    let some index := env.getModuleIdxFor? name | continue
    unless (`Ample.Math).isPrefixOf env.header.moduleNames[index.toNat]! do continue
    if let .axiomInfo _ := declaration then
      throwError "The mathematical library introduces an axiom: {name}."
    match declaration with
    | .thmInfo _ | .defnInfo _ =>
        for axiomName in ← collectAxioms name do
          unless #[`propext, `Quot.sound, `Classical.choice].contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}."
    | _ => pure ()
