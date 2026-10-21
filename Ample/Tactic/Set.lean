/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Benway

Adapted from Mathlib.Tactic.Set: local abbreviations without a Mathlib dependency.
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Rewrite

open Lean Meta Elab Tactic

namespace Ample

/-- Metadata on the value distinguishes an explicit abbreviation from an ordinary local let. -/
def setAliasKey : Name := `Ample.setAlias

/-- Whether a local definition was introduced as a persistent presentation abbreviation. -/
def isSetAlias (decl : LocalDecl) : Bool :=
  match decl.value? with
  | some (.mdata data _) => data.getBool setAliasKey
  | _ => false

/-- `set q := expression` defines a local abbreviation and replaces the expression in
all hypotheses and the current goal. It does not simplify or solve the remaining goal.
An optional type annotation is accepted. `with h` records `h : q = expression`;
`with ← h` records the reverse equality. Ample's automatic normalization preserves
this abbreviation; use `unfold q` or `dsimp [q]` to expand it explicitly. -/
scoped syntax (name := setAlias) "set " ident (" : " term)? " := " term
  (" with " ("← ")? ident)? : tactic

@[tactic setAlias] def evalSetAlias : Tactic := fun stx => do
  let saved ← saveState
  try
    let `(tactic| set $name:ident $[: $ty:term]? := $value:term $[with $[←%$rev]? $eqName:ident]?) := stx
      | throwUnsupportedSyntax
    withMainContext do
      let type? ← ty.mapM (fun t => Term.elabType t)
      let value ← Term.elabTermEnsuringType value type?
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      let type ← inferType value
      let tagged := mkMData (MData.empty.setBool setAliasKey true) value
      let (alias, goal) ← (← (← getMainGoal).define name.getId type tagged).intro1P
      replaceMainGoal [goal]
      withMainContext do
        Term.addTermInfo' (isBinder := true) name (mkFVar alias)
        let valueSyntax ← Term.exprToSyntax value
        -- Native `rewrite` performs the certified substitution without rw's trailing rfl.
        evalTactic (← `(tactic| try rewrite [show $valueSyntax = $name from rfl] at *))
        if let some eqName := eqName then
          let typeSyntax ← Term.exprToSyntax type
          if rev.isSome then
            evalTactic (← `(tactic| have $eqName : ($valueSyntax : $typeSyntax) = $name := rfl))
          else
            evalTactic (← `(tactic| have $eqName : $name = ($valueSyntax : $typeSyntax) := rfl))
  catch ex =>
    saved.restore
    throw ex

end Ample

