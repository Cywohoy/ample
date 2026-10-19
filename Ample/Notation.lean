import Lean

open Lean PrettyPrinter Delaborator SubExpr

namespace Course.Notation

/-- Prefer the existing non-membership notation when printing a negated membership.
This changes syntax for display only; it never unfolds a set or changes an expression. -/
@[delab app.Not]
def delabNotMembership : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Not 1
  withAppArg do
    guard <| (← getExpr).isAppOfArity ``Membership.mem 5
    let x ← withNaryArg 4 delab
    let s ← withNaryArg 3 delab
    `($x ∉ $s)

end Course.Notation
