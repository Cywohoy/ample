# Third-party notices

Ample uses the Lean distribution. It does not require separate Batteries, mathlib, or Verso packages.

The pattern handling in `Ample/Tactic/Ext.lean` is adapted from Lean's `Lean.Elab.Tactic.Ext` implementation.
The original copyright notice is preserved in that file.

The forward `apply` interface in `Ample/Tactic/Rule.lean` and the implementation in `Ample/Tactic/Wlog.lean`
are adapted from their mathlib counterparts for Lean 4.35.0.
The original copyright notices and source links are preserved at the top of the respective files.
A copy of the Apache License 2.0 is included in `licenses/Apache-2.0.txt`.
These source attributions do not introduce a build dependency on mathlib.
