import Ample.Tactic.Unfold
import Tests.Fixtures.Expansion

open Ample

-- Imported application definitions are left alone until explicitly registered.
example (n : Nat) (h : ExternalMath.nested n = n) : ExternalMath.nested n = n := by
  expand
  guard_target = ExternalMath.nested n = n
  exact h

register_expand_module ExternalMath

-- Registration uses the module path, not the declaration's namespace.
example (n : Nat) (h : ExternalMath.nested n = n) : ExternalMath.nested n = n := by
  expand
  guard_target = ExternalMath.nested n = n
  exact h

register_expand_module Tests.Fixtures

example (n : Nat) (h : n + n = n) : ExternalMath.nested n = n := by
  expand
  guard_target = ExternalMath.twice n = n
  expand
  guard_target = n + n = n
  exact h
