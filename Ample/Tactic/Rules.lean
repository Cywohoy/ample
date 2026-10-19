import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.Meta.Tactic.Grind.Attr
import Lean.LabelAttribute

/-!
`course_norm` contains shared expression normalization rules.
`course_classical_norm` adds rules available in classical contexts.
`course_norm_hyp` contains hypothesis-only comparisons for constructed elements and pairs.
Each mathematical module registers the rules for its own definitions.
-/

register_simp_attr course_norm
register_simp_attr course_classical_norm
register_simp_attr course_norm_hyp

-- Iff theorems connecting whole equalities with their mathematical comparisons.
register_label_attr course_compare

-- Separate arithmetic rule application, expression simplification, and reasoning from hypotheses.
register_label_attr course_arith_apply
register_label_attr course_card_rules
register_label_attr course_group_rules
register_simp_attr course_arith_simp

initialize courseArithmeticGrindExtension : Lean.Meta.Grind.Extension ←
  Lean.Meta.Grind.registerAttr `course_arith_grind

syntax (name := Lean.Parser.Attr.course_arith_grind) "course_arith_grind"
  (Lean.Parser.Attr.grindMod)? : attr
