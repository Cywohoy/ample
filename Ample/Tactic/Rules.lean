import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.Meta.Tactic.Grind.Attr
import Lean.LabelAttribute

/-!
`ample_norm` contains shared expression normalization rules.
`ample_classical_norm` adds rules available in classical contexts.
`ample_norm_hyp` contains hypothesis-only comparisons for constructed elements and pairs.
Each mathematical module registers the rules for its own definitions.
-/

register_simp_attr ample_norm
register_simp_attr ample_classical_norm
register_simp_attr ample_norm_hyp

-- Iff theorems connecting whole equalities with their mathematical comparisons.
register_label_attr ample_compare
-- Certified relation laws and unary/binary actions for reversible rewriting.
register_label_attr ample_rewrite

-- Separate arithmetic rule application, expression simplification, and reasoning from hypotheses.
register_label_attr ample_arith_apply
-- One-premise implications used once on the original arithmetic hypotheses.
register_label_attr ample_arith_prepare
register_label_attr ample_card_rules
register_label_attr ample_group_rules
register_simp_attr ample_arith_simp

initialize ampleArithmeticGrindExtension : Lean.Meta.Grind.Extension ←
  Lean.Meta.Grind.registerAttr `ample_arith_grind

syntax (name := Lean.Parser.Attr.ample_arith_grind) "ample_arith_grind"
  (Lean.Parser.Attr.grindMod)? : attr
