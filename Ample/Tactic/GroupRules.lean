import Ample.Math.Groups.Powers
import Lean.LabelAttribute

/-!
Group calculation rules, enabled after the basic group laws. Kept separate from arithmetic rules.
-/

namespace Course

private theorem calc_assoc {A : Type} (G : Group A) (a b c : A) :
    G.op (G.op a b) c = G.op a (G.op b c) := G.assoc a b c
private theorem calc_id_left {A : Type} (G : Group A) (a : A) :
    G.op G.id a = a := G.id_left a
private theorem calc_id_right {A : Type} (G : Group A) (a : A) :
    G.op a G.id = a := G.id_right a
private theorem calc_inv_left {A : Type} (G : Group A) (a : A) :
    G.op (G.inv a) a = G.id := G.inv_left a
private theorem calc_inv_right {A : Type} (G : Group A) (a : A) :
    G.op a (G.inv a) = G.id := G.inv_right a

attribute [course_group_rules] calc_assoc calc_id_left calc_id_right
  calc_inv_left calc_inv_right

end Course

attribute [course_group_rules]
  Course.inv_id Course.inv_inv Course.inv_op
  Course.solve_op_left Course.inv_op_cancel_left
  Course.power_zero Course.power_one Course.power_succ
  Course.power_add Course.power_mul Course.power_comm
  Course.inv_power Course.power_op_of_comm
  Course.integerPower_zero Course.integerPower_nat
  Course.integerPower_negSucc Course.integerPower_add
  Course.integerPower_neg Course.integerPower_sub
  Course.integerPower_mul
