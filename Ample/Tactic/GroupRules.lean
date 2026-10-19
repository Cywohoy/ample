import Ample.Math.Groups.Powers
import Lean.LabelAttribute

/-!
Group calculation rules, enabled after the basic group laws. Kept separate from arithmetic rules.
-/

namespace Ample

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

attribute [ample_group_rules] calc_assoc calc_id_left calc_id_right
  calc_inv_left calc_inv_right

end Ample

attribute [ample_group_rules]
  Ample.inv_id Ample.inv_inv Ample.inv_op
  Ample.solve_op_left Ample.inv_op_cancel_left
  Ample.power_zero Ample.power_one Ample.power_succ
  Ample.power_add Ample.power_mul Ample.power_comm
  Ample.inv_power Ample.power_op_of_comm
  Ample.integerPower_zero Ample.integerPower_nat
  Ample.integerPower_negSucc Ample.integerPower_add
  Ample.integerPower_neg Ample.integerPower_sub
  Ample.integerPower_mul
