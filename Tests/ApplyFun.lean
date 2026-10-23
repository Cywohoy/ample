import Ample.Tactic
import Ample.Math.Functions

open Ample

namespace ApplyFunTests

theorem arithmetic_observation (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  apply_fun (fun x => x + 1) at h
  guard_hyp h :ₛ a + 1 = b + 1
  exact h

theorem named_observation (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  apply_fun (fun x => x + 1) at h with shifted
  guard_hyp h :ₛ a = b
  guard_hyp shifted :ₛ a + 1 = b + 1
  exact shifted

theorem pair_projections {A B : Type} (a c : A) (b d : B)
    (h : (a, b) = (c, d)) : (b, a) = (d, c) := by
  apply_fun (fun p => p.1) at h with first
  apply_fun (fun p => p.2) at h with second
  guard_hyp first :ₛ a = c
  guard_hyp second :ₛ b = d
  rw [first, second]

theorem subtype_values {A : Type} {P : A → Prop} (s t : Subtype P)
    (h : s = t) : s.val = t.val := by
  apply_fun (fun x => x.val) at h
  guard_hyp h :ₛ s.val = t.val
  exact h

theorem fin_values {n : Nat} (i j : Fin n) (h : i = j) : i.val = j.val := by
  apply_fun (fun x => x.val) at h
  guard_hyp h :ₛ i.val = j.val
  exact h

theorem nested_values {n : Nat} (p q : Fin n × Fin n) (h : p = q) :
    p.1.val = q.1.val ∧ p.2.val = q.2.val := by
  apply_fun (fun x => x.1.val) at h with first
  apply_fun (fun x => x.2.val) at h with second
  constructor
  · exact first
  · exact second

theorem function_observation {A B : Type} (f g : A → B) (a : A) (h : f = g) :
    f a = g a := by
  apply_fun (fun k => k a) at h
  exact h

theorem composed_observation {n : Nat}
    (f g : { _f : Fin n → Fin n // True }) (i : Fin n) (h : f = g) :
    (f.val i).val = (g.val i).val := by
  apply_fun (fun k => (k.val i).val) at h
  exact h

theorem predicate_equality_stays_equality {A : Type} (P Q : A → Prop)
    (a : A) (h : P = Q) : P a ↔ Q a := by
  apply_fun (fun R => R a) at h
  guard_hyp h :ₛ P a = Q a
  apply Iff.of_eq
  exact h

def tagged (n : Nat) : { _k : Nat // True } := ⟨n, True.intro⟩

theorem known_projection (a b : Nat) (h : tagged a = tagged b) : a = b := by
  apply_fun (fun x => x.val) at h
  guard_hyp h :ₛ a = b
  exact h

def untouched (n : Nat) : Nat := n + 1

theorem mathematical_name_is_preserved (a b : Nat) (h : a = b) :
    untouched a = untouched b := by
  apply_fun untouched at h
  guard_hyp h :ₛ untouched a = untouched b
  exact h

theorem explicit_injectivity {A B : Type} (f : A → B) (hf : Injective f)
    (a b : A) (h : f a = f b) : a = b := by
  apply_fun f using hf
  guard_target =ₛ f a = f b
  exact h

theorem local_injectivity {A B : Type} (f : A → B) (hf : Injective f)
    (a b : A) (h : f a = f b) : a = b := by
  apply_fun f
  guard_target =ₛ f a = f b
  exact h

theorem injectivity_is_an_obligation {A B : Type} (f : A → B)
    (a b : A) (_h : f a = f b) (hab : a = b) : a = b := by
  run_tac do
    let saved ← Lean.Elab.Tactic.saveState
    let fn := Lean.mkIdent `f
    let a := Lean.mkIdent `a
    let b := Lean.mkIdent `b
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply_fun $fn))
      let goals ← Lean.Elab.Tactic.getGoals
      unless goals.length == 2 do throwError "Expected image equality and injectivity goals"
      Lean.Elab.Tactic.evalTactic (← `(tactic| guard_target =ₛ $fn $a = $fn $b))
      Lean.Elab.Tactic.setGoals goals.tail!
      Lean.Elab.Tactic.evalTactic (← `(tactic| guard_target =ₛ ∀ x y, $fn x = $fn y → x = y))
    finally
      saved.restore
  exact hab

theorem constant_map_does_not_prove_equality (a b : Nat) (h : a = b) : a = b := by
  fail_if_success solve | apply_fun (fun _ : Nat => 0)
  guard_target =ₛ a = b
  exact h

theorem errors_restore_state (a b : Nat) (h : a = b) : a = b := by
  fail_if_success apply_fun _ at h
  fail_if_success apply_fun (fun x => x.val) at h
  fail_if_success apply_fun (fun x => x + 1) at missing
  fail_if_success apply_fun (fun x => x + 1) at h using h
  guard_hyp h :ₛ a = b
  guard_target =ₛ a = b
  exact h

theorem failed_injectivity_restores (a b : Nat) (h : a = b) : a = b := by
  fail_if_success apply_fun (fun x => x + 1) using h
  guard_hyp h :ₛ a = b
  guard_target =ₛ a = b
  exact h

theorem other_goals_remain (a b : Nat) : (a = a) ∧ (b = b) := by
  constructor
  apply_fun (fun x : Nat => x) using (fun _ _ h => h)
  guard_target =ₛ b = b
  rfl

theorem data_is_not_chosen : ∃ n : Nat, n = n := by
  refine ⟨?value, ?proof⟩
  case proof =>
    apply_fun (fun x : Nat => x) using (fun _ _ h => h)
  guard_target =ₛ Nat
  exact 7

open scoped Ample.Auto in
theorem auto_step (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  apply_fun (fun x => x + 1) at h
  exact h

end ApplyFunTests
