import Ample.Math.Cardinality
import Ample.Math.Preliminaries
import Ample.Tactic.Indiscern

open Course

theorem pointwise_without_ext {A B : Type} (f g : A → B) (h : f = g) (x : A) :
    f x = g x := by
  indiscern x at h with hx
  guard_hyp h :ₛ f = g
  guard_hyp hx :ₛ f x = g x
  exact hx

example {A B : Type} (f g : A → B) (h : f = g) : ∀ x, f x = g x := by
  indiscern at h with hp
  exact hp

example (f g : Nat → Nat → Nat) (h : f = g) : f 2 3 = g 2 3 := by
  indiscern 2 3 at h with hp
  exact hp

example (f g : (n : Nat) → Fin (n + 1)) (h : f = g) (n : Nat) : f n = g n := by
  indiscern n at h with hp
  exact hp

example {A : Type} (S T : Set A) (h : S = T) (x : A) : x ∈ S ↔ x ∈ T := by
  indiscern x at h with hx
  guard_hyp hx :ₛ x ∈ S ↔ x ∈ T
  exact hx

example {A : Type} (S T : Set A) (h : S = T) : ∀ x, x ∈ S ↔ x ∈ T := by
  indiscern at h with hx
  exact hx

example (P Q : Prop) (h : P = Q) : P ↔ Q := by
  indiscern at h with hp
  exact hp

theorem pair_without_ext {A B : Type} (p q : A × B) (h : p = q) :
    p.1 = q.1 ∧ p.2 = q.2 := by
  indiscern at h with ha hb
  guard_hyp h :ₛ p = q
  constructor
  · exact ha
  · exact hb

example (n : Nat) (i j : Fin n) (h : i = j) : i.val = j.val := by
  indiscern at h with hv
  exact hv

example {A : Type} (S : Set A) (s t : Elem S) (h : s = t) : s.val = t.val := by
  indiscern at h with hv
  exact hv

@[ext] structure OtherRecord where
  count : Nat
  flag : Bool

theorem record_without_ext (p q : OtherRecord) (h : p = q) : p.count = q.count := by
  indiscern at h with hc hf
  guard_hyp hc :ₛ p.count = q.count
  guard_hyp hf :ₛ p.flag = q.flag
  exact hc

example (a b : Int) (h : parityClass a = parityClass b) : Congruent 2 a b := by
  indiscern at h with hr
  exact hr

example (A B : Type) (h : cardinal A = cardinal B) : SameCardinality A B := by
  indiscern at h with hr
  guard_hyp hr :ₛ SameCardinality A B
  exact hr

-- Arbitrary class elements expose their stored sets without choosing representatives.
example (p q : Parity) (h : p = q) : True := by
  indiscern at h with hSets
  guard_hyp h :ₛ p = q
  guard_hyp hSets :ₛ p.val = q.val
  trivial

example (f : Nat → Nat) (a b : Nat) (h : f a = f b) : True := by
  fail_if_success indiscern at h
  guard_hyp h :ₛ f a = f b
  trivial

example (f g : Nat → Nat) (h : f = g) : True := by
  fail_if_success indiscern 1 2 at h
  fail_if_success indiscern 1 at h with h1 h2
  guard_hyp h :ₛ f = g
  trivial

#print axioms pointwise_without_ext
#print axioms pair_without_ext
#print axioms record_without_ext

example {A B : Type} (f g : A → B) (h : f = g) (x : A) : f x = g x := by
  indiscern
  guard_target =ₛ f = g
  exact h

example {A B : Type} (f g : A → B) (h : f = g) : ∀ x, f x = g x := by
  indiscern
  guard_target =ₛ f = g
  exact h

example {A : Type} (S T : Set A) (h : S = T) (x : A) : x ∈ S ↔ x ∈ T := by
  indiscern
  guard_target =ₛ S = T
  exact h

example {A B : Type} (p q : A × B) (h : p = q) : p.1 = q.1 ∧ p.2 = q.2 := by
  indiscern
  guard_target =ₛ p = q
  exact h

example (a b : Int) (h : parityClass a = parityClass b) : Congruent 2 a b := by
  indiscern (parityClass a = parityClass b)
  exact h

example (f g : Nat → Nat) (h : f = g) : ∀ x, f x = g x := by
  indiscern at h
  guard_hyp h :ₛ ∀ x, f x = g x
  ext at h
  guard_hyp h :ₛ f = g
  intro x
  indiscern x at h
  guard_hyp h :ₛ f x = g x
  exact h

example {A B : Type} (p q : A × B) (h : p = q) : p = q := by
  indiscern at h
  guard_hyp h :ₛ p.1 = q.1 ∧ p.2 = q.2
  ext at h
  guard_hyp h :ₛ p = q
  exact h

example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext at h with hfg
  guard_hyp h :ₛ ∀ x, f x = g x
  exact hfg

example (a b : Int) (h : Congruent 2 a b) : parityClass a = parityClass b := by
  ext at h : parityClass a = parityClass b
  exact h

example (f g : Nat → Nat) (x : Nat) (h : f x = g x) : True := by
  fail_if_success ext at h : f = g
  guard_hyp h :ₛ f x = g x
  trivial

example (n : Nat) (P : Nat → Prop)
    (x y : Fin n × (Nat × Subtype P)) (h : x = y) : True := by
  indiscern! at h
  guard_hyp h :ₛ x = y
  have hFin : x.1 = y.1 := by assumption
  have hFinValue : x.1.val = y.1.val := by assumption
  have hPair : x.2 = y.2 := by assumption
  have hSubtypeValue : x.2.2.val = y.2.2.val := by assumption
  run_tac
    let before := (← Lean.getLCtx).getFVarIds.size
    Lean.Elab.Tactic.evalTactic (← `(tactic| indiscern! at *))
    let after := (← Lean.getLCtx).getFVarIds.size
    unless before == after do throwError "Repeated indiscern! added duplicate facts."
  trivial

example (P Q : Nat → Prop) (h : P = Q) : ∀ x, P x ↔ Q x := by
  indiscern at h
  guard_hyp h :ₛ ∀ x, P x ↔ Q x
  ext! at h
  guard_hyp h :ₛ P = Q
  indiscern
  exact h

example (a b c d : Nat) (h : (a, b) = (c, d)) : a = c ∧ b = d := by
  indiscern at h
  guard_hyp h :ₛ a = c ∧ b = d
  exact h

example {A : Type} (S T : Set A) (h : S = T) : S = T := by
  indiscern at h
  guard_hyp h :ₛ ∀ x, x ∈ S ↔ x ∈ T
  ext at h
  guard_hyp h :ₛ S = T
  exact h

example (n : Nat) (i j : Fin n) (h : i = j) : i = j := by
  indiscern at h
  guard_hyp h :ₛ i.val = j.val
  ext at h
  guard_hyp h :ₛ i = j
  exact h

example {A : Type} (S : Set A) (s t : Elem S) (h : s = t) : s = t := by
  indiscern at h
  guard_hyp h :ₛ s.val = t.val
  ext at h
  guard_hyp h :ₛ s = t
  exact h

example (p q : OtherRecord) (h : p = q) : p = q := by
  indiscern at h
  guard_hyp h :ₛ p.count = q.count ∧ p.flag = q.flag
  ext at h
  guard_hyp h :ₛ p = q
  exact h

example (A B : Type) (h : cardinal A = cardinal B) : cardinal A = cardinal B := by
  indiscern at h
  guard_hyp h :ₛ SameCardinality A B
  ext at h : cardinal A = cardinal B
  guard_hyp h :ₛ cardinal A = cardinal B
  exact h
