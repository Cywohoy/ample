import Ample.Math.Relations

open Ample

namespace RelationRewriteTests

theorem left (n a b c : Int)
    (hab : Congruent n a b) (hbc : Congruent n b c) :
    Congruent n a c := by
  rw [hab]
  exact hbc

theorem right (n a b c : Int)
    (hab : Congruent n a b) (hca : Congruent n c a) :
    Congruent n c b := by
  rw [← hab]
  exact hca

theorem square (n a b : Int)
    (hab : Congruent n a b) : Congruent n (a ^ 2) (b ^ 2) := by
  rw [hab]
  exact congruent_refl n _

theorem polynomial (n a b : Int)
    (hab : Congruent n a b) :
    Congruent n (3 * a * a + 2 * a + 1) (3 * b * b + 2 * b + 1) := by
  rw [hab]
  exact congruent_refl n _

theorem hypothesis (n a b c : Int)
    (hab : Congruent n a b) (hac : Congruent n (a + 1) c) :
    Congruent n (b + 1) c := by
  rw [hab] at hac
  exact hac

theorem per {A : Type} (R : A → A → Prop)
    (hs : ∀ a b, R a b → R b a)
    (ht : ∀ a b c, R a b → R b c → R a c)
    (a b c : A) (hab : R a b) (hac : R a c) : R b c := by
  rw [← hab]
  exact hac

theorem equivalence {A : Type} (R : Relation A)
    (hR : IsEquivalence R) (a b c : A)
    (hab : R a b) (hac : R a c) : R b c := by
  rw [← hab]
  exact hac

theorem connectives (n a b c : Int) (P : Prop)
    (hab : Congruent n a b)
    (h : ¬ Congruent n b c ∨ P) : ¬ Congruent n a c ∨ P := by
  rw [hab]
  exact h

theorem quantifier (n a b : Int)
    (hab : Congruent n a b)
    (h : ∀ x, Congruent n b x) : ∀ x, Congruent n a x := by
  rw [hab]
  exact h

theorem existential (n a b : Int)
    (hab : Congruent n a b)
    (h : ∃ x, Congruent n b x) : ∃ x, Congruent n a x := by
  rw [hab]
  exact h

theorem implication (n a b c : Int) (P : Prop)
    (hab : Congruent n a b)
    (h : Congruent n b c → P) : Congruent n a c → P := by
  rw [hab]
  exact h

theorem occurrence (n a b : Int) (hab : Congruent n a b) :
    Congruent n a a := by
  rw (occs := .pos [1]) [hab]
  guard_target =ₛ Congruent n b a
  apply congruent_symm n a b
  exact hab

example (h : Congruent 2 0 2) : (0 : Int) = 0 := by
  fail_if_success rw (occs := .pos [1]) [h]
  rfl

example (h : Congruent 2 0 2) : ¬ Congruent 2 (0 / 2) (2 / 2) := by
  fail_if_success rw [h]
  arith

example (a b : Int) (h : Congruent 3 a b) (known : Congruent 6 a b) : Congruent 6 a b := by
  fail_if_success (clear known; rw [h])
  exact known

example (f : Int → Int) (n a b : Int) (h : Congruent n a b)
    (known : Congruent n (f a) (f b)) : Congruent n (f a) (f b) := by
  fail_if_success (clear known; rw [h])
  exact known

def equalityContext (n : Int) (f : Int → Int) (c : Int)
    (hf : ∀ a b, Congruent n a b → f a = f b) :
    RewriteContext (Congruent n) (fun a => f a = c) (fun a => f a = c) where
  transport := by
    intro _ a b hab
    rw [hf a b hab]

theorem explicitContext (n a b : Int) (f : Int → Int)
    (hab : Congruent n a b)
    (hf : ∀ a b, Congruent n a b → f a = f b) : f a = f b := by
  rw [hab] using equalityContext n f (f b) hf

def conditionalContext (n : Int) (f : Int → Int) (c : Int) (P : Prop)
    (hf : ∀ a b, Congruent n a b → f a = f b) :
    RewriteContext (Congruent n) (fun a => f a = c) (fun a => f a = c) where
  Condition := P
  transport := by
    intro _ a b hab
    rw [hf a b hab]

theorem explicitCondition (n a b : Int) (f : Int → Int) (P : Prop)
    (hab : Congruent n a b)
    (hf : ∀ a b, Congruent n a b → f a = f b)
    (hP : True → P) : f a = f b := by
  rw [hab] using conditionalContext n f (f b) P hf
  guard_target =ₛ P
  exact hP True.intro

@[irreducible] def shifted (a : Int) : Int := 3 * a + 1

@[ample_rewrite] theorem shiftedAction (n : Int) (_positive : 0 < n) :
    Rewriting.Action (Congruent n) (Congruent n) shifted where
  map := by
    intro a b hab
    unfold shifted
    arith

theorem automaticCondition (n a b : Int)
    (hab : Congruent n a b) (bound : 2 ≤ n) :
    Congruent n (shifted a) (shifted b) := by
  rw [hab]
  · guard_target =ₛ 0 < n
    arith
  · exact congruent_refl n _

theorem noExtraCondition (n a b : Int)
    (hab : Congruent n a b) (positive : 0 < n) :
    Congruent n (shifted a) (shifted b) := by
  rw [hab]
  exact congruent_refl n _

theorem localAction {A B : Type} (R : A → A → Prop) (f : A → B)
    (hf : Rewriting.Action R (@Eq B) f) (a b : A) (hab : R a b) : f a = f b := by
  rw [hab]

theorem mixedRules (n a b c : Int) (hab : Congruent n a b) (hbc : b = c) :
    Congruent n (a + 1) (c + 1) := by
  rw [hab, hbc]
  exact congruent_refl n _

theorem selfHypothesis (n a b : Int) (hab : Congruent n a b) : Congruent n b b := by
  rw [hab] at hab
  exact hab

theorem wildcard (n a b c : Int)
    (hab : Congruent n a b) (hac : Congruent n a c) : Congruent n b c := by
  rw [hab] at *
  exact hac

theorem selectedLocations (n a b c : Int)
    (hab : Congruent n a b) (hac : Congruent n a c) : Congruent n b c := by
  rw [hab] at hab hac
  exact hac

@[irreducible] def flaggedLeft (_P : Prop) (a : Int) : Int := a
@[irreducible] def flaggedRight (_Q : Prop) (a : Int) : Int := a

@[ample_rewrite] theorem flaggedLeftAction (P : Prop) (n : Int) (_h : P) :
    Rewriting.Action (Congruent n) (Congruent n) (flaggedLeft P) where
  map := by intro a b hab; unfold flaggedLeft; exact hab

@[ample_rewrite] theorem flaggedRightAction (Q : Prop) (n : Int) (_h : Q) :
    Rewriting.Action (Congruent n) (Congruent n) (flaggedRight Q) where
  map := by intro a b hab; unfold flaggedRight; exact hab

theorem conditionOrder (P Q : Prop) (n a b c d : Int)
    (hab : Congruent n a b) (hcd : Congruent n c d)
    (hp : True → P) (hq : True → Q) :
    Congruent n (flaggedLeft P a + flaggedRight Q c)
      (flaggedLeft P b + flaggedRight Q d) := by
  rw [hab, hcd]
  · guard_target =ₛ Q
    exact hq True.intro
  · guard_target =ₛ P
    exact hp True.intro
  · exact congruent_refl n _

theorem reverseContext (n a b : Int) (f : Int → Int)
    (hab : Congruent n a b)
    (hf : ∀ a b, Congruent n a b → f a = f b) : f b = f a := by
  rw [← hab] using equalityContext n f (f a) hf

-- Rewriting a proof also transports later declarations depending on that proof.
theorem dependentHypothesis (n a b c : Int)
    (hab : Congruent n a b) (hac : Congruent n a c)
    (P : Congruent n a c → Prop) (hp : P hac) : ∃ h, P h := by
  rw [hab] at hac
  exact ⟨(by assumption), hp⟩

#print axioms polynomial
#print axioms quantifier
#print axioms explicitCondition
#print axioms selectedLocations
#print axioms dependentHypothesis

end RelationRewriteTests
