import Ample

open Ample
open scoped Ample

namespace NamedPropertiesTests

-- A single unpack preserves an inner conjunction as one field.
example (P Q R : Prop) (h : P ∧ (Q ∧ R)) : Q ∧ R := by
  unpack h with ⟨hP, hQR⟩
  guard_hyp hQR : Q ∧ R
  exact hQR

-- Pattern alternatives produce different local facts in each branch.
example (P Q R : Prop)
    (h : (P ∧ (P → R)) ∨ (Q ∧ (Q → R))) : R := by
  rcases h with ⟨hP, hPR⟩ | ⟨hQ, hQR⟩
  · guard_hyp hP : P
    guard_hyp hPR : P → R
    fail_if_success exact hQ
    apply hPR
    exact hP
  · guard_hyp hQ : Q
    guard_hyp hQR : Q → R
    fail_if_success exact hP
    apply hQR
    exact hQ

example {A B : Type} (f : A → B)
    (h : Injective f ∧ Surjective f) : Bijective f := by
  unpack h with ⟨hinj, hsurj⟩
  constructor with injectivity surjectivity
  case injectivity => exact hinj
  case surjectivity => exact hsurj

example {A B : Type} (f : A → B)
    (hf : Bijective f) : Injective f ∧ Surjective f := by
  unpack hf with ⟨hinj, hsurj⟩
  constructor
  · exact hinj
  · exact hsurj

-- The three named laws are immediate fields, not nested conjunctions.
example {A : Type} (R : Relation A)
    (hR : IsEquivalence R) : IsEquivalence R := by
  unpack hR with ⟨hrefl, hsymm, htrans⟩
  guard_hyp hrefl : ∀ a, R a a
  guard_hyp hsymm : ∀ {a b}, R a b → R b a
  guard_hyp htrans : ∀ {a b c}, R a b → R b c → R a c
  constructor with reflexivity symmetry transitivity
  case reflexivity => exact hrefl
  case symmetry => exact hsymm
  case transitivity => exact htrans

example {A : Type} (blocks : Set (Set A))
    (h : IsPartition blocks) : IsPartition blocks := by
  unpack h with ⟨hn, hc, he⟩
  guard_hyp hn : ∀ S, S ∈ blocks → ∃ x, x ∈ S
  guard_hyp hc : ∀ x, ∃ S, S ∈ blocks ∧ x ∈ S
  constructor with nonemptiness coverage intersection
  case nonemptiness => exact hn
  case coverage => exact hc
  case intersection => exact he

end NamedPropertiesTests
