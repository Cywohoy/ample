/-!
Shared certificates for equivalence relations and relation-preserving maps.
This module uses only Lean's logical foundation; mathematical constructions and
tactic implementations can consume the same certificates independently.
-/
namespace Ample

/-- The reflexive, symmetric and transitive laws of the specified relation. -/
structure IsEquivalence {A : Type u} (R : A → A → Prop) : Prop where
  refl : ∀ a, R a a
  symm : ∀ {a b}, R a b → R b a
  trans : ∀ {a b c}, R a b → R b c → R a c

namespace Rewriting

/-- The laws needed for reversible rewriting in a relation's own arguments. -/
structure SymmetricTransitive {A : Type u} (R : A → A → Prop) : Prop where
  symm : ∀ {a b}, R a b → R b a
  trans : ∀ {a b c}, R a b → R b c → R a c

/-- A function preserves the given source and target relations. -/
structure Action {A : Type u} {B : Type v}
    (R : A → A → Prop) (S : B → B → Prop) (f : A → B) : Prop where
  map : ∀ {a b}, R a b → S (f a) (f b)

/-- A two-argument function preserves a relation in both arguments. -/
structure Action2 {A : Type u} {B : Type v} {C : Type w}
    (R : A → A → Prop) (S : B → B → Prop)
    (T : C → C → Prop) (f : A → B → C) : Prop where
  map : ∀ {a b c d}, R a b → S c d → T (f a c) (f b d)

end Rewriting
end Ample
