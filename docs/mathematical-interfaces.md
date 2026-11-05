# Mathematical interfaces

Keep chosen data explicit and infer laws about that data. In particular,
`QuotientType R`, `classOf R`, and `quotientLift R` require `IsEquivalence R`;
they do not select a relation for the caller. The representation remains an
`Elem` of the set of equivalence classes.

`Ample.Logic.Relation` owns the common relation-law and preservation records.
Both mathematics and relational rewriting use `Ample.IsEquivalence`; the former
`Rewriting.Laws` record has been removed. `Ample.Math.Relations` registers the
equivalence-law record as a typeclass. Preservation records `Rewriting.Action`
and `Rewriting.Action2` retain explicit source/target relations and functions.

## Quotients

The API follows the roles of Lean's quotient interface without changing the
backend or treating a relation as definitional equality:

| Role | Ample API |
| --- | --- |
| Construction | `QuotientType R`, `classOf R a` |
| Class equality from the relation | `classOf_sound R` |
| Relation from class equality | `classOf_exact R`, `classOf_eq_iff R a b` |
| Representative-based proof | `quotientInductionOn R q`, `quotientInductionOn₂ R S q r` |
| Function comparison | `quotient_funext R` |
| Lift an invariant function | `quotientLift R f hf`, `quotientLift₂ R S f hf` |
| Map between quotients | `quotientMap R S f hf` |
| Computation | The corresponding `_classOf` theorems |

`quotientMap` accepts an `Action R S f`. Its identity and composition theorems
allow callers to reason without opening the class-set representation.
`quotientLift₂` requires both arguments' relations to preserve the result.
It is implemented with two unary lifts. After its computation theorem is proved,
the definition is marked irreducible so elaboration compares applications at the
API boundary instead of unfolding the nested construction and losing proof
arguments during inference. Use its computation theorem to calculate values.

## Restricted functions and chosen correspondences

`Elem.map f hf` restricts both domain and codomain. `Elem.inclusion hST` embeds
a subset into its containing set. Their value, identity, composition and
injectivity theorems avoid repeated reconstruction of membership fields.

`Bijective f` remains a proposition about a fixed function. `Equiv A B` stores
chosen forward and inverse functions together with the two inverse laws.
It supports identity, reversal, composition, products, sums, and function-space
transport. `Equiv.ofBijective` uses `inverseMap` when only bijectivity is given.
The reusable function interfaces support independent universe levels.

The introductory text first constructs restricted functions and inverse maps
directly. Cardinal addition is completed with two unary lifts and a finite
calculation. Binary lifting is introduced when that construction recurs for
multiplication. The text verifies that it gives the same addition before using
it for multiplication and exponentiation. Library availability does not
determine the order of introduction in the textbook.

## Boundaries

The current source synchronization remains authoritative: update the completed
`savedLean` blocks in the sibling Textbook checkout and export with its sync
script. Ordinary library builds and consumer builds do not require that checkout.
This change does not migrate source ownership, replace the quotient backend,
add a second finite-enumeration abstraction, or infer chosen group operations.
The existing permutation representation can be migrated separately when its
full-book source is edited; adding `Equiv` does not silently change that API.

`Tests.MathematicalInterfaces` covers law requirements, mixed-universe uses,
representative proofs, relational rewriting with the shared laws, and both
`exact` and `rw` uses of the new computation interfaces.
