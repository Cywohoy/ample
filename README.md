# Ample

Ample is a Lean library for defining mathematical objects and writing proofs.
It uses Lean 4.35.0's standard types, propositions, equality, and kernel.
Its only dependencies are `Init`, `Std`, and `Lean`, as shipped with Lean itself.

## Usage

```lean
import Ample

open Ample
open scoped Ample.Auto

theorem double_is_not_five (n : Int) : 2 * n ≠ 5 := by
  arith

theorem group_inverse {A : Type} (G : Group A) (a : A) :
    G.op a (G.inv a) = G.id := by
  group_calc G
```

Public mathematical declarations and tactics use the `Ample` namespace.
Normalization uses `Ample.Auto`, and rule attributes use the `ample_*` prefix.
Opening `Ample` makes the mathematical names and scoped tactics available.
`open scoped Ample.Auto` enables presentation normalization before and after proof steps.
Use `open scoped Classical` in scopes that should use classical logic by default.

`apply_fun (fun x => x.val) at h` applies the specified function to both sides of an equality.
Add `with valueEquality` to retain the original hypothesis and name its image.
On an equality goal, `apply_fun f using hf` requires an injectivity proof `hf`;
without `using`, a matching local proof is reused or injectivity remains a goal.
Function applications and projections are computed without selecting mathematical comparison rules.

`ext` applies one comparison layer by default.
Use `ext!` to repeat comparisons, or specify a depth with `ext : 2`.
The depth notation for congruence is likewise `congr : 2`.
One registered mathematical comparison counts as one layer: for sets, `set_ext` compares membership conditions up to logical equivalence.
Iff theorems registered with `ample_compare` connect equalities and their comparison conditions in both directions.
Matching does not choose representatives or assign unresolved inputs of an existing goal.
`expand` unfolds one layer of definitions; `expand!` repeats unfolding.
Definitions from `Ample.Math` and the current file are eligible automatically.
Use `register_expand_module MyProject.Math` to opt another module and its submodules into expansion.
Compatibility spellings such as `ext1` and `congr 2` remain available.

Transformations apply a restricted reflexivity check to the results of the current step.
This check does not process unrelated pending goals or choose values for existing data metavariables.
Names supplied by `apply … with …` follow Lean's native goal order.
Missing premises appear before the continuation that uses the derived fact.
Typeclass arguments are synthesized by Lean; if synthesis fails, supply an instance with `letI` or provide the structure explicitly.

Use Lean's explicit `suffices` syntax, for example:

```lean
theorem remainder_of_fin (m : Nat) (i : Fin m) : i.val % m = i.val := by
  suffices bound : i.val < m by arith
  exact i.isLt
```

### Arithmetic and relation rewrites

`arith` handles natural-number and integer arithmetic with bounded, registered
rules. `Ample.Math.Numbers` connects integer congruence (`a ≡ b [MOD n]`) to
divisibility and remainders, and registers addition, subtraction, multiplication,
negation, and natural powers. It does not decide arbitrary number-theoretic
existence statements or cancel factors without the necessary assumptions.

Direct registered one-premise bridges are checked against existing hypotheses
before search. Search then tries structural arithmetic rules. On failure it restores the
state, prepares relevant facts from the original hypotheses once, removes
duplicates, and retries. `ample.arith.maxPreparedFacts` defaults to 64; prepared
facts do not recursively produce more prepared facts. The two stages have
local heartbeat budgets and respect the enclosing heartbeat/recursion limits.
A failed `arith` leaves the proof state unchanged.

With a relation proof `h : R a b`, `rw [h]` can rewrite a proposition only if it
constructs an iff between the old and new propositions. It composes registered
`Rewriting.Action`/`Action2` certificates; it never changes the meaning of `Eq`.
Symmetry and transitivity suffice to rewrite a single argument of `R` itself.
Operations inside that argument need their own preservation certificates.

```lean
example (n a b : Int) (h : a ≡ b [MOD n]) :
    a * a ≡ b * b [MOD n] := by
  rw [h]
  exact congruent_refl n _
```

Register laws/actions using `@[ample_rewrite]`, or provide an explicit
`RewriteContext R P P` with `rw [h] using context`. Its optional `Condition`
becomes a proof obligation when it is not already known. Conditions precede the
rewritten continuation. `←`, `at h`, `at *`, selected locations, and native
occurrence configurations remain available. Later rules in a rewrite sequence
can put their new conditions before conditions from earlier rules; each condition
keeps the context in which its certificate was constructed.
A source relation proof is held
fixed across selected locations even when one location is that proof itself.
Dependent hypotheses follow Lean's usual replacement behavior: the original
hypothesis can be retained when its type is needed by later declarations.

The automatic engine composes unary and binary operations, logical connectives,
and quantifiers. It defaults to depth 10 and 128 certificate/comparison steps
(`ample.rewrite.maxDepth`, `ample.rewrite.maxSteps`). An explicit context is the
escape hatch for unsupported operations or deeper contexts. Errors identify
missing preserving actions; `set_option trace.Ample.rewrite true` shows search
details. Failure restores all selected hypotheses, goals, and pending siblings.
Type-valued relations with proof-relevant inverse laws are outside this API.

Library documentation, hover help, diagnostics, and implementation comments are written in English.
The accompanying Korean textbook is maintained separately.

To use the package from another project, add a path dependency to `lakefile.toml`:

```toml
[[require]]
name = "ample"
path = "../Ample"
```

Adjust `path` to point from your project to the Ample directory.
A standalone consumer project is available in `Examples/Consumer/`.

A project can instead pin the published Git release:

```toml
[[require]]
name = "ample"
git = "https://github.com/Cywohoy/ample.git"
rev = "v0.2.0"
```

Use the same `lean-toolchain` as Ample, then run `lake update ample` and `lake build`.
Git dependencies work without a package-registry listing. Reservoir indexing
is a separate process; see its [inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria).

## Modules

| Import | Contents |
| --- | --- |
| `Ample.Tactic` | Forward and backward inference, equality comparison, unfolding, and automation |
| `Ample.Tactic.Auto` | Optional normalization of proof-state presentation |
| `Ample.Tactic.ApplyFun` | Explicit application of a function to an equality |
| `Ample.Tactic.Comparison` | Registered iff theorems for equality comparison |
| `Ample.Tactic.Arithmetic` | Natural-number and integer arithmetic via `arith` |
| `Ample.Tactic.GroupRules` | Registration of group laws for group calculation |
| `Ample.Math.Sets` | Sets and membership conditions |
| `Ample.Math.Functions` | Functions, subtypes, injectivity, surjectivity, and inverses |
| `Ample.Math.Numbers` | Basic natural-number and integer properties |
| `Ample.Math.Relations` | Equivalence relations, quotient sets, and their subtype of elements |
| `Ample.Math.FiniteCardinality` | Cardinals, finite types, and finite cardinalities |
| `Ample.Math.InfiniteCardinality` | Infinite types and Cantor's theorem |
| `Ample.Math.Groups.*` | Group definitions, powers, products, and permutation groups |

Importing `Ample.Tactic` does not import the mathematical library.
`quotientSet R` is the set of equivalence classes, and `QuotientType R` is `Elem (quotientSet R)`.
With `open Ample` or `open scoped Ample`, write this type as `A / R`, where `R : Relation A`.
The notation uses the same precedence and left associativity as ordinary division;
for example, `A / R → B` is a function from the quotient to `B`.
Write a quotient element as `⟦a⟧` when its quotient type can be inferred,
or as `(⟦a⟧ : A / R)` to specify the relation. This denotes `classOf R a`.
Each quotient element stores a class as a set and evidence that it belongs to the quotient set.
`Cardinal` uses the same construction for equicardinality.
`quotientRepr R q` returns a representative, and `quotientRepr_spec R q` proves that it represents `q`.
Inverse values, representatives, finite sizes, and listing extensions are selected
with `Classical.choose`; `Classical.choose_spec` proves the condition for the selected value.
Each construction packages its value and law in a subtype before exposing them separately:

| Construction | Bundled data | Value | Law |
| --- | --- | --- | --- |
| Inverse function | `inverseMapData` | `inverseMap` | `inverseMap_right`, `inverseMap_left` |
| Representative | `quotientReprData` | `quotientRepr` | `quotientRepr_spec` |
| Finite size | `cardinalityData` | `cardinality` | `cardinality_spec` |
| Listing extension | `nextListingData` | `nextListing` | `nextListing_spec` |
| Map on a quotient | `quotientLiftData` | `quotientLift` | `quotientLift_classOf` |

Value definitions project `.val`, and their laws project `.property`.
The inverse data stores the right inverse law; injectivity supplies the left inverse law.
For a class-invariant map `f`, `quotientLiftData R hR f hf` packages the quotient map
with the law `∀ a, F (classOf R a) = f a`.
`quotientLift R hR f hf` projects the map, and `quotientLift_classOf` projects its law.
`quotientLift_unique` proves that any two maps satisfying this law are equal.
Domain-specific automation uses the definitions and rules imported for that domain.
`import Ample` imports both the current mathematical library and the tactics.

## Textbook integration

Ample and the [Korean textbook](https://github.com/Cywohoy/lean-algebra) are separate public Git repositories.
The textbook's `main` branch is a standalone foundations book and pins an Ample release as a Git dependency.
Its `full-book` branch preserves the complete algebra textbook and uses `../Ample` as a path dependency.
For export development, place their checkouts next to one another. The textbook's former tactic modules are thin import adapters.
The textbook presents definitions and complete proofs in teaching order; `Ample/Math/` exports the executable mathematical code without incomplete exercises.
Korean proof annotations stay in the textbook and are omitted from the English library exports.
Do not import a textbook module and its matching mathematical export together: both define the same `Ample` declarations.

After editing the mathematical code in the textbook, run these commands from the textbook root:

```powershell
python scripts/sync_ample.py
python scripts/sync_ample.py --check
```

The exporter belongs to the textbook repository. It accepts `--ample-root PATH`
when the Ample checkout is elsewhere. Its source is the complete `savedLean` code
in that repository, not the chapter layout of the separate `LeanFoundations` book.
The current exporter owns ten foundations modules and two aggregate modules;
it does not delete or overwrite group modules. Export synchronization requires Python;
normal library builds and use do not require Python or the textbook directory.
The generated mathematical files are committed in Ample so that every release
is buildable on its own. Changes to their definitions or proofs should be made
in the textbook and exported before committing both repositories.

The textbook commits `scripts/ample-sync.json` alongside its source to record
the last synchronized exports. Before writing any output, the exporter checks
all owned files against that baseline. If an Ample file was edited independently,
it refuses the entire update. Merge that work into the complete `savedLean`
source first, then rerun the exporter; matching files can be recorded without
being overwritten. There is no force-overwrite option. `--check` is read-only
and verifies both exports and the synchronization record. This record adds no
textbook dependency to Ample's build or CI.

## Validation

```powershell
lake build
lake exe ample-demo
```

The build checks the mathematical modules and tactic regressions.
Boundary tests check for accidental textbook or Cubical dependencies and for new axioms or admitted proofs.
The standard Lean axioms `propext`, `Quot.sound`, and `Classical.choice` are allowed.
Run `lake exe ample-consumer` in `Examples/Consumer` to check external imports.
Source attributions and licenses are listed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

GitHub CI builds the library and its regression tests on Linux and Windows,
then runs the demo and independent consumer. CI needs no textbook checkout.

## License

Ample is distributed under the [Apache License 2.0](LICENSE).
Adapted files retain their original copyright and license notices.
