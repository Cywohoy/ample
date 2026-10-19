# Ample

Ample is a Lean library for defining mathematical objects and writing proofs.
It uses Lean 4.35.0's standard types, propositions, equality, and kernel.
Its only dependencies are `Init`, `Std`, and `Lean`, as shipped with Lean itself.

Ample uses Lean's existing kernel. The earlier Cubical foundations experiment
is archived separately and is not part of this package.

## Usage

```lean
import Ample

open Course
open scoped Course.Auto

theorem double_is_not_five (n : Int) : 2 * n ≠ 5 := by
  arith

theorem group_inverse {A : Type} (G : Group A) (a : A) :
    G.op a (G.inv a) = G.id := by
  group_calc G
```

The public namespaces remain `Course`, `Course.Auto`, and `course_*` to preserve existing imports and proofs.
Opening `Course` makes the mathematical names and scoped tactics available.
`open scoped Course.Auto` enables presentation normalization before and after proof steps.
Use `open scoped Classical` in scopes that should use classical logic by default.

`ext` and `indisc` apply one comparison layer by default, in goals and hypotheses.
Use `ext!` and `indisc!` to repeat comparisons, or specify a depth with `ext : 2` or `indisc : 2 at h`.
The depth notation for congruence is likewise `congr : 2`.
One registered mathematical comparison counts as one layer: for sets, `set_ext` compares membership conditions up to logical equivalence.
Iff theorems registered with `course_compare` connect equalities and their comparison conditions in both directions.
Matching does not choose representatives or assign unresolved inputs of an existing goal.
`expand` unfolds one layer of definitions; `expand!` repeats unfolding.
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

Ample does not provide the former `suffices G` shorthand that searched for the connecting proof automatically.
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

Once a remote repository and release tag are available, a project can instead
pin a Git dependency (replace `OWNER` with the repository owner):

```toml
[[require]]
name = "ample"
git = "https://github.com/OWNER/ample.git"
rev = "v0.1.0"
```

Use the same `lean-toolchain` as Ample, then run `lake update ample` and `lake build`.
Git dependencies work without a package-registry listing. Reservoir indexing
is a separate process; see its [inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria).

## Modules

| Import | Contents |
| --- | --- |
| `Ample.Tactic` | Forward and backward inference, equality comparison, unfolding, and automation |
| `Ample.Tactic.Auto` | Optional normalization of proof-state presentation |
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
With `open Course` or `open scoped Course`, write this type as `A / R`, where `R : Relation A`.
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
| Inverse function | `inverseMapData` | `inverseMap` | `inverseMap_spec` |
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

Ample and the textbook are separate Git repositories.
For local development, place their checkouts next to one another and let the
textbook use `../Ample` as a path dependency. Its former tactic modules are thin import adapters.
The textbook presents definitions and complete proofs in teaching order; `Ample/Math/` exports the executable mathematical code without incomplete exercises.
Korean proof annotations stay in the textbook and are omitted from the English library exports.
Do not import a textbook module and its matching mathematical export together: both define the same `Course` declarations.

After editing the mathematical code in the textbook, run these commands from the textbook root:

```powershell
python scripts/sync_ample.py
python scripts/sync_ample.py --check
```

The exporter belongs to the textbook repository. It accepts `--ample-root PATH`
when the Ample checkout is elsewhere. Export synchronization requires Python;
normal library builds and use do not require Python or the textbook directory.
The generated mathematical files are committed in Ample so that every release
is buildable on its own. Changes to their definitions or proofs should be made
in the textbook and exported before committing both repositories.

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
