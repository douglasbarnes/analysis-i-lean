# Notation Policy

This policy applies to all Lean files and declaration-level specifications under `InfiniteDimensionalStatistics`.

## General principles

1. Reuse Mathlib structures and notation whenever they express the source statement without changing its mathematical content.
2. Preserve the book's quantifier order, dependence of constants and measurable-space assumptions in specification files.
3. Do not encode a source typo or ambiguity as a silently corrected Lean theorem. Record the issue and, where necessary, formalise separately named original and corrected variants.
4. Keep implementation difficulty separate from source pass assignment.

## Namespaces and declaration names

Lean declarations belong under:

```lean
namespace InfiniteDimensionalStatistics
```

Chapter-specific declarations should use descriptive names in chapter modules rather than source-number-only identifiers. Source numbers must appear in docstrings or specification metadata.

## Measures and probability

- Use `Measure α` for measures and `[MeasurableSpace α]` for measurable spaces.
- Use `IsProbabilityMeasure μ` rather than a bespoke probability-measure wrapper unless a later interface demonstrably requires a bundled object.
- Use `Measure.dirac`, product measures, kernels and Radon–Nikodym derivatives from Mathlib.
- Use almost-everywhere equality `f =ᵐ[μ] g` and filter notation rather than manually quantified null sets when equivalent.
- State measurability hypotheses explicitly whenever Mathlib cannot infer them from the types.

## Random variables and processes

- A random variable is normally a measurable function `X : Ω → S` with a separate hypothesis `Measurable X`.
- A stochastic process indexed by `T` is represented as `X : T → Ω → S`; joint measurability uses `Measurable (Function.uncurry X)`.
- Finite-dimensional distributions, modifications and separability require named predicates. Do not reduce Doob separability to topological separability of the index set.

## Integrals and expectations

- Use `∫ x, f x ∂μ` for Bochner integrals and the corresponding Mathlib expectation notation when available.
- Use `ℝ≥0∞` for measure-valued quantities and `EReal` only where signed extended values are mathematically required.
- Coercions to `ℝ` must be justified by finiteness hypotheses.

## Norms and function spaces

- Use `‖x‖` and `dist x y` for norm and metric notation.
- Use Mathlib's `Lp`, `MeasureTheory.MemLp`, continuous-map, bounded-continuous-map and Hilbert-space APIs before introducing local wrappers.
- Sobolev, Besov, Hölder and multiscale spaces should be represented by reusable structures or predicates with parameters and ambient measure/domain explicit.
- Equivalent norms appearing in the book must not be definitionally identified unless the specification explicitly chooses one canonical norm and records the equivalence theorem.

## Probability metrics and information quantities

Names should distinguish:

- total variation distance;
- Hellinger distance and squared Hellinger distance;
- Kullback–Leibler divergence;
- variance of the log-likelihood ratio;
- weak, Wasserstein and multiscale metrics.

Normalisation conventions must be included in declaration names or docstrings when the literature has competing factors such as `1/2`.

## Asymptotics and constants

- Use filters (`atTop`, `Tendsto`, `IsLittleO`, `IsBigO`, `IsTheta`) for asymptotic statements where practical.
- Record uniformity domains explicitly.
- Constants named `C`, `c`, `K` or similar are existentially quantified unless the source gives a value.
- Every dependency of a constant must be stated in the specification and reflected in Lean binder order.
- Phrases such as "for sufficiently large n" require an explicit threshold whose dependencies are recorded.

## Sets, classes and suprema

- Function classes are sets `Set (α → β)` unless a bundled structure supplies essential data.
- Suprema over nonempty classes require explicit nonemptiness or an extended-value formulation.
- Essential suprema use the measure-theoretic API; ordinary suprema must not replace them silently.

## Exercises and starred material

- `exercise` is reserved for declarations extracted from exercises.
- `starred` is reserved for material explicitly starred in the source.
- A theorem requiring major new infrastructure remains `core` when the source is unstarred; its `difficulty` field records the implementation burden.

## Source references

Every implemented declaration should be traceable to:

- chapter and source number;
- printed page;
- the corresponding specification identifier;
- any central-review or corrigendum item affecting the statement.
