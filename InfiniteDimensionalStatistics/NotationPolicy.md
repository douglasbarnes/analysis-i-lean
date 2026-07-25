# Notation and Source-Fidelity Policy

## Source fidelity

The printed book statement is the specification baseline. Official errata are recorded explicitly. A suspected typo, missing measurability condition, ambiguous quantifier, or excessive generality is never repaired silently. Each entry records the printed reading, the issue, and any separately approved corrected reading.

A declaration whose operative formula is still described as “to be transcribed”, “schematic”, “recoverable only”, or equivalent is not accepted for P1.

## Pass and difficulty

`core`, `starred`, and `exercise` describe source position, not implementation effort.

- `core`: every unstarred declaration in main text or notes.
- `starred`: only declarations explicitly starred in the book.
- `exercise`: selected exercises.

Difficulty is independently one of `routine`, `substantial`, `major-library`, or `research-level`.

## Identifiers

Specification IDs are globally unique within a chapter package. Main-text IDs use a chapter-qualified stable slug or book label. Exercise IDs are prefixed by `ex.`. Lean names are proposals only until the chapter API is approved.

## Scalars and extended values

Real-valued statistical models use `ℝ` unless the source requires complex Fourier coefficients. Nonnegative extended quantities use `ℝ≥0∞`; signed extended integrals use an explicitly justified extended-real representation. Conversions between `ℝ`, `ℝ≥0`, `ℝ≥0∞`, and `EReal` are never implicit in theorem statements.

## Measures, laws, and densities

A statistical law is a `Measure` with a probability instance or an explicit mass-one hypothesis. Radon–Nikodym derivatives are equality-a.e. objects. Likelihood identities are stated with the governing measure and an almost-everywhere qualifier.

The total-variation convention is

\[
  \|P-Q\|_{\mathrm{TV}}=\sup_A|P(A)-Q(A)|
  =\frac12\int|p-q|\,d\mu.
\]

Any mathlib primitive with a different normalisation must be wrapped or converted explicitly.

## Function spaces and representatives

`L^p` objects are a.e.-equivalence classes. Pointwise claims require a chosen representative or a pointwise function space. The specification must distinguish `L∞` essential bounds from genuine pointwise suprema.

Boundary, periodised, and whole-line wavelet systems are separate structures. Endpoint conventions are explicit. Fourier-transform normalisation is fixed once per file and all constants are checked against it.

## Probability and measurability

All tests, estimators, suprema, infima, argmin selections, random radii, and membership events must carry measurable formulations. A random set is initially represented by a measurable membership predicate unless a measurable hyperspace API is supplied.

Independence is always relative to a named probability measure. Conditional expectations and sample splitting identify the conditioning σ-field and the independent component.

## Asymptotics

Quantifier order is part of the theorem. Informal relations such as `O`, `o`, and `asymp` are represented by filter-based predicates or by explicit eventual two-sided inequalities. Constants record every permitted dependency. Uniformity over parameter classes is not inferred from pointwise convergence.

## Source numbering and dependencies

Book theorem/equation numbers and printed pages remain metadata. Dependencies distinguish:

- earlier-book prerequisites;
- chapter-local prerequisite IDs;
- later uses;
- exercise delegation.

The chapter DAG contains only chapter-local nodes and must be acyclic. Cross-chapter dependencies are not forced into a chapter-local DAG.

## Errata

An official correction is stored alongside the hardback reading and identified as official errata. The formal declaration may use the corrected reading only when that choice is explicit in the entry. Suspected corrections without an official source remain central-review items.
