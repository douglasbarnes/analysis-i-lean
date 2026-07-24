# Notation, naming and provenance policy

## General rule

Use Mathlib notation and canonical types unless the book's statement cannot be expressed faithfully
without a local abstraction. A notation preference is never sufficient reason to duplicate a
Mathlib definition.

## Namespace policy

- All new declarations live under `InfiniteDimensionalStatistics`.
- Foundation declarations use `InfiniteDimensionalStatistics.Foundations.<Area>`.
- Chapter-local declarations use `InfiniteDimensionalStatistics.ChapterNN`.
- Open namespaces locally and minimally. Do not add repository-wide `open` commands.
- Do not place book declarations in the root namespace or in existing course namespaces.

## Declaration naming

- Types, structures and classes use `UpperCamelCase`.
- Definitions and theorems use descriptive `lowerCamelCase` names.
- Predicate names begin with `Is`, `Has` or `Mem` when that is the established Mathlib convention.
- Avoid chapter numbers and source labels in Lean names. Stable source identity belongs in
  `BookManifest.yaml`.
- Helper lemmas receive semantic names; names such as `aux1`, `technicalLemma` and `obvious` are
  prohibited outside a short private proof block.
- A theorem re-exporting Mathlib should normally retain the Mathlib declaration directly. Add an
  alias only when it provides a stable book-facing statement and the manifest records the match.

## Binder and object conventions

- Measurable spaces: `Ω`, `S`, `T`; probability measures: `P`, `Q`, `μ`, `ν`.
- Random variables and stochastic processes: `X`, `Y`, `G`; observed values: `x`, `y`.
- Parameters: `θ`, `η`; parameter spaces: `Θ`, `H`.
- Function classes: `F`, `G`, `𝓕` only when scoped notation is justified.
- Banach and Hilbert spaces: `E`, `F`, `H`; dual elements: `L`, `ℓ`.
- Sample size: `n`; indices: `i`, `j`, `k`; smoothness: `s`, `α`, `β`; integrability exponents:
  `p`, `q`.

These are conventions, not permissions to shadow existing declarations or make binder types
implicit when the statement becomes ambiguous.

## Probability and integration

- Use `MeasureTheory.Measure`, `MeasureTheory.ProbabilityMeasure` and
  `MeasureTheory.IsProbabilityMeasure` rather than a bespoke probability-space record.
- Use Mathlib's Bochner integral and expectation notation where available.
- Laws are push-forward measures. Do not introduce an untyped `law` function.
- Almost-everywhere statements use Mathlib filters and `=ᵐ[μ]`.
- Independence, identical distribution and convergence modes use Mathlib predicates whenever their
  statements match.

## Norms and function spaces

- `‖x‖` denotes the norm supplied by the active normed-space instance.
- Distinguish pointwise functions from `Lp` equivalence classes explicitly.
- Record the measure in every `L^p` object when it is not inferable without ambiguity.
- Sobolev, Besov and Hölder notation must be scoped. The defining norm, domain, boundary convention
  and homogeneous/inhomogeneous choice must be recorded in the manifest notes before notation is
  introduced.
- Do not overload one notation for both a function class and its normed-space completion.

## Empirical-process notation

The following notation is reserved but not introduced by this baseline:

- empirical measure and empirical average;
- centred empirical process;
- covering and bracketing numbers;
- stochastic-order notation such as `O_P` and `o_P`.

Each requires a formal definition and a scoped notation module. Informal asymptotic notation must
not appear in theorem statements as an uninterpreted proposition.

## Local notation requirements

Any new notation must:

1. be declared with `scoped` unless it is an exact Mathlib convention;
2. live in a file named for the relevant area, not in `Prelude.lean`;
3. have a docstring stating its expansion;
4. appear in `BookManifest.yaml` when it corresponds to book notation;
5. avoid changing parser precedence for existing Mathlib notation.

## Source provenance

Every book-facing declaration must have a docstring containing its manifest ID. The manifest entry,
not the docstring, is authoritative and must include:

- printed chapter, section, label and page;
- exact source statement;
- uploaded source filename and checksum at book level;
- statement-fidelity notes;
- exact Mathlib matches and dependencies;
- statement-audit and proof-audit status;
- axiom report.

Do not cite a theorem as "from the book" without a page and stable manifest ID. Corrections,
errata and edition differences must be recorded in `notes`, never silently incorporated.

## Import and attribute discipline

- Add `[simp]`, `[aesop]`, coercions and instances only with a documented normalization or search
  rationale.
- Avoid global `attribute` changes.
- Prefer explicit local instances to low-priority global instances.
- New classical reasoning should be locally scoped and visible in the axiom audit.
- No `axiom`, `sorry`, `admit` or theorem-hiding `opaque` declaration is permitted.
