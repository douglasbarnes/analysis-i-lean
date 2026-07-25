/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import Mathlib

/-!
# Chapter 3: Empirical measures and empirical processes

This file begins the source-order formalisation of Chapter 3 of Giné and Nickl,
*Mathematical Foundations of Infinite-Dimensional Statistical Models*.

The declarations correspond to the foundational definitions on printed
pages 109–111.  The book assumes a positive sample size.  The Lean definitions
are total at sample size zero; later theorems that use normalisation identities
must retain the source hypothesis `0 < n`.

No theorem from the chapter is asserted in this file without proof.  The
extended-valued supremum definitions below separate the mathematical supremum
from the chapter's later measurability conventions.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section EmpiricalMeasure

variable {S : Type*} [MeasurableSpace S]

/--
The empirical measure

`Pₙ = n⁻¹ ∑ᵢ δ_(Xᵢ)`.

Source: equation (3.1), printed page 109; specification id
`empirical_measure`.
-/
def empiricalMeasure {n : ℕ} (X : Fin n → S) : Measure S :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (X i)

/--
The empirical average of a real-valued function,

`Pₙ f = n⁻¹ ∑ᵢ f(Xᵢ)`.

Source: equation (3.1), printed page 109; specification id
`empirical_measure`.
-/
def empiricalMean {n : ℕ} (X : Fin n → S) (f : S → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (X i)

/--
The book's notation `Qf` for the Bochner integral `∫ x, f x ∂Q`.

Source: unnumbered notation on printed page 110; specification id
`Qf_notation`.
-/
def measureIntegral (Q : Measure S) (f : S → ℝ) : ℝ :=
  ∫ x, f x ∂Q

/--
The uncentred empirical process indexed by a function class `𝓕`.

The subtype index preserves membership in the class at the type level.
Source: equation (3.2), printed page 110; specification id
`uncentred_empirical_process`.
-/
def uncentredEmpiricalProcess {n : ℕ} (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : 𝓕 → ℝ :=
  fun f ↦ empiricalMean X f.1

/--
The centred, normalised empirical process

`νₙ(f) = √n (Pₙf - Pf)`.

The source's i.i.d. and integrability assumptions belong to the theorems that
use this definition.  Source: equation (3.3), printed page 110;
specification id `centred_empirical_process`.
-/
def centredEmpiricalProcess {n : ℕ} (P : Measure S) (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : 𝓕 → ℝ :=
  fun f ↦ Real.sqrt (n : ℝ) * (empiricalMean X f.1 - measureIntegral P f.1)

/--
The uniform empirical deviation over `𝓕`.

The book writes a real supremum.  This foundational definition is
`ℝ≥0∞`-valued so it is total for empty or unbounded classes.  A later bounded
nonempty-class lemma will identify it with the source's real supremum.

Source: unnumbered definition on printed page 110; specification id
`uniform_deviation`.
-/
def uniformEmpiricalDeviation {n : ℕ} (P : Measure S) (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : ℝ≥0∞ :=
  ⨆ f : 𝓕, ENNReal.ofReal |empiricalMean X f.1 - measureIntegral P f.1|

end EmpiricalMeasure

section KernelDensityEstimator

/--
The usual one-dimensional kernel rescaling `K_h(u) = h⁻¹ K(u / h)`.

The source requires `h > 0`; the definition is total and leaves that condition
to estimator theorems.  Source: equation (3.4), printed pages 110–111;
specification id `kde_example`.
-/
def rescaledKernel (K : ℝ → ℝ) (h u : ℝ) : ℝ :=
  h⁻¹ * K (u / h)

/-- The translate class `{y ↦ K_h(x-y) : x ∈ ℝ}`. -/
def kernelTranslateClass (K : ℝ → ℝ) (h : ℝ) : Set (ℝ → ℝ) :=
  Set.range (fun x ↦ fun y ↦ rescaledKernel K h (x - y))

/--
The kernel density estimator written as an empirical average:

`fₙ(x) = Pₙ (y ↦ K_h(x-y))`.

Source: equation (3.4), printed pages 110–111; specification id
`kde_example`.
-/
def kernelDensityEstimator {n : ℕ} (X : Fin n → ℝ) (K : ℝ → ℝ)
    (h x : ℝ) : ℝ :=
  empiricalMean X (fun y ↦ rescaledKernel K h (x - y))

end KernelDensityEstimator

section SampleBoundedness

/-- A real stochastic process indexed by `T`. -/
abbrev RealProcess (T Ω : Type*) := T → Ω → ℝ

/--
The extended sample-path supremum `sup_t |X_t(ω)|`.

Using `ℝ≥0∞` keeps the definition total before any boundedness or measurability
assumption is imposed.
-/
def sampleSupNorm {T Ω : Type*} (X : RealProcess T Ω) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : T, ENNReal.ofReal |X t ω|

/--
A process is sample bounded when its sample-path supremum is finite almost
surely.  Measurability of the supremum is deliberately not built into this
predicate; the chapter handles that issue through separate countability and
separability hypotheses.

Source: equation (3.5), printed page 111; specification id `sample_bounded`.
-/
def IsSampleBounded {T Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealProcess T Ω) : Prop :=
  ∀ᵐ ω ∂P, sampleSupNorm X ω < ∞

end SampleBoundedness

end Chapter03
end InfiniteDimensionalStatistics
