/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.OuterMeasure

/-!
# Chapter 3: Glivenko–Cantelli and measurable classes

Definitions 3.7.10–3.7.11 and supporting finite-sample functionals.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section FiniteSamples

variable {S : Type*} [MeasurableSpace S]

/-- A finite weighted class supremum with an additional population term. -/
def classLinearSupremum {n : ℕ}
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (a : Fin n → ℝ) (b : ℝ) (x : Fin n → S) : ℝ≥0∞ :=
  ⨆ f : 𝓕,
    ENNReal.ofReal
      |(∑ i, a i * f.1 (x i)) + b * ∫ y, f.1 y ∂P|

/--
A class is `P`-measurable when all finite weighted class suprema are measurable
for the completed product law.

Source: Definition 3.7.11, printed p. 235; specification id
`definition_3_7_11`.
-/
def IsPMeasurableClass
    (P : Measure S) (𝓕 : Set (S → ℝ)) : Prop :=
  ∀ n : ℕ, ∀ a : Fin n → ℝ, ∀ b : ℝ,
    Measurable (classLinearSupremum P 𝓕 a b)

/-- Prefix of an infinite sample, indexed by `Fin n`. -/
def samplePrefix (X : ℕ → S) (n : ℕ) : Fin n → S :=
  fun i ↦ X i

end FiniteSamples

section GlivenkoCantelli

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Outer empirical deviation along the first `n` observations. -/
def samplePathUniformDeviation
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  uniformEmpiricalDeviation (samplePrefix (fun i ↦ X i ω) n) P 𝓕

/--
A function class is `P`-Glivenko–Cantelli along a sample when the outer uniform
empirical deviation tends to zero almost surely.

Source: Definition 3.7.10, printed p. 234; specification id
`definition_3_7_10`.
-/
def IsGlivenkoCantelli
    (sampleMeasure : Measure Ω) (P : Measure S)
    (𝓕 : Set (S → ℝ)) (X : ℕ → Ω → S) : Prop :=
  ∀ᵐ ω ∂sampleMeasure,
    Tendsto (fun n ↦ samplePathUniformDeviation P 𝓕 X n ω)
      atTop (𝓝 0)

/-- Weak Glivenko–Cantelli convergence in outer probability. -/
def IsWeakGlivenkoCantelli
    (sampleMeasure : Measure Ω) (P : Measure S)
    (𝓕 : Set (S → ℝ)) (X : ℕ → Ω → S) : Prop :=
  ∀ ε > 0,
    Tendsto
      (fun n ↦ outerProbability sampleMeasure
        {ω | ENNReal.ofReal ε < samplePathUniformDeviation P 𝓕 X n ω})
      atTop (𝓝 0)

end GlivenkoCantelli

section ClassOperations

variable {S : Type*}

/-- Pointwise convex hull of a function class. -/
def convexHullClass (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  convexHull ℝ 𝓕

/-- Pointwise closure of a class in the product topology. -/
def pointwiseClosureClass (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  closure 𝓕

end ClassOperations

end Chapter03
end InfiniteDimensionalStatistics
