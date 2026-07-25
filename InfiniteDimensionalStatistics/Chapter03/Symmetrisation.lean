/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Concentration

/-!
# Chapter 3: Symmetrisation and contraction interfaces

Source-order definitions for the independent-copy and Rademacher arguments used
throughout Sections 3.1–3.5.  No symmetrisation or contraction inequality is
asserted here without proof.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Copies

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Two random variables on one probability space are independent copies. -/
def AreIndependentCopies (P : Measure Ω) (X X' : Ω → S) : Prop :=
  Measurable X ∧ Measurable X' ∧
    Measure.map X P = Measure.map X' P ∧ ProbabilityTheory.IndepFun X X' P

/-- A real random variable is symmetric about zero. -/
def IsSymmetricAboutZero (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    Measure.map X P = Measure.map (fun ω ↦ -X ω) P

end Copies

section FiniteSamples

variable {S : Type*}

/-- Difference of empirical averages formed from a sample and an independent copy. -/
def symmetrisedEmpiricalDifference {n : ℕ}
    (X X' : Fin n → S) (f : S → ℝ) : ℝ :=
  empiricalMean X f - empiricalMean X' f

/-- The Rademacher average of `f` along a fixed sample. -/
def rademacherAverage {Ω : Type*} {n : ℕ}
    (ε : Fin n → Ω → ℝ) (X : Fin n → S) (f : S → ℝ) : Ω → ℝ :=
  fun ω ↦ (n : ℝ)⁻¹ * ∑ i, ε i ω * f (X i)

/-- The normalised Rademacher process `n⁻¹ᐟ² ∑ εᵢ f(Xᵢ)`. -/
def normalisedRademacherProcess {Ω : Type*} {n : ℕ}
    (ε : Fin n → Ω → ℝ) (X : Fin n → S)
    (𝓕 : Set (S → ℝ)) : 𝓕 → Ω → ℝ :=
  fun f ω ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ i, ε i ω * f.1 (X i)

/-- Pointwise multiplication of a function class by a scalar. -/
def scalarClass (a : ℝ) (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  (fun f ↦ fun x ↦ a * f x) '' 𝓕

/-- The symmetric hull `𝓕 ∪ (-𝓕)`. -/
def symmetricHull (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  𝓕 ∪ (fun f ↦ fun x ↦ -f x) '' 𝓕

/-- The star hull `{a f : |a| ≤ 1, f ∈ 𝓕}`. -/
def starHull (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  {g | ∃ a : ℝ, |a| ≤ 1 ∧ ∃ f ∈ 𝓕, g = fun x ↦ a * f x}

/-- A pointwise contraction fixing zero. -/
def IsContractionAtZero (φ : ℝ → ℝ) : Prop :=
  φ 0 = 0 ∧ LipschitzWith 1 φ

/-- The image of a class under a scalar function. -/
def compositionClass (φ : ℝ → ℝ) (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  (fun f ↦ φ ∘ f) '' 𝓕

end FiniteSamples

end Chapter03
end InfiniteDimensionalStatistics
