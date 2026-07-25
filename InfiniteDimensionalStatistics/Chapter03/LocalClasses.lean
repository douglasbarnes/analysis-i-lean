/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.GaussianBridge

/-!
# Chapter 3: Local difference classes

Local classes used by Theorems 3.7.52–3.7.55.  The corrected localisation
`P(f-g)² ≤ ε / √n` is recorded literally.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

variable {S : Type*} [MeasurableSpace S]

/-- Pointwise difference class `𝓕-𝓕`. -/
def differenceClass (𝓕 : Set (S → ℝ)) : Set (S → ℝ) :=
  {h | ∃ f ∈ 𝓕, ∃ g ∈ 𝓕, h = fun x ↦ f x - g x}

/-- Population squared `L²(P)` size. -/
def populationSquaredL2 (P : Measure S) (f : S → ℝ) : ℝ :=
  ∫ x, f x ^ 2 ∂P

/-- Population-local difference class at radius `δ`. -/
def populationLocalDifferenceClass
    (P : Measure S) (𝓕 : Set (S → ℝ)) (δ : ℝ) : Set (S → ℝ) :=
  {h | h ∈ differenceClass 𝓕 ∧ populationSquaredL2 P h ≤ δ}

/--
The corrected class `𝓕'_{ε,n}` from Theorem 3.7.52.

Source: Theorem 3.7.52, printed pp. 273–275; the official correction uses
`ε / √n`, not the erroneous hardback cross-reference.
-/
def donskerLocalDifferenceClass
    (P : Measure S) (𝓕 : Set (S → ℝ))
    (ε : ℝ) (n : ℕ) : Set (S → ℝ) :=
  populationLocalDifferenceClass P 𝓕 (ε / Real.sqrt (n : ℝ))

/-- Empirical `L²`-local difference class. -/
def empiricalL2LocalDifferenceClass {n : ℕ}
    (X : Fin n → S) (𝓕 : Set (S → ℝ)) (δ : ℝ) : Set (S → ℝ) :=
  {h | h ∈ differenceClass 𝓕 ∧ empiricalL2PseudoMetric X h 0 ≤ δ}

/-- Empirical `L¹` pseudometric. -/
def empiricalL1PseudoMetric {n : ℕ}
    (X : Fin n → S) (f g : S → ℝ) : ℝ :=
  empiricalMean X (fun x ↦ |f x - g x|)

/-- Empirical `L¹`-local difference class. -/
def empiricalL1LocalDifferenceClass {n : ℕ}
    (X : Fin n → S) (𝓕 : Set (S → ℝ)) (δ : ℝ) : Set (S → ℝ) :=
  {h | h ∈ differenceClass 𝓕 ∧ empiricalL1PseudoMetric X h 0 ≤ δ}

/-- Random covering number of a local difference class. -/
def localEmpiricalCoveringNumber {n : ℕ}
    (X : Fin n → S) (𝓕local : Set (S → ℝ))
    (p : ℕ) (ρ : ℝ) : WithTop ℕ :=
  if p = 1 then coveringNumber (empiricalL1PseudoMetric X) 𝓕local ρ
  else coveringNumber (empiricalL2PseudoMetric X) 𝓕local ρ

/-- Normalised log trace growth of a set class on a sample. -/
def normalisedLogTraceGrowth {n : ℕ}
    (𝓒 : Set (Set S)) (X : Fin n → S) : ℝ :=
  (n : ℝ)⁻¹ * Real.log ((setClassTrace 𝓒 (Finset.univ.image X)).ncard : ℕ)

end Chapter03
end InfiniteDimensionalStatistics
