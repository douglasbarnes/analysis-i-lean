/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EmpiricalMeasureLemmas
import Mathlib.Probability.StrongLaw

/-!
# Chapter 3: Finite-class Glivenko–Cantelli theorem

A finite function class is bundled as a random vector in `Fin m → ℝ`.  Mathlib's
Banach-valued strong law then gives simultaneous almost-sure convergence of all
coordinates, hence convergence in the finite sup norm.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Finset

namespace InfiniteDimensionalStatistics
namespace Chapter03

section FiniteClass

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ}

/-- Evaluation vector of a finite indexed function class. -/
def finiteClassEvaluation (F : Fin m → S → ℝ) (x : S) : Fin m → ℝ :=
  fun j ↦ F j x

/-- The empirical average vector of a finite indexed class. -/
def finiteClassEmpiricalAverage
    (F : Fin m → S → ℝ) (X : ℕ → S) (n : ℕ) : Fin m → ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, finiteClassEvaluation F (X i)

/-- The population expectation vector of a finite indexed class. -/
def finiteClassExpectation
    (P : Measure S) (F : Fin m → S → ℝ) : Fin m → ℝ :=
  fun j ↦ ∫ x, F j x ∂P

/-- Measurability of the finite evaluation vector. -/
theorem measurable_finiteClassEvaluation
    (F : Fin m → S → ℝ) (hF : ∀ j, Measurable (F j)) :
    Measurable (finiteClassEvaluation F) := by
  rw [measurable_pi_iff]
  exact hF

/--
Simultaneous strong law for a finite indexed function class.

This is the finite-class instance underlying Definition 3.7.10 and the finite
case of Corollary 3.7.17.
-/
theorem finiteClass_strongLaw
    (X : ℕ → Ω → S) (F : Fin m → S → ℝ)
    (hF : ∀ j, Measurable (F j))
    (hint : Integrable (fun ω ↦ finiteClassEvaluation F (X 0 ω)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ finiteClassEmpiricalAverage F (fun i ↦ X i ω) n)
        atTop
        (𝓝 (∫ ω, finiteClassEvaluation F (X 0 ω) ∂μ)) := by
  let Y : ℕ → Ω → (Fin m → ℝ) :=
    fun i ω ↦ finiteClassEvaluation F (X i ω)
  have hEval : Measurable (finiteClassEvaluation F) :=
    measurable_finiteClassEvaluation F hF
  have hYindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y) := by
    intro i j hij
    exact (hindep hij).comp hEval hEval
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    exact (hident i).comp hEval
  simpa [Y, finiteClassEmpiricalAverage] using
    (ProbabilityTheory.strong_law_ae Y hint hYindep hYident)

/--
Finite-class uniform deviation tends to zero almost surely, expressed by the
sup norm on `Fin m → ℝ`.
-/
theorem finiteClass_uniformDeviation_tendsto_zero
    (X : ℕ → Ω → S) (F : Fin m → S → ℝ)
    (hF : ∀ j, Measurable (F j))
    (hint : Integrable (fun ω ↦ finiteClassEvaluation F (X 0 ω)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦
          ‖finiteClassEmpiricalAverage F (fun i ↦ X i ω) n -
            (∫ u, finiteClassEvaluation F (X 0 u) ∂μ)‖)
        atTop (𝓝 0) := by
  filter_upwards [finiteClass_strongLaw X F hF hint hindep hident] with ω hω
  exact tendsto_norm_sub_nhds_zero_iff.mpr hω

end FiniteClass

end Chapter03
end InfiniteDimensionalStatistics
