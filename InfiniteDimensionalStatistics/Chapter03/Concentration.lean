/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EmpiricalProcesses
import Mathlib.Probability.Moments.SubGaussian

/-!
# Chapter 3: Concentration interfaces

Definitions used by the concentration inequalities in Section 3.1.  This file
contains no unproved concentration theorem.  It fixes the objects that occur in
Lemmas 3.1.1–3.1.9 and their later applications.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

/-- The logarithmic moment-generating function `λ ↦ log E exp (λ X)`. -/
def logMomentGeneratingFunction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (λ : ℝ) : ℝ :=
  Real.log (∫ ω, Real.exp (λ * X ω) ∂P)

/-- A real-valued random variable with the symmetric Rademacher law. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : Ω → ℝ) : Prop :=
  Measurable ε ∧
    P {ω | ε ω = 1} = (2 : ℝ≥0∞)⁻¹ ∧
    P {ω | ε ω = -1} = (2 : ℝ≥0∞)⁻¹

/-- A mutually independent finite family of Rademacher variables. -/
def IsRademacherFamily {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (ε : Fin n → Ω → ℝ) : Prop :=
  (∀ i, IsRademacher P (ε i)) ∧ ProbabilityTheory.iIndepFun ε P

/-- The finite sum of a family of real random variables. -/
def randomVariableSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ ∑ i, X i ω

/-- A deterministic weighted Rademacher sum. -/
def rademacherWeightedSum {Ω : Type*} {n : ℕ}
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ) : Ω → ℝ :=
  fun ω ↦ ∑ i, a i * ε i ω

/-- Hamming distance on the discrete cube. -/
def hammingDistance {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ x i ≠ y i).card

/-- Bennett's convex function `h₁(u) = (1+u) log(1+u) - u`. -/
def bennettFunction (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u

/-- The Bernstein quadratic-linear exponent `t² / (2v + 2ct/3)`. -/
def bernsteinExponent (v c t : ℝ) : ℝ :=
  t ^ 2 / (2 * v + 2 * c * t / 3)

/-- The moment condition used in Proposition 3.1.8. -/
def BernsteinMomentCondition {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Fin n → Ω → ℝ) (v c : ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    ∑ i, ∫ ω, |X i ω| ^ m ∂P ≤
      (Nat.factorial m : ℝ) / 2 * v * c ^ (m - 2)

/-- Outer probability induced by a measure. -/
def outerProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) : ℝ≥0∞ :=
  P.toOuterMeasure A

/--
Outer expectation of a nonnegative extended-valued function, defined as the
infimum of the integrals of measurable majorants.
-/
def outerExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Y : Ω → ℝ≥0∞) (_hY : Measurable Y) (_hXY : X ≤ Y), ∫⁻ ω, Y ω ∂P

/-- A median of a real random variable. -/
def IsMedian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (m : ℝ) : Prop :=
  (2 : ℝ≥0∞)⁻¹ ≤ P {ω | X ω ≤ m} ∧
    (2 : ℝ≥0∞)⁻¹ ≤ P {ω | m ≤ X ω}

/-- The maximum of a finite nonempty real family, expressed by `sSup`. -/
def finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  sSup (Set.range f)

end Chapter03
end InfiniteDimensionalStatistics
