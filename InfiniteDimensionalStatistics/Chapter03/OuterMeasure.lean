/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Variation

/-!
# Chapter 3: Outer probability and measurable covers

Outer expectation, measurable majorants, and outer convergence definitions from
Section 3.7.  The nonnegative `ℝ≥0∞` outer expectation is defined in
`Concentration.lean`; this file adds the real-valued majorant formulation.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Filter Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Majorants

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `g` is a measurable pointwise majorant of `f`. -/
def IsMeasurableMajorant (f g : Ω → ℝ) : Prop :=
  Measurable g ∧ f ≤ g

/-- `g` is an integrable measurable pointwise majorant of `f`. -/
def IsIntegrableMeasurableMajorant
    (P : Measure Ω) (f g : Ω → ℝ) : Prop :=
  IsMeasurableMajorant f g ∧ Integrable g P

/--
Real-valued outer expectation, represented in `EReal` to allow infinite values.

Source: equation (3.242), printed p. 230; specification id
`outer_expectation`.
-/
def outerExpectationReal (P : Measure Ω) (f : Ω → ℝ) : EReal :=
  sInf {a : EReal | ∃ g : Ω → ℝ,
    IsIntegrableMeasurableMajorant P f g ∧
      a = EReal.ofReal (∫ ω, g ω ∂P)}

/-- A pointwise measurable cover: an essentially minimal measurable majorant. -/
def IsMeasurableCover (P : Measure Ω) (f fstar : Ω → ℝ) : Prop :=
  IsMeasurableMajorant f fstar ∧
  ∀ g : Ω → ℝ, IsMeasurableMajorant f g → fstar ≤ᵐ[P] g

/-- Outer expectation of the absolute value of a real function. -/
def outerExpectationAbs (P : Measure Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  outerExpectation P (fun ω ↦ ENNReal.ofReal |f ω|)

end Majorants

section OuterConvergence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Outer convergence in probability to a real random variable. -/
def ConvergesInOuterProbability
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  ∀ ε > 0,
    Tendsto (fun n ↦ outerProbability P {ω | ε < |X n ω - Y ω|})
      atTop (𝓝 0)

/-- Outer stochastic boundedness (`O_P^*`). -/
def IsOuterStochasticallyBounded
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∃ N : ℕ, ∀ n ≥ N,
    outerProbability P {ω | M < |X n ω|} ≤ ENNReal.ofReal ε

/-- Outer asymptotic negligibility (`o_P^*`). -/
def IsOuterAsymptoticallyNegligible
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ConvergesInOuterProbability P X (fun _ ↦ 0)

end OuterConvergence

end Chapter03
end InfiniteDimensionalStatistics
