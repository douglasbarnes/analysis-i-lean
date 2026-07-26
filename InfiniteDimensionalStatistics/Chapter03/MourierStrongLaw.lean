/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.BennettOptimization
import Mathlib.Probability.StrongLaw

/-!
# Chapter 3: Mourier strong law

Corollary 3.7.21 is supplied directly by Mathlib's Banach-valued strong law of
large numbers.  The statement keeps the Bochner-integrability qualification
added by the official correction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Mourier

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/--
Mourier's strong law in a Banach space.

For pairwise independent, identically distributed, Bochner-integrable
`E`-valued random variables, the empirical averages converge almost surely to
the Bochner expectation.

Source: Corollary 3.7.21, pp. 241–242; specification id
`corollary_3_7_21`.
-/
theorem mourier_strong_law
    (X : ℕ → Ω → E)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
        atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  exact ProbabilityTheory.strong_law_ae X hint hindep hident

end Mourier

end Chapter03
end InfiniteDimensionalStatistics
