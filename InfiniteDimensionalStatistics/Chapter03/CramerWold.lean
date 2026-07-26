/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.ScalarCentralLimit
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Chapter 3: Cramér--Wold assembly

Finite-dimensional weak convergence is assembled from convergence of every real
inner-product projection.  The proof uses Mathlib's Lévy convergence theorem for
probability measures on finite-dimensional real inner-product spaces.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory RealInnerProductSpace
open scoped Real Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section CharacteristicFunctions

variable {E Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

/--
The characteristic function of the law of a vector at `t` is the scalar
characteristic function of its inner-product projection at frequency one.
-/
theorem charFun_map_eq_charFun_inner
    (μ : Measure Ω) (X : Ω → E) (hX : AEMeasurable X μ) (t : E) :
    charFun (μ.map X) t =
      charFun (μ.map (fun ω => ⟪X ω, t⟫_ℝ)) 1 := by
  rw [charFun_apply, integral_map hX (by fun_prop),
    charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  simp

end CharacteristicFunctions

section CramerWold

variable {E Ω Ω' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/--
**Cramér--Wold theorem, random-variable form.**

A sequence of finite-dimensional random vectors converges in distribution once
every real inner-product projection converges in distribution.
-/
theorem tendstoInDistribution_of_forall_inner
    (X : ℕ → Ω → E) (Y : Ω' → E)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : AEMeasurable Y P')
    (hproj : ∀ t : E,
      TendstoInDistribution
        (fun n ω => ⟪X n ω, t⟫_ℝ) atTop
        (fun ω => ⟪Y ω, t⟫_ℝ)
        (fun _ => P) P') :
    TendstoInDistribution X atTop Y (fun _ => P) P' := by
  refine ⟨hX, hY, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have hs :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
      (hproj t).tendsto) (1 : ℝ)
  convert hs using 1
  · funext n
    exact charFun_map_eq_charFun_inner P (X n) (hX n) t
  · exact charFun_map_eq_charFun_inner P' Y hY t

/--
A convenient formulation for triangular arrays or process projections: the
finite-dimensional law follows from the scalar projection laws without any
additional tightness argument, because the target space is finite dimensional.
-/
theorem finiteDimensionalConvergence_of_projectionConvergence
    (X : ℕ → Ω → E) (Y : Ω' → E)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : AEMeasurable Y P')
    (hproj : ∀ t : E,
      TendstoInDistribution
        (fun n ω => ⟪X n ω, t⟫_ℝ) atTop
        (fun ω => ⟪Y ω, t⟫_ℝ)
        (fun _ => P) P') :
    TendstoInDistribution X atTop Y (fun _ => P) P' :=
  tendstoInDistribution_of_forall_inner X Y hX hY hproj

end CramerWold

end Chapter03
end InfiniteDimensionalStatistics
