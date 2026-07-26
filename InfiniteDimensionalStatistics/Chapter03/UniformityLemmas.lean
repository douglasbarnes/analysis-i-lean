/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.BoundedLipschitzLemmas

/-!
# Chapter 3: Uniformity and weak-convergence closure lemmas

Elementary order closure of the uniform Donsker and uniformly pre-Gaussian
predicates, together with constant and pointwise-congruence rules for the
bounded-Lipschitz formulation of weak convergence.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section WeakConvergence

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

/-- A constant sequence of measures weakly converges to its constant value. -/
@[simp] theorem weaklyConverges_const (Q : Measure E) :
    WeaklyConverges (fun _ => Q) Q := by
  unfold WeaklyConverges
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- Pointwise equal sequences have the same weak-convergence property. -/
theorem WeaklyConverges.congr
    {P R : ℕ → Measure E} {Q : Measure E}
    (hP : WeaklyConverges P Q) (hPR : ∀ n, P n = R n) :
    WeaklyConverges R Q := by
  unfold WeaklyConverges at hP ⊢
  exact hP.congr' (Filter.Eventually.of_forall fun n => by rw [hPR n])

/-- Replacing the limit measure by an equal measure preserves weak convergence. -/
theorem WeaklyConverges.congr_limit
    {P : ℕ → Measure E} {Q R : Measure E}
    (hP : WeaklyConverges P Q) (hQR : Q = R) :
    WeaklyConverges P R := by
  simpa [hQR] using hP

end WeakConvergence

section UniformDonskerDiscrepancy

variable {I J : Type*}

/-- The identically zero discrepancy is uniformly Donsker-negligible. -/
@[simp] theorem isUniformDonskerDiscrepancy_zero :
    IsUniformDonskerDiscrepancy (fun (_ : I) (_ : ℕ) => 0) := by
  unfold IsUniformDonskerDiscrepancy
  simp

/-- A pointwise smaller discrepancy inherits uniform convergence to zero. -/
theorem IsUniformDonskerDiscrepancy.mono
    {d e : I → ℕ → ℝ≥0∞}
    (he : IsUniformDonskerDiscrepancy e)
    (hde : ∀ i n, d i n ≤ e i n) :
    IsUniformDonskerDiscrepancy d := by
  unfold IsUniformDonskerDiscrepancy at he ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds he
    (fun _ => bot_le)
    (fun n => iSup_mono fun i => hde i n)

/-- Restricting or reindexing the family preserves a uniform discrepancy bound. -/
theorem IsUniformDonskerDiscrepancy.reindex
    {d : I → ℕ → ℝ≥0∞}
    (hd : IsUniformDonskerDiscrepancy d) (ι : J → I) :
    IsUniformDonskerDiscrepancy (fun j n => d (ι j) n) := by
  apply hd.mono
  intro j n
  exact le_iSup (fun i => d i n) (ι j)

end UniformDonskerDiscrepancy

section UniformPreGaussian

variable {S I J : Type*}

/-- Zero expected increments satisfy uniform pre-Gaussian equicontinuity. -/
@[simp] theorem isUniformlyPreGaussianFor_zero
    (metric : I → (S → ℝ) → (S → ℝ) → ℝ) :
    IsUniformlyPreGaussianFor metric (fun (_ : I) (_ : ℝ) => 0) := by
  unfold IsUniformlyPreGaussianFor
  simp

/-- Pointwise domination preserves uniform pre-Gaussian increment convergence. -/
theorem IsUniformlyPreGaussianFor.mono
    {metric : I → (S → ℝ) → (S → ℝ) → ℝ}
    {a b : I → ℝ → ℝ≥0∞}
    (hb : IsUniformlyPreGaussianFor metric b)
    (hab : ∀ i δ, a i δ ≤ b i δ) :
    IsUniformlyPreGaussianFor metric a := by
  unfold IsUniformlyPreGaussianFor at hb ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hb
    (fun _ => bot_le)
    (fun δ => iSup_mono fun i => hab i δ)

/-- Reindexing the family preserves uniform pre-Gaussian increment convergence. -/
theorem IsUniformlyPreGaussianFor.reindex
    {metric : I → (S → ℝ) → (S → ℝ) → ℝ}
    {a : I → ℝ → ℝ≥0∞}
    (ha : IsUniformlyPreGaussianFor metric a) (ι : J → I) :
    IsUniformlyPreGaussianFor
      (fun j => metric (ι j)) (fun j => a (ι j)) := by
  unfold IsUniformlyPreGaussianFor at ha ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds ha
    (fun _ => bot_le)
    (fun δ => iSup_le fun j => le_iSup (fun i => a i δ) (ι j))

end UniformPreGaussian

end Chapter03
end InfiniteDimensionalStatistics
