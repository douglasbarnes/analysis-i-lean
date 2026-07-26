/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EntropyGrowthLemmas

/-!
# Chapter 3: Lorentz `L₂,₁` lemmas

Elementary invariance and monotonicity properties of the Lorentz multiplier
functional introduced in equation (3.49).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Lorentz

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Lorentz functional is nonnegative. -/
theorem lorentzL21_nonneg (P : Measure Ω) (ξ : Ω → ℝ) :
    0 ≤ lorentzL21 P ξ :=
  bot_le

/-- The zero random variable has zero Lorentz functional. -/
@[simp] theorem lorentzL21_zero (P : Measure Ω) :
    lorentzL21 P (fun _ => 0) = 0 := by
  simp [lorentzL21]

/-- Negation does not change the Lorentz functional. -/
@[simp] theorem lorentzL21_neg (P : Measure Ω) (ξ : Ω → ℝ) :
    lorentzL21 P (fun ω => -ξ ω) = lorentzL21 P ξ := by
  simp [lorentzL21]

/-- Taking absolute values does not change the Lorentz functional. -/
@[simp] theorem lorentzL21_abs (P : Measure Ω) (ξ : Ω → ℝ) :
    lorentzL21 P (fun ω => |ξ ω|) = lorentzL21 P ξ := by
  simp [lorentzL21]

/-- Pointwise domination of absolute values implies domination of Lorentz functionals. -/
theorem lorentzL21_mono_abs
    (P : Measure Ω) {ξ η : Ω → ℝ}
    (hξη : ∀ ω, |ξ ω| ≤ |η ω|) :
    lorentzL21 P ξ ≤ lorentzL21 P η := by
  unfold lorentzL21
  apply lintegral_mono
  intro t
  apply ENNReal.sqrt_le_sqrt
  apply measure_mono
  intro ω hω
  exact hω.trans_le (hξη ω)

/-- Domination of the underlying measure implies domination of Lorentz functionals. -/
theorem lorentzL21_mono_measure
    {P Q : Measure Ω} (hPQ : P ≤ Q) (ξ : Ω → ℝ) :
    lorentzL21 P ξ ≤ lorentzL21 Q ξ := by
  unfold lorentzL21
  apply lintegral_mono
  intro t
  exact ENNReal.sqrt_le_sqrt (hPQ {ω | t < |ξ ω|})

/-- Lorentz membership is invariant under negation. -/
@[simp] theorem memLorentzL21_neg_iff (P : Measure Ω) (ξ : Ω → ℝ) :
    MemLorentzL21 P (fun ω => -ξ ω) ↔ MemLorentzL21 P ξ := by
  simp [MemLorentzL21]

/-- Lorentz membership is invariant under absolute value. -/
@[simp] theorem memLorentzL21_abs_iff (P : Measure Ω) (ξ : Ω → ℝ) :
    MemLorentzL21 P (fun ω => |ξ ω|) ↔ MemLorentzL21 P ξ := by
  simp [MemLorentzL21]

/-- Absolute-value domination preserves Lorentz membership. -/
theorem MemLorentzL21.mono_abs
    (P : Measure Ω) {ξ η : Ω → ℝ}
    (hη : MemLorentzL21 P η)
    (hξη : ∀ ω, |ξ ω| ≤ |η ω|) :
    MemLorentzL21 P ξ := by
  exact (lorentzL21_mono_abs P hξη).trans_lt hη

/-- Restricting to a smaller measure preserves Lorentz membership. -/
theorem MemLorentzL21.mono_measure
    {P Q : Measure Ω} (hPQ : P ≤ Q) {ξ : Ω → ℝ}
    (hξ : MemLorentzL21 Q ξ) :
    MemLorentzL21 P ξ := by
  exact (lorentzL21_mono_measure hPQ ξ).trans_lt hξ

end Lorentz

end Chapter03
end InfiniteDimensionalStatistics
