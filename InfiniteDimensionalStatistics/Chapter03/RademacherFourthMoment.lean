/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.RademacherMoments
import InfiniteDimensionalStatistics.Chapter03.BennettMGF
import Mathlib.Probability.Independence.Integration

/-!
# Chapter 3: Fourth moments of Rademacher sums

The exact fourth-moment recursion for independent centred real variables is
proved and specialised to weighted Rademacher sums.  This gives the moment
input used with Paley--Zygmund in Proposition 3.2.8.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter

namespace InfiniteDimensionalStatistics
namespace Chapter03

section IndependentFourthMoment

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ} {CX CY : ℝ}

/-- Fourth-moment expansion for two independent centred bounded variables. -/
theorem integral_add_pow_four_of_indep_centered
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : X ⟂ᵢ[μ] Y)
    (hCX : 0 ≤ CX) (hCY : 0 ≤ CY)
    (hXbound : ∀ᵐ ω ∂μ, |X ω| ≤ CX)
    (hYbound : ∀ᵐ ω ∂μ, |Y ω| ≤ CY)
    (hXmean : (∫ ω, X ω ∂μ) = 0)
    (hYmean : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) +
        6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
        ∫ ω, Y ω ^ 4 ∂μ := by
  have hX1 := integrable_pow_of_ae_abs_le hX.aemeasurable hCX hXbound 1
  have hX2 := integrable_pow_of_ae_abs_le hX.aemeasurable hCX hXbound 2
  have hX3 := integrable_pow_of_ae_abs_le hX.aemeasurable hCX hXbound 3
  have hX4 := integrable_pow_of_ae_abs_le hX.aemeasurable hCX hXbound 4
  have hY1 := integrable_pow_of_ae_abs_le hY.aemeasurable hCY hYbound 1
  have hY2 := integrable_pow_of_ae_abs_le hY.aemeasurable hCY hYbound 2
  have hY3 := integrable_pow_of_ae_abs_le hY.aemeasurable hCY hYbound 3
  have hY4 := integrable_pow_of_ae_abs_le hY.aemeasurable hCY hYbound 4
  have h31ind : (fun ω => X ω ^ 3) ⟂ᵢ[μ] Y :=
    hXY.comp (by fun_prop) (by fun_prop)
  have h22ind : (fun ω => X ω ^ 2) ⟂ᵢ[μ] (fun ω => Y ω ^ 2) :=
    hXY.comp (by fun_prop) (by fun_prop)
  have h13ind : X ⟂ᵢ[μ] (fun ω => Y ω ^ 3) :=
    hXY.comp (by fun_prop) (by fun_prop)
  have h31int : Integrable (fun ω => X ω ^ 3 * Y ω) μ :=
    h31ind.integrable_mul hX3 hY1
  have h22int : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ :=
    h22ind.integrable_mul hX2 hY2
  have h13int : Integrable (fun ω => X ω * Y ω ^ 3) μ :=
    h13ind.integrable_mul hX1 hY3
  have h31factor :
      (∫ ω, X ω ^ 3 * Y ω ∂μ) =
        (∫ ω, X ω ^ 3 ∂μ) * (∫ ω, Y ω ∂μ) :=
    h31ind.integral_fun_mul_eq_mul_integral hX3.1 hY1.1
  have h22factor :
      (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) =
        (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) :=
    h22ind.integral_fun_mul_eq_mul_integral hX2.1 hY2.1
  have h13factor :
      (∫ ω, X ω * Y ω ^ 3 ∂μ) =
        (∫ ω, X ω ∂μ) * (∫ ω, Y ω ^ 3 ∂μ) :=
    h13ind.integral_fun_mul_eq_mul_integral hX1.1 hY3.1
  have hexpand :
      (fun ω => (X ω + Y ω) ^ 4) =
        fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
          6 * (X ω ^ 2 * Y ω ^ 2) +
          4 * (X ω * Y ω ^ 3) + Y ω ^ 4 := by
    funext ω
    ring
  rw [hexpand]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_add]
      · rw [integral_add]
        · rw [integral_const_mul, integral_const_mul, integral_const_mul,
            h31factor, h22factor, h13factor, hXmean, hYmean]
          ring
        · exact hX4
        · exact h31int.const_mul 4
      · exact hX4.add (h31int.const_mul 4)
      · exact h22int.const_mul 6
    · exact (hX4.add (h31int.const_mul 4)).add (h22int.const_mul 6)
    · exact h13int.const_mul 4
  · exact ((hX4.add (h31int.const_mul 4)).add (h22int.const_mul 6)).add
      (h13int.const_mul 4)
  · exact hY4

end IndependentFourthMoment

section FiniteWeightedSums

variable {Ω ι : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ε : ι → Ω → ℝ} {a : ι → ℝ}

/-- Weighted sum over an arbitrary finite set of coordinates. -/
def finsetRademacherSum (s : Finset ι) (ε : ι → Ω → ℝ)
    (a : ι → ℝ) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, a i * ε i ω

/-- A finite weighted Rademacher sum is centred. -/
theorem integral_finsetRademacherSum_eq_zero
    (hε : ∀ i, IsRademacher μ (ε i)) (s : Finset ι) :
    (∫ ω, finsetRademacherSum s ε a ω ∂μ) = 0 := by
  unfold finsetRademacherSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun i _hi =>
      integral_mul_rademacher_eq_zero (ε i) (a i) (hε i)
  · intro i _hi
    exact (memLp_of_bounded
      (mul_rademacher_mem_Icc (ε i) (a i) (hε i))
      (hε i).1.aestronglyMeasurable.const_mul 2).integrable (by simp)

/-- A deterministic almost-sure bound for a finite weighted Rademacher sum. -/
theorem ae_abs_finsetRademacherSum_le
    (hε : ∀ i, IsRademacher μ (ε i)) (s : Finset ι) :
    ∀ᵐ ω ∂μ, |finsetRademacherSum s ε a ω| ≤ ∑ i ∈ s, |a i| := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : {i // i ∈ s}, |ε i.1 ω| = 1 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(hε i.1).2.1] with ω hω
    rcases hω with hneg | hpos <;> simp [hneg, hpos]
  filter_upwards [hall] with ω hω
  unfold finsetRademacherSum
  calc
    |∑ i ∈ s, a i * ε i ω| ≤ ∑ i ∈ s, |a i * ε i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |a i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, hω ⟨i, hi⟩, mul_one]

/-- Exact second moment of a finite weighted Rademacher sum. -/
theorem integral_sq_finsetRademacherSum
    (hε : ∀ i, IsRademacher μ (ε i))
    (hindep : iIndepFun ε μ) (s : Finset ι) :
    (∫ ω, finsetRademacherSum s ε a ω ^ 2 ∂μ) =
      ∑ i ∈ s, a i ^ 2 := by
  let Z : ι → Ω → ℝ := fun i ω => a i * ε i ω
  have hZmem : ∀ i ∈ s, MemLp (Z i) 2 μ := by
    intro i _hi
    exact memLp_of_bounded
      (mul_rademacher_mem_Icc (ε i) (a i) (hε i))
      (hε i).1.aestronglyMeasurable.const_mul 2
  have hZpair : Set.Pairwise (↑s) (fun i j => Z i ⟂ᵢ[μ] Z j) := by
    intro i hi j hj hij
    exact (hindep.indepFun hij).comp (by fun_prop) (by fun_prop)
  have hvar : Var[∑ i ∈ s, Z i; μ] = ∑ i ∈ s, a i ^ 2 := by
    simpa [Z, variance_mul_rademacher] using
      (ProbabilityTheory.IndepFun.variance_sum hZmem hZpair)
  have hmem : MemLp (fun ω => ∑ i ∈ s, Z i ω) 2 μ :=
    memLp_finsetSum' s hZmem
  have hcenter : (∫ ω, ∑ i ∈ s, Z i ω ∂μ) = 0 := by
    simpa [Z, finsetRademacherSum] using
      integral_finsetRademacherSum_eq_zero (a := a) hε s
  rw [← variance_of_integral_eq_zero hmem.aemeasurable hcenter]
  simpa [Z, finsetRademacherSum] using hvar

/-- Fourth moment of a single weighted Rademacher variable. -/
theorem integral_pow_four_mul_rademacher
    (i : ι) (hε : IsRademacher μ (ε i)) :
    (∫ ω, (a i * ε i ω) ^ 4 ∂μ) = a i ^ 4 := by
  calc
    (∫ ω, (a i * ε i ω) ^ 4 ∂μ) = ∫ _ω, a i ^ 4 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hε.ae_sq_eq_one] with ω hω
      rw [mul_pow, show ε i ω ^ 4 = (ε i ω ^ 2) ^ 2 by ring, hω]
      simp
    _ = a i ^ 4 := by simp

/-- The standard fourth-moment estimate `E S⁴ ≤ 3(∑aᵢ²)²`. -/
theorem integral_pow_four_finsetRademacherSum_le
    (hε : ∀ i, IsRademacher μ (ε i))
    (hindep : iIndepFun ε μ) (s : Finset ι) :
    (∫ ω, finsetRademacherSum s ε a ω ^ 4 ∂μ) ≤
      3 * (∑ i ∈ s, a i ^ 2) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finsetRademacherSum]
  | @insert i s hi ih =>
      let S : Ω → ℝ := finsetRademacherSum s ε a
      let Y : Ω → ℝ := fun ω => a i * ε i ω
      have hSmeas : Measurable S := by
        unfold S finsetRademacherSum
        fun_prop
      have hYmeas : Measurable Y := by
        unfold Y
        fun_prop
      have hSindY : S ⟂ᵢ[μ] Y := by
        let Z : ι → Ω → ℝ := fun j ω => a j * ε j ω
        have hZind : iIndepFun Z μ :=
          hindep.comp (fun j x => a j * x) (fun _ => by fun_prop)
        simpa [S, Y, Z, finsetRademacherSum] using
          hZind.indepFun_finsetSum_of_notMem (fun j => by fun_prop) hi
      have hSbound := ae_abs_finsetRademacherSum_le (a := a) hε s
      have hYbound : ∀ᵐ ω ∂μ, |Y ω| ≤ |a i| := by
        filter_upwards [(hε i).2.1] with ω hω
        rcases hω with hneg | hpos <;> simp [Y, hneg, hpos]
      have hSmean : (∫ ω, S ω ∂μ) = 0 := by
        simpa [S] using integral_finsetRademacherSum_eq_zero (a := a) hε s
      have hYmean : (∫ ω, Y ω ∂μ) = 0 := by
        simpa [Y] using integral_mul_rademacher_eq_zero (ε i) (a i) (hε i)
      have hformula := integral_add_pow_four_of_indep_centered
        hSmeas hYmeas hSindY (by positivity) (abs_nonneg (a i))
        hSbound hYbound hSmean hYmean
      have hS2 := integral_sq_finsetRademacherSum (a := a) hε hindep s
      have hYmem : MemLp Y 2 μ := by
        simpa [Y] using memLp_of_bounded
          (mul_rademacher_mem_Icc (ε i) (a i) (hε i))
          (hε i).1.aestronglyMeasurable.const_mul 2
      have hY2 : (∫ ω, Y ω ^ 2 ∂μ) = a i ^ 2 := by
        rw [← variance_of_integral_eq_zero hYmem.aemeasurable hYmean]
        simpa [Y] using variance_mul_rademacher (ε i) (a i) (hε i)
      have hY4 := integral_pow_four_mul_rademacher (a := a) i (hε i)
      calc
        (∫ ω, finsetRademacherSum (insert i s) ε a ω ^ 4 ∂μ)
            = (∫ ω, (S ω + Y ω) ^ 4 ∂μ) := by
                apply integral_congr_ae
                filter_upwards with ω
                simp [S, Y, finsetRademacherSum, Finset.sum_insert hi, add_comm]
        _ = (∫ ω, S ω ^ 4 ∂μ) +
              6 * (∫ ω, S ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
              ∫ ω, Y ω ^ 4 ∂μ := hformula
        _ ≤ 3 * (∑ j ∈ s, a j ^ 2) ^ 2 +
              6 * (∑ j ∈ s, a j ^ 2) * a i ^ 2 + a i ^ 4 := by
                rw [hS2, hY2, hY4]
                gcongr
        _ ≤ 3 * (∑ j ∈ insert i s, a j ^ 2) ^ 2 := by
              rw [Finset.sum_insert hi]
              nlinarith [sq_nonneg (a i ^ 2)]

end FiniteWeightedSums

section FinWeightedSums

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}

/-- Fourth moment bound for the chapter's `Fin n` weighted sum. -/
theorem integral_pow_four_rademacherWeightedSum_le
    (ε : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hε : IsRademacherFamily μ ε) :
    (∫ ω, rademacherWeightedSum ε a ω ^ 4 ∂μ) ≤
      3 * (∑ i, a i ^ 2) ^ 2 := by
  simpa [rademacherWeightedSum, finsetRademacherSum] using
    integral_pow_four_finsetRademacherSum_le
      (a := a) hε.1 hε.2 (Finset.univ : Finset (Fin n))

end FinWeightedSums

end Chapter03
end InfiniteDimensionalStatistics
