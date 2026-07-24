module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Covariance

/-!
# Basic real Brownian motion on the pinned Mathlib revision

A pre-Brownian process is represented by the standard equivalent characterization: it is a centred
Gaussian process whose covariance is `min s t`. A Brownian process is a pre-Brownian process with
almost-surely continuous paths. The elementary invariance and weak Markov results are proved from
this characterization.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownianReal

/-- A centred real Gaussian process with Brownian covariance. -/
structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  gaussian : IsGaussianProcess X P
  centered : ∀ t, P[X t] = 0
  covariance_of_le : ∀ s t, s ≤ t → cov[fun ω ↦ X s ω, fun ω ↦ X t ω; P] = s

lemma IsPreBrownianReal.isGaussianProcess (hB : IsPreBrownianReal B P) :
    IsGaussianProcess B P := hB.gaussian

lemma IsPreBrownianReal.aemeasurable (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    AEMeasurable (B t) P := hB.gaussian.aemeasurable t

lemma IsPreBrownianReal.integral_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    P[B t] = 0 := hB.centered t

lemma IsPreBrownianReal.integrable_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Integrable (B t) P := hB.gaussian.hasGaussianLaw_eval t |>.integrable

lemma IsPreBrownianReal.covariance_fun_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[fun ω ↦ B s ω, fun ω ↦ B t ω; P] = min s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [covariance_comm, this t s (le_of_not_ge hst), min_comm]
  rw [hB.covariance_of_le s t hst, min_eq_left hst]

lemma IsPreBrownianReal.covariance_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = min s t := hB.covariance_fun_eval s t

/-- A pre-Brownian motion has independent increments. -/
lemma IsPreBrownianReal.hasIndepIncrements (hB : IsPreBrownianReal B P) :
    HasIndepIncrements B P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht ↦ hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij ↦ ?_
  rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
  · simp_rw [hB.covariance_fun_eval]
    wlog h : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by grind), min_comm]
      grind
    have h1 : i.succ ≤ j.succ := Fin.strictMono_succ h |>.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  any_goals exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

lemma IsPreBrownianReal.neg (hB : IsPreBrownianReal B P) : IsPreBrownianReal (-B) P where
  gaussian := by
    simpa [Pi.neg_def] using hB.isGaussianProcess.smul (fun _ ↦ (-1 : ℝ))
  centered := by
    intro t
    change ∫ ω, -B t ω ∂P = 0
    rw [integral_neg, hB.integral_eval, neg_zero]
  covariance_of_le := by
    intro s t hst
    change cov[fun ω ↦ -B s ω, fun ω ↦ -B t ω; P] = s
    simp only [covariance_fun_neg_left, covariance_fun_neg_right, neg_neg]
    exact hB.covariance_of_le s t hst

/-- Brownian scaling for pre-Brownian motion. -/
lemma IsPreBrownianReal.smul (hB : IsPreBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P where
  gaussian := by
    have hpoint t ω : (√c)⁻¹ * B (c * t) ω = (√c)⁻¹ • ((B ∘ (c * ·)) t ω) := rfl
    simp_rw [hpoint]
    exact (hB.isGaussianProcess.comp_right _).smul _
  centered := by
    intro t
    rw [integral_const_mul, hB.integral_eval, mul_zero]
  covariance_of_le := by
    intro s t hst
    rw [covariance_const_mul_left, covariance_const_mul_right,
      hB.covariance_of_le (c * s) (c * t) (mul_le_mul_right hst c)]
    simp [field]

/-- Deterministic time shifts preserve pre-Brownian motion. -/
lemma IsPreBrownianReal.shift (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IsPreBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P where
  gaussian := hB.isGaussianProcess.shift t₀
  centered := by
    intro t
    rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  covariance_of_le := by
    intro s t hst
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/-- Future increments are independent of all coordinates up to the shift time. -/
lemma IsPreBrownianReal.indepFun_shift (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ B (t₀ + t) ω - B t₀ ω) (fun ω (t : Set.Iic t₀) ↦ B t ω) P := by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{t},
        { toFun x := x ⟨t, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  any_goals fun_prop
  · rintro s ⟨t, ht : t ≤ t₀⟩
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, hB.covariance_eval, hB.covariance_eval, min_eq_right, min_eq_right,
      sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- Time inversion preserves Brownian finite-dimensional Gaussian data. -/
lemma IsPreBrownianReal.inv (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ t * B (1 / t) ω) P where
  gaussian := (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  centered := by
    intro t
    rw [integral_const_mul, hB.integral_eval, mul_zero]
  covariance_of_le := by
    intro s t hst
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have ht : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

end IsPreBrownianReal

section IsBrownianReal

/-- A Brownian process is a pre-Brownian process with almost-surely continuous paths. -/
structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianReal X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

lemma IsBrownianReal.neg (hB : IsBrownianReal B P) : IsBrownianReal (-B) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.neg
  cont := hB.cont.mono (fun _ _ ↦ by simpa [← Pi.neg_def, continuous_neg_iff])

/-- Brownian scaling preserves Brownian motion. -/
lemma IsBrownianReal.smul (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

lemma IsBrownianReal.shift (hB : IsBrownianReal B P) (t₀ : ℝ≥0) :
    IsBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

end IsBrownianReal

end ProbabilityTheory
