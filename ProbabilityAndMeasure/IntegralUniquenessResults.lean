import ProbabilityAndMeasure.DistributionTailResults
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Probability and Measure: integral identities and uniqueness

Source-numbered declarations for the basic integral properties and the pi-system uniqueness
argument.  The latter is proved by an explicit Dynkin-system induction.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory MeasurableSpace

namespace ProbabilityAndMeasure

/-- Source 69, lines 1761--1768: linearity, monotonicity, and definiteness of the
non-negative Lebesgue integral. -/
theorem source069_lintegral_properties {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∀ a b : ℝ≥0∞,
      (∫⁻ x, a * f x + b * g x ∂μ) =
        a * (∫⁻ x, f x ∂μ) + b * (∫⁻ x, g x ∂μ)) ∧
    ((∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧
    (f =ᵐ[μ] 0 ↔ (∫⁻ x, f x ∂μ) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rw [lintegral_add_left (measurable_const.mul hf),
      lintegral_const_mul a hf, lintegral_const_mul b hg]
  · intro hfg
    exact lintegral_mono hfg
  · exact (lintegral_eq_zero_iff hf).symm

/-- Source 70, lines 1817--1824: linearity, monotonicity, and invariance under a.e.
equality for integrable real functions.  The linearity statement is strengthened to arbitrary
real coefficients. -/
theorem source070_integral_properties {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ a b : ℝ,
      (∫ x, a * f x + b * g x ∂μ) =
        a * (∫ x, f x ∂μ) + b * (∫ x, g x ∂μ)) ∧
    ((∀ x, f x ≤ g x) → (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ) ∧
    (f =ᵐ[μ] 0 → (∫ x, f x ∂μ) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simpa only [Pi.smul_apply, smul_eq_mul] using
      integral_add (hf.smul a) (hg.smul b)
  · intro hfg
    exact integral_mono_ae hf hg (ae_of_all μ hfg)
  · intro hzero
    exact integral_eq_zero_of_ae hzero

/-- Source 71, lines 1865--1871: if the set integral of an integrable function vanishes
on a generating pi-system containing the whole space, then the function vanishes almost
everywhere. -/
theorem source071_ae_eq_zero_of_piSystem_setIntegral_zero
    {α : Type*} [mα : MeasurableSpace α] (μ : Measure α)
    (C : Set (Set α)) (hgen : mα = MeasurableSpace.generateFrom C)
    (hC : IsPiSystem C) (huniv : Set.univ ∈ C)
    (f : α → ℝ) (hf : Integrable f μ)
    (hzero : ∀ A ∈ C, ∫ x in A, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  have htotal : ∫ x, f x ∂μ = 0 := by
    simpa only [setIntegral_univ] using hzero Set.univ huniv
  have hall : ∀ A : Set α, MeasurableSet A → ∫ x in A, f x ∂μ = 0 := by
    intro A hA
    refine MeasurableSpace.induction_on_inter hgen hC ?_ ?_ ?_ ?_ A hA
    · simp
    · intro B hB
      exact hzero B hB
    · intro B hBm hBzero
      simpa [hBzero, htotal] using integral_add_compl hBm hf
    · intro B hdis hBm hBzero
      rw [integral_iUnion hBm hdis hf.integrableOn]
      simp [hBzero]
  exact hf.ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ ↦ hall A hA

end ProbabilityAndMeasure
