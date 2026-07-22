import ProbabilityAndMeasure.MeasurabilityConvergenceResults
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Probability and Measure: measurable limits, Stieltjes measures, and tail events

Further source-numbered declarations from the measurable-functions and probability chapters.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory MeasurableSpace
open ProbabilityTheory

namespace ProbabilityAndMeasure

/-- Source 41, lines 891--898: the elementary arithmetic, lattice, and sequential limit
operations on non-negative measurable functions are measurable. -/
theorem source041_measurable_operations {E : Type*} [MeasurableSpace E]
    (f : ℕ → E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x ↦ f 0 x + f 1 x) ∧
      Measurable (fun x ↦ f 0 x * f 1 x) ∧
      Measurable (fun x ↦ max (f 0 x) (f 1 x)) ∧
      Measurable (fun x ↦ min (f 0 x) (f 1 x)) ∧
      Measurable (fun x ↦ ⨅ n, f n x) ∧
      Measurable (fun x ↦ ⨆ n, f n x) ∧
      Measurable (fun x ↦ liminf (fun n ↦ f n x) atTop) ∧
      Measurable (fun x ↦ limsup (fun n ↦ f n x) atTop) := by
  exact ⟨(hf 0).add (hf 1), (hf 0).mul (hf 1), (hf 0).max (hf 1),
    (hf 0).min (hf 1), Measurable.iInf hf, Measurable.iSup hf,
    Measurable.liminf hf, Measurable.limsup hf⟩

/-- Source 46, lines 1041--1047: the Stieltjes measure associated with a monotone
right-continuous function has the prescribed masses on half-open intervals and is locally finite. -/
theorem source046_stieltjes_measure_exists (F : StieltjesFunction ℝ) :
    IsLocallyFiniteMeasure F.measure ∧
      ∀ a b : ℝ, F.measure (Set.Ioc a b) = ENNReal.ofReal (F b - F a) := by
  exact ⟨inferInstance, F.measure_Ioc⟩

/-- Source 46, uniqueness clause: a locally finite Borel measure with the prescribed values
on all half-open intervals is the Stieltjes measure of `F`. -/
theorem source046_stieltjes_measure_unique (F : StieltjesFunction ℝ)
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ ⦃a b : ℝ⦄, a < b →
      μ (Set.Ioc a b) = ENNReal.ofReal (F b - F a)) :
    μ = F.measure := by
  apply MeasureTheory.Measure.ext_of_Ioc μ F.measure
  intro a b hab
  exact (hμ hab).trans (F.measure_Ioc a b).symm

/-- Source 62, first clause: Kolmogorov's zero-one law for an independent sequence of
sub-sigma-algebras. -/
theorem source062_kolmogorov_zero_one {Ω : Type*} [m0 : MeasurableSpace Ω]
    (s : ℕ → MeasurableSpace Ω) (P : Measure Ω)
    (h_le : ∀ n, s n ≤ m0) (h_indep : ProbabilityTheory.iIndep s P)
    {A : Set Ω} (hA : MeasurableSet[limsup s atTop] A) :
    P A = 0 ∨ P A = 1 :=
  ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep hA

/-- Source 62, second clause: every real-valued random variable measurable with respect to
the tail sigma-algebra is almost surely constant. -/
theorem source062_tail_measurable_ae_constant {Ω : Type*} [m0 : MeasurableSpace Ω]
    (s : ℕ → MeasurableSpace Ω) (P : Measure Ω)
    (h_le : ∀ n, s n ≤ m0) (h_indep : ProbabilityTheory.iIndep s P)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ (limsup s atTop) (borel ℝ) X) :
    ∃ c : ℝ, X =ᵐ[P] Function.const Ω c := by
  classical
  letI : IsProbabilityMeasure P := h_indep.isProbabilityMeasure
  have htail_le : limsup s atTop ≤ m0 := limsup_le_iSup.trans (iSup_le h_le)
  refine Filter.exists_eventuallyEq_const_of_forall_separating (l := ae P) MeasurableSet ?_
  intro U hU
  have hpre_tail : MeasurableSet[limsup s atTop] (X ⁻¹' U) := hX hU
  have hpre : MeasurableSet (X ⁻¹' U) := htail_le _ hpre_tail
  rcases ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
      h_le h_indep hpre_tail with h0 | h1
  · refine Or.inr ?_
    apply ae_iff.2
    change P (X ⁻¹' U) = 0
    exact h0
  · refine Or.inl ?_
    apply ae_iff.2
    change P (X ⁻¹' U)ᶜ = 0
    rw [MeasureTheory.prob_compl_eq_one_sub hpre, h1, tsub_self]

end ProbabilityAndMeasure
