import ProbabilityAndMeasure.ProductAndFubiniResults
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Probability and Measure: inequalities and `Lᵖ`
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- Source lines 2544--2549, Jensen's inequality for a probability measure. -/
theorem jensen_source {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Set E} {X : Ω → E} {c : E → ℝ}
    (hc : ConvexOn ℝ s c) (hcc : ContinuousOn c s) (hs : IsClosed s)
    (hXs : ∀ᵐ ω ∂P, X ω ∈ s) (hX : Integrable X P)
    (hcX : Integrable (c ∘ X) P) :
    c (∫ ω, X ω ∂P) ≤ ∫ ω, c (X ω) ∂P :=
  hc.map_integral_le hcc hs hXs hX hcX

/-- Source lines 2644--2650, Hölder's inequality for non-negative extended-real
functions. -/
theorem holder_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  simpa only [Pi.mul_apply] using ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg

/-- Source lines 2712--2717, Minkowski's inequality for the `Lᵖ` seminorm. -/
theorem minkowski_eLpNorm_source {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 ≤ p) :
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ :=
  MeasureTheory.eLpNorm_add_le hf hg hp

/-- Source lines 2800--2802: Mathlib's `Lᵖ` space is complete for `1 ≤ p`. -/
theorem lp_complete_source {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) :
    CompleteSpace (MeasureTheory.Lp E p μ) := by
  infer_instance

/-- Source lines 2863--2866: real `L²` is a complete inner-product space. -/
theorem l2_complete_source {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    CompleteSpace (MeasureTheory.Lp ℝ 2 μ) := by
  infer_instance

end ProbabilityAndMeasure
