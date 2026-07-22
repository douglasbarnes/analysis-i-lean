import ProbabilityAndMeasure.ProbabilityResults
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Probability and Measure: product measures and Fubini
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- Source lines 2250--2256 and 2311--2316: the product measure takes a measurable
rectangle to the product of the factor measures. -/
theorem product_measure_rectangle_source {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (A : Set α) (B : Set β) :
    (μ.prod ν) (A ×ˢ B) = μ A * ν B :=
  MeasureTheory.Measure.prod_prod A B

/-- Source lines 2267--2274: measurable functions on a product have measurable fixed
sections. -/
theorem measurable_product_section_source {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
    {f : α × β → E} (hf : Measurable f) (x : α) :
    Measurable (fun y ↦ f (x, y)) :=
  hf.comp measurable_prodMk_left

/-- The symmetric fixed-section statement. -/
theorem measurable_product_section_symm_source {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
    {f : α × β → E} (hf : Measurable f) (y : β) :
    Measurable (fun x ↦ f (x, y)) :=
  hf.comp measurable_prodMk_right

/-- Source lines 2357--2368, Fubini's theorem in Bochner-integral form. -/
theorem fubini_source {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  MeasureTheory.integral_prod f hf

/-- The order of two integrals can be exchanged under the Fubini integrability hypothesis. -/
theorem fubini_swap_source {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → β → E} (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  MeasureTheory.integral_integral_swap hf

end ProbabilityAndMeasure
