import Mathlib

open Filter Function Set Topology
open scoped Topology ContDiff

namespace AnalysisII

noncomputable section

/-- Analysis II source 64, in its intrinsic Fréchet form: on an open set, a map is
`C¹` iff it is differentiable and its Fréchet derivative is continuous.  For
finite-dimensional Euclidean spaces this is equivalent to the coordinate-partial
formulation in the notes. -/
theorem source064_c1_iff_differentiable_continuous_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} :
    ContDiffOn ℝ 1 f U ↔
      DifferentiableOn ℝ f U ∧ ContinuousOn (fderiv ℝ f) U := by
  simpa using
    (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (f := f) (s := U)
      (n := (0 : ℕ∞ω)) hU)

/-- Analysis II source 66: the second Fréchet derivative of a `C²` real map is
symmetric.  This is the basis-free form of equality of mixed partials. -/
theorem source066_mixed_partials_symmetric
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {a : E} (hf : ContDiffAt ℝ 2 f a) :
    IsSymmSndFDerivAt ℝ f a :=
  hf.isSymmSndFDerivAt (by norm_num)

/-- Analysis II source 67: a `C²` map has a Fréchet derivative which is
differentiable; its derivative is a symmetric continuous bilinear map. -/
theorem source067_second_derivative_exists_symmetric
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {a : E} (hf : ContDiffAt ℝ 2 f a) :
    ∃ B : E →L[ℝ] E →L[ℝ] F,
      HasFDerivAt (fderiv ℝ f) B a ∧ ∀ u v, B u v = B v u := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) a := by
    apply ContDiffAt.differentiableAt _ one_ne_zero
    exact hf.fderiv_right (by norm_num)
  let B : E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ f) a
  refine ⟨B, hdiff.hasFDerivAt, ?_⟩
  intro u v
  exact (source066_mixed_partials_symmetric hf) u v

/-- The second derivative applied to two vectors is bilinear in the two
arguments; this is the coordinate-free content of the source 67 summation
formula. -/
theorem source067_second_derivative_bilinear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] E →L[ℝ] F) (u₁ u₂ v : E) (a b : ℝ) :
    B (a • u₁ + b • u₂) v = a • B u₁ v + b • B u₂ v ∧
      B v (a • u₁ + b • u₂) = a • B v u₁ + b • B v u₂ := by
  constructor <;> simp

end

end AnalysisII
