import Mathlib

open Filter Function Set Topology
open scoped Topology

namespace AnalysisII

noncomputable section

/-- Analysis II source 60: the vector-valued one-dimensional mean value inequality. -/
theorem source060_interval_mean_value_inequality
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : ℝ → ℝ →L[ℝ] F} {a b M : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasFDerivWithinAt f (f' x) (Icc a b) x)
    (hM : ∀ x ∈ Icc a b, ‖f' x‖ ≤ M) :
    ‖f b - f a‖ ≤ M * (b - a) := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hf hM (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- Analysis II source 61: mean value inequality on a convex domain. -/
theorem source061_convex_mean_value_inequality
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} {M : ℝ}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hM : ∀ x ∈ s, ‖f' x‖ ≤ M)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x‖ ≤ M * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hM hx hy

/-- Analysis II source 62: a differentiable map with zero derivative on a ball
is constant on that ball. -/
theorem source062_zero_derivative_on_ball_constant
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {a : E} {r : ℝ}
    (hf : DifferentiableOn ℝ f (Metric.ball a r))
    (hzero : ∀ x ∈ Metric.ball a r,
      fderivWithin ℝ f (Metric.ball a r) x = 0)
    {x y : E} (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) :
    f x = f y :=
  (convex_ball a r).is_const_of_fderivWithin_eq_zero hf hzero hx hy

/-- Analysis II source 63: zero derivative on an open path-connected set implies constancy. -/
theorem source063_zero_derivative_on_pathConnected_open_constant
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E}
    (hUopen : IsOpen U) (hUconn : IsPathConnected U)
    (hf : DifferentiableOn ℝ f U)
    (hzero : U.EqOn (fderiv ℝ f) 0)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) : f x = f y :=
  hUopen.is_const_of_fderiv_eq_zero hUconn.isPreconnected hf hzero hx hy

end

end AnalysisII
