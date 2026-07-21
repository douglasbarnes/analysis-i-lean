import Mathlib

open Filter Topology Set

namespace AnalysisI

/-- Source theorem 1, specialised to the real field. -/
theorem source001_sq_nonneg (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

/-- Source theorem 3. -/
theorem source003_one_div_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

/-- Source theorem 5. -/
theorem source005_tendsto_add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n => a n + b n) atTop (𝓝 (x + y)) :=
  ha.add hb

/-- Source theorem 9. -/
theorem source009_tendsto_mul {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n => a n * b n) atTop (𝓝 (x * y)) :=
  ha.mul hb

/-- Source theorem 17. -/
theorem source017_limit_unique {a : ℕ → ℝ} {x y : ℝ}
    (hx : Tendsto a atTop (𝓝 x)) (hy : Tendsto a atTop (𝓝 y)) : x = y :=
  tendsto_nhds_unique hx hy

/-- Source theorem 40. -/
theorem source040_continuous_comp {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf

/-- Source theorem 48. -/
theorem source048_heine_borel (a b : ℝ) : IsCompact (Icc a b) :=
  isCompact_Icc

/-- Source theorem 56. -/
theorem source056_differentiable_continuous {f : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x) : ContinuousAt f x :=
  hf.continuousAt

/-- Source theorem 66. -/
theorem source066_exp_derivative (z : ℂ) : HasDerivAt Complex.exp (Complex.exp z) z :=
  Complex.hasDerivAt_exp z

/-- Source theorem 68. -/
theorem source068_exp_add (z w : ℂ) : Complex.exp (z + w) = Complex.exp z * Complex.exp w :=
  Complex.exp_add z w

end AnalysisI
