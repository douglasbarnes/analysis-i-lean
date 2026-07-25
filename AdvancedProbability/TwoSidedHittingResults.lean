import AdvancedProbability.BrownianMotion

noncomputable section

namespace AdvancedProbability

/-- Source 115: the two-sided Brownian exit probability and mean exit time follow from the two
optional-stopping identities.

For an exit from `(-y, x)`, let `p` be the probability of exiting at `x`. Optional stopping for
Brownian motion gives `p*x - (1-p)*y = 0`; optional stopping for `B_t^2 - t` gives the second-moment
identity. These determine `p = y/(x+y)` and `E τ = x*y`. -/
theorem TwoSidedHittingFormulaTheorem
    (x y p expectedTime : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hmean : p * x - (1 - p) * y = 0)
    (hsecond : expectedTime = p * x ^ 2 + (1 - p) * y ^ 2) :
    p = y / (x + y) ∧ expectedTime = x * y := by
  have hxy_pos : 0 < x + y := add_pos hx hy
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy_pos
  have hp : p = y / (x + y) := by
    apply (eq_div_iff hxy_ne).2
    nlinarith [hmean]
  refine ⟨hp, ?_⟩
  rw [hsecond, hp]
  field_simp [hxy_ne]
  ring

end AdvancedProbability
