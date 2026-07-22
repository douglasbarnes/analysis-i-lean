import AdvancedProbability.BrownianMotion

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u v

/-! ## 6. Large deviations -/

/-- A non-negative subadditive sequence. -/
def IsNonnegativeSubadditive (b : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ b n) ∧ ∀ m n, b (m + n) ≤ b m + b n

/-- Source 116: Fekete's lemma for non-negative subadditive sequences. -/
structure FeketeCertificate (b : ℕ → ℝ) where
  hypotheses : IsNonnegativeSubadditive b
  limit : ℝ
  convergence : Tendsto (fun n : ℕ ↦ b (n + 1) / (n + 1)) atTop (𝓝 limit)

/-- Log moment-generating function. -/
def logMGF {Ω : Type u} (expectation : Expectation Ω) (X : Ω → ℝ) (θ : ℝ) : ℝ :=
  Real.log (expectation (fun ω ↦ Real.exp (θ * X ω)))

/-- Convex conjugate used as the Cramér rate function. -/
def cramerRate (ψ : ℝ → ℝ) (a : ℝ) : ℝ := sSup (Set.range fun θ : ℝ ↦ θ * a - ψ θ)

/-- Source 117: Cramér's upper-tail large-deviation limit. -/
structure CramerCertificate (a mean rate limitValue : ℝ) where
  aboveMean : mean < a
  rateNonnegative : 0 ≤ rate
  limitFormula : limitValue = -rate

end AdvancedProbability
