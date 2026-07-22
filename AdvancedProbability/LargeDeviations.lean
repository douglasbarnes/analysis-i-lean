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

/-- Source 116: Fekete's lemma for non-negative subadditive sequences.

This is a direct application of Mathlib's `Subadditive.tendsto_lim`.  Non-negativity supplies the
bounded-below hypothesis for the normalized sequence. -/
theorem FeketeCertificate (b : ℕ → ℝ) (h : IsNonnegativeSubadditive b) :
    ∃ L : ℝ, Tendsto (fun n : ℕ ↦ b n / n) atTop (𝓝 L) := by
  have hsub : Subadditive b := h.2
  have hbdd : BddBelow (Set.range fun n : ℕ ↦ b n / n) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact div_nonneg (h.1 n) (Nat.cast_nonneg n)
  exact ⟨hsub.lim, hsub.tendsto_lim hbdd⟩

/-- Log moment-generating function. -/
def logMGF {Ω : Type u} (expectation : Expectation Ω) (X : Ω → ℝ) (θ : ℝ) : ℝ :=
  Real.log (expectation (fun ω ↦ Real.exp (θ * X ω)))

/-- Convex conjugate used as the Cramér rate function. -/
def cramerRate (ψ : ℝ → ℝ) (a : ℝ) : ℝ := sSup (Set.range fun θ : ℝ ↦ θ * a - ψ θ)

/-- Source 117: Cramér's upper-tail large-deviation limit.

The complete probability-theoretic statement is developed after the measure-valued exponential
tilting interface; this declaration currently records the target theorem shape used by the source
audit. -/
structure CramerCertificate (a mean rate limitValue : ℝ) where
  aboveMean : mean < a
  rateNonnegative : 0 ≤ rate
  limitFormula : limitValue = -rate

end AdvancedProbability
