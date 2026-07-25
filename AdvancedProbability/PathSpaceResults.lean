import AdvancedProbability.ContinuousTime

noncomputable section

open scoped NNReal

namespace AdvancedProbability

/-- The source-56 path space is canonically equivalent to Mathlib's bundled continuous-map type. -/
def continuousPathSpaceEquiv : ContinuousPathSpace ≃ ContinuousMap ℝ≥0 ℝ where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f, f.continuous⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- The canonical coordinate process on continuous path space. -/
def canonicalPathProcess : ContinuousProcess ContinuousPathSpace :=
  fun t ω ↦ ω.1 t

/-- Every sample path of the canonical coordinate process is continuous. -/
theorem canonicalPathProcess_isContinuous : IsContinuousProcess canonicalPathProcess :=
  fun ω ↦ ω.2

@[simp] theorem canonicalPathProcess_apply (t : ℝ≥0) (ω : ContinuousPathSpace) :
    canonicalPathProcess t ω = ω.1 t :=
  rfl

end AdvancedProbability