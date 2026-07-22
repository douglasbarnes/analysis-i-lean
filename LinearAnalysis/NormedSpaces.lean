import Mathlib
import AnalysisI
import AnalysisII
import MetricTopologicalSpaces
import LinearAlgebraCourse

/-!
# Linear Analysis: normed spaces and duality

Course-facing declarations for the first chapter of `II_M/linear_analysis.tex`.
The foundational material from Analysis I/II, Linear Algebra, and Metric and Topological Spaces is
imported; standard functional-analytic theorems are discharged by their Mathlib implementations.
-/

noncomputable section

open Set Function Topology Bornology
open scoped Topology NNReal

namespace Cambridge.LinearAnalysis

abbrev BoundedLinearMap (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] := E →L[𝕜] F

abbrev ContinuousDual (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] := StrongDual 𝕜 E

abbrev DoubleDual (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] := StrongDual 𝕜 (StrongDual 𝕜 E)

/-- The course definition of an absolutely convex set. -/
abbrev AbsolutelyConvex (𝕜 : Type*) {E : Type*} [SeminormedRing 𝕜]
    [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E] (s : Set E) : Prop := AbsConvex 𝕜 s

/-- Addition is continuous in every normed additive group. -/
theorem normed_addition_continuous {E : Type*} [SeminormedAddCommGroup E] :
    Continuous (fun p : E × E ↦ p.1 + p.2) :=
  continuous_fst.add continuous_snd

/-- Scalar multiplication is continuous in every normed space over a normed field. -/
theorem normed_scalar_multiplication_continuous {𝕜 E : Type*}
    [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Continuous (fun p : 𝕜 × E ↦ p.1 • p.2) :=
  continuous_fst.smul continuous_snd

/-- Norm balls centred at zero are absolutely convex over `ℝ`. -/
theorem real_ball_absolutelyConvex {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) : AbsConvex ℝ (Metric.ball (0 : E) r) :=
  ⟨balanced_ball_zero, convex_ball 0 r⟩

/-- The topological and bornological definition of a bounded subset agrees with Mathlib's
bornological boundedness on normed spaces. -/
abbrev IsBoundedSubset {E : Type*} [PseudoMetricSpace E] [Bornology E]
    (s : Set E) : Prop := Bornology.IsBounded s

/-- The operator norm controls every value of a bounded linear map. -/
theorem apply_norm_le_operator_norm {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.le_opNorm x

/-- A linear map is continuous exactly when it admits a global norm bound. -/
theorem linearMap_continuous_iff_bounded {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →ₗ[𝕜] F) :
    Continuous T ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hT
    obtain ⟨C, hC, hbound⟩ := SemilinearMapClass.bound_of_continuous T hT
    exact ⟨C, hC.le, hbound⟩
  · rintro ⟨C, _, hbound⟩
    exact (T.mkContinuous C hbound).continuous

/-- Continuous duals are Banach spaces, even when the original space is incomplete. -/
theorem dual_is_complete {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    CompleteSpace (StrongDual 𝕜 E) := inferInstance

/-- The dual (transpose) action of a bounded linear map. -/
def dualAction {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (g : StrongDual 𝕜 F) : StrongDual 𝕜 E :=
  g.comp T

@[simp] theorem dualAction_apply {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (g : StrongDual 𝕜 F) (x : E) :
    dualAction T g x = g (T x) := rfl

/-- The dual action is bounded by the product of operator norms. -/
theorem dualAction_norm_le {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (g : StrongDual 𝕜 F) :
    ‖dualAction T g‖ ≤ ‖g‖ * ‖T‖ :=
  ContinuousLinearMap.opNorm_comp_le g T

/-- Canonical evaluation embedding into the bidual. -/
abbrev canonicalEmbedding (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  NormedSpace.inclusionInDoubleDual 𝕜 E

@[simp] theorem canonicalEmbedding_apply {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : E) (f : StrongDual 𝕜 E) :
    canonicalEmbedding 𝕜 E x f = f x := rfl

/-- The canonical bidual embedding has operator norm at most one. -/
theorem canonicalEmbedding_norm_le {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    ‖canonicalEmbedding 𝕜 E‖ ≤ 1 :=
  NormedSpace.inclusionInDoubleDual_norm_le 𝕜 E

/-- Hahn--Banach: a continuous functional on a subspace extends without increasing its norm. -/
theorem hahnBanach_extension {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f

/-- Hahn--Banach supplies a norming functional at every nonzero vector. -/
theorem exists_norming_functional {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : E) (hx : x ≠ 0) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ = 1 ∧ f x = ‖x‖ :=
  exists_dual_vector 𝕜 x (by simpa only [norm_ne_zero_iff] using hx)

/-- Continuous functionals separate points. -/
theorem dual_separates_points {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x y : E} (hxy : x ≠ y) :
    ∃ f : StrongDual 𝕜 E, f x ≠ f y := by
  by_contra h
  push Not at h
  exact hxy ((SeparatingDual.eq_iff_forall_dual_eq).2 h)

/-- The canonical map into the bidual is an isometry. -/
theorem canonicalEmbedding_norm_eq {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖canonicalEmbedding 𝕜 E x‖ = ‖x‖ :=
  (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).norm_map x

/-- Reflexivity, expressed as surjectivity of the canonical bidual embedding. -/
def IsReflexive (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  Surjective (canonicalEmbedding 𝕜 E)

/-- Finite-dimensional normed spaces are complete. -/
theorem finiteDimensional_complete {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

/-- Every linear map out of a finite-dimensional normed space is continuous. -/
noncomputable def finiteDimensional_toContinuousLinearMap {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] F) : E →L[𝕜] F :=
  LinearMap.toContinuousLinearMap T

end Cambridge.LinearAnalysis
