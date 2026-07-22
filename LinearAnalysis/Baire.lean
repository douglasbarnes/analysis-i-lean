import LinearAnalysis.NormedSpaces

/-!
# Linear Analysis: Baire-category methods

The Baire category theorem and its principal functional-analytic consequences: uniform boundedness,
open mapping, inverse mapping, and closed graph.
-/

noncomputable section

open Set Function Topology Filter

namespace Cambridge.LinearAnalysis

/-- Course terminology: a nowhere-dense set. -/
abbrev IsNowhereDense {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsNowhereDense s

/-- Course terminology: a meagre (first-category) set. -/
abbrev IsMeagreSet {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsMeagre s

/-- Course terminology: a residual set. -/
def IsResidual {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsMeagre sᶜ

/-- Every complete metric space is a Baire space. -/
theorem completeMetric_baire {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] :
    BaireSpace X := inferInstance

/-- Banach--Steinhaus (uniform boundedness principle). -/
theorem uniform_boundedness {ι 𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : ι → E →L[𝕜] F)
    (hT : ∀ x, ∃ C : ℝ, ∀ i, ‖T i x‖ ≤ C) :
    ∃ C : ℝ, ∀ i, ‖T i‖ ≤ C :=
  banach_steinhaus hT

/-- Banach's open mapping theorem. -/
theorem open_mapping {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : Surjective T) : IsOpenMap T :=
  T.isOpenMap hT

/-- Banach's inverse mapping theorem, packaged as a continuous linear equivalence. -/
noncomputable def inverse_mapping {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : Bijective T) : E ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hT.1) (LinearMap.range_eq_top.mpr hT.2)

@[simp] theorem inverse_mapping_apply {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : Bijective T) (x : E) :
    inverse_mapping T hT x = T x := rfl

/-- Closed graph theorem: a linear map between Banach spaces with closed graph is continuous. -/
noncomputable def continuousLinearMap_of_closedGraph {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →ₗ[𝕜] F) (hT : IsClosed T.graph) : E →L[𝕜] F :=
  ContinuousLinearMap.ofIsClosedGraph hT

@[simp] theorem continuousLinearMap_of_closedGraph_apply {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →ₗ[𝕜] F) (hT : IsClosed T.graph) (x : E) :
    continuousLinearMap_of_closedGraph T hT x = T x := rfl

end Cambridge.LinearAnalysis
