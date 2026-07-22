import LinearAnalysis.HilbertSpaces

/-!
# Linear Analysis: bounded and compact operators

Spectrum and resolvent, compact operators, self-adjointness, eigenspaces, and the spectral theorem
for compact self-adjoint operators.
-/

noncomputable section

open Set Function Topology Filter
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Cambridge.LinearAnalysis

/-- Spectrum of a bounded complex-linear operator. -/
def operatorSpectrum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) : Set ℂ :=
  spectrum ℂ T

/-- Resolvent set of a bounded complex-linear operator. -/
def operatorResolventSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) : Set ℂ :=
  resolventSet ℂ T

/-- Point spectrum, expressed through nontrivial eigenspaces. -/
def pointSpectrum {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (T : E →ₗ[𝕜] E) : Set 𝕜 :=
  {μ | Module.End.HasEigenvalue T μ}

/-- Approximate point spectrum: unit approximate eigenvectors. -/
def approximatePointSpectrum {𝕜 E : Type*} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E →L[𝕜] E) : Set 𝕜 :=
  {μ | ∃ u : ℕ → E, (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n ↦ T (u n) - μ • u n) atTop (𝓝 0)}

/-- Compactness of a bounded operator. -/
abbrev IsCompactLinearOperator {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) : Prop :=
  IsCompactOperator T

/-- Self-adjointness in the inner-product formulation used by the notes. -/
abbrev IsSelfAdjoint {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (T : E →L[𝕜] E) : Prop :=
  (T : E →ₗ[𝕜] E).IsSymmetric

/-- The resolvent set is open. -/
theorem operatorResolventSet_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : E →L[ℂ] E) :
    IsOpen (operatorResolventSet T) :=
  spectrum.isOpen_resolventSet T

/-- The spectrum is closed. -/
theorem operatorSpectrum_isClosed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : E →L[ℂ] E) :
    IsClosed (operatorSpectrum T) :=
  spectrum.isClosed T

/-- Spectral values lie in the closed disk of radius `‖T‖`. -/
theorem operatorSpectrum_subset_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E] (T : E →L[ℂ] E) :
    operatorSpectrum T ⊆ Metric.closedBall 0 ‖T‖ :=
  spectrum.subset_closedBall_norm T

/-- Characterisation of compact operators by compactness of the closure of the image of a ball. -/
theorem compact_iff_compact_closure_image_ball {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) :
    IsCompactOperator T ↔
      IsCompact (closure (T '' Metric.ball (0 : E) 1)) := by
  simpa using isCompactOperator_iff_isCompact_closure_image_ball T.toLinearMap
    (show (0 : ℝ) < 1 by norm_num)

/-- Precomposition by a bounded operator preserves compactness. -/
theorem compact_comp_right {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : F →L[𝕜] G} (hT : IsCompactOperator T) (S : E →L[𝕜] F) :
    IsCompactOperator (T.comp S) :=
  hT.comp_clm S

/-- Postcomposition by a bounded operator preserves compactness. -/
theorem compact_comp_left {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : E →L[𝕜] F} (hT : IsCompactOperator T) (S : F →L[𝕜] G) :
    IsCompactOperator (S.comp T) :=
  hT.clm_comp S

/-- Eigenvalues of a self-adjoint operator are fixed by conjugation, hence real. -/
theorem selfAdjoint_eigenvalue_real {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ) :
    star μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

/-- Eigenspaces belonging to distinct eigenvalues of a self-adjoint operator are orthogonal. -/
theorem selfAdjoint_orthogonal_eigenspaces {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    OrthogonalFamily 𝕜
      (fun μ : 𝕜 ↦ Module.End.eigenspace (T : E →ₗ[𝕜] E) μ)
      (fun μ ↦ (Module.End.eigenspace (T : E →ₗ[𝕜] E) μ).subtypeₗᵢ) :=
  hT.orthogonalFamily_eigenspaces

/-- Nonzero eigenspaces of compact operators are finite-dimensional. -/
theorem compact_finiteDimensional_eigenspace {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (T : E →ₗ[𝕜] E) μ) :=
  T.finite_dimensional_eigenspace hT μ hμ

/-- Spectral theorem for compact self-adjoint operators: the closed span of all eigenspaces is the
whole Hilbert space, expressed by triviality of its orthogonal complement. -/
theorem compact_selfAdjoint_spectral_theorem {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    (⨆ μ : 𝕜, Module.End.eigenspace (T : E →ₗ[𝕜] E) μ)ᗮ = ⊥ :=
  T.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hself

end Cambridge.LinearAnalysis
