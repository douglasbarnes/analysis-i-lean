import LinearAnalysis.ContinuousFunctions

/-!
# Linear Analysis: Hilbert spaces

Inner products, orthogonality, projections, Riesz representation, orthonormal systems,
Bessel's inequality, Parseval, and Riesz--Fischer.
-/

noncomputable section

open Set Function Topology Filter
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Cambridge.LinearAnalysis

/-- Orthogonality in an inner-product space. -/
def Orthogonal {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) : Prop :=
  ⟪x, y⟫_𝕜 = 0

/-- Hilbert-space assumptions, bundled as the standard Mathlib class alias. -/
abbrev IsHilbertSpace (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] := CompleteSpace E

/-- Orthogonal complement of a linear subspace. -/
abbrev orthogonalComplement {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (W : Submodule 𝕜 E) : Submodule 𝕜 E := Wᗮ

/-- Cauchy--Schwarz. -/
theorem cauchySchwarz {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm x y

/-- The parallelogram law. -/
theorem parallelogram {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simpa [two_mul] using parallelogram_law x y

/-- Pythagoras for orthogonal vectors. -/
theorem pythagoras {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {x y : E} (hxy : ⟪x, y⟫_𝕜 = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
  norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hxy

/-- The inner product is jointly continuous. -/
theorem inner_continuous {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    Continuous (fun p : E × E ↦ ⟪p.1, p.2⟫_𝕜) :=
  continuous_inner

/-- Orthogonal complements are closed. -/
theorem orthogonalComplement_isClosed {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (W : Submodule 𝕜 E) :
    IsClosed (Wᗮ : Set E) :=
  W.isClosed_orthogonal

/-- Fréchet--Riesz representation, as a conjugate-linear isometric equivalence. -/
abbrev rieszEquiv (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  InnerProductSpace.toDual 𝕜 E

@[simp] theorem rieszEquiv_apply {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (x y : E) : rieszEquiv 𝕜 E x y = ⟪x, y⟫_𝕜 :=
  InnerProductSpace.toDual_apply_apply 𝕜 x y

/-- Every continuous functional is represented by a unique vector. -/
theorem riesz_representation {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (f : StrongDual 𝕜 E) : ∃! x : E, ∀ y, ⟪x, y⟫_𝕜 = f y := by
  refine ⟨(rieszEquiv 𝕜 E).symm f, ?_, ?_⟩
  · intro y
    simpa using congrFun (congrArg DFunLike.coe ((rieszEquiv 𝕜 E).apply_symm_apply f)) y
  · intro x hx
    apply (rieszEquiv 𝕜 E).injective
    ext y
    simpa [hx y] using (InnerProductSpace.toDual_apply_apply 𝕜 x y)

/-- An orthonormal system. -/
abbrev OrthonormalSystem {ι 𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : ι → E) : Prop :=
  Orthonormal 𝕜 v

/-- Gram--Schmidt orthogonalisation. -/
def gramSchmidt {ι 𝕜 E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : ι → E) : ι → E :=
  InnerProductSpace.gramSchmidt 𝕜 v

/-- Bessel's inequality for an arbitrary orthonormal family. -/
theorem bessel {ι 𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.tsum_inner_products_le x

/-- Finite-dimensional Parseval identity. -/
theorem parseval_finite {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪b i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 :=
  b.sum_sq_norm_inner_right x

/-- A maximal orthonormal family exists. -/
theorem exists_maximal_orthonormal_system {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    ∃ (ι : Type) (v : ι → E), Orthonormal 𝕜 v ∧
      ∀ x, (∀ i, ⟪v i, x⟫_𝕜 = 0) → x = 0 := by
  simpa only [orthogonalFamily_iff] using exists_maximal_orthonormal 𝕜 E

end Cambridge.LinearAnalysis
