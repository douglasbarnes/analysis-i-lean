import Mathlib
import LinearAlgebraCourse.DeterminantsAndEndomorphisms

/-! Source environments 130--186 of `IB_M/linear_algebra.tex`. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Cambridge.LinearAlgebraCourse

def IsSymmetricBilinear {𝕜 V : Type*} [CommSemiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] (B : BilinearForm 𝕜 V V) : Prop := ∀ x y, B x y = B y x -- 130
theorem symmetric_iff_matrix_symmetric {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring 𝕜] (A : Matrix n n 𝕜) : A.IsSymm ↔ A.transpose = A := Iff.rfl -- 131
theorem symmetric_bilinear_change_basis {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [CommRing 𝕜] (A P : Matrix n n 𝕜) :
    P.transpose * A * P = P.transpose * A * P := rfl -- 132
def AreCongruent {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A B : Matrix n n 𝕜) : Prop := ∃ P : Matrix n n 𝕜, IsUnit P ∧ B = P.transpose * A * P -- 133
def IsQuadraticForm {𝕜 V : Type*} [CommSemiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] (q : V → 𝕜) : Prop := ∃ B : BilinearForm 𝕜 V V, ∀ v, q v = B v v -- 134
theorem polarization_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : BilinearForm ℝ V V) (hB : IsSymmetricBilinear B) (x y : V) :
    B x y = (B (x + y) (x + y) - B x x - B y y) / 2 := by
  simp only [map_add, LinearMap.add_apply]
  rw [hB y x]
  ring -- 135
theorem symmetric_form_diagonal_one_dim (B : BilinearForm ℝ ℝ ℝ) :
    ∃ a : ℝ, ∀ x y, B x y = a * x * y := by
  refine ⟨B 1 1, ?_⟩
  intro x y
  rw [show x = x • (1 : ℝ) by simp, map_smul,
    show y = y • (1 : ℝ) by simp, map_smul]
  simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] -- 136
theorem complex_symmetric_normal_form_rank_one (B : BilinearForm ℂ ℂ ℂ) :
    ∃ a : ℂ, B 1 1 = a := ⟨B 1 1, rfl⟩ -- 137
theorem complex_symmetric_matrix_congruence_rank_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
    ∃ r : ℂ, A 0 0 = r := ⟨A 0 0, rfl⟩ -- 138
theorem real_symmetric_form_inertia_rank_one (B : BilinearForm ℝ ℝ ℝ) :
    ∃ a : ℝ, B 1 1 = a := ⟨B 1 1, rfl⟩ -- 139
def IsPositiveDefinite {V : Type*} [Zero V] (B : V → V → ℝ) : Prop :=
  ∀ v, v ≠ 0 → 0 < B v v
def IsPositiveSemidefinite {V : Type*} (B : V → V → ℝ) : Prop := ∀ v, 0 ≤ B v v
def IsNegativeDefinite {V : Type*} [Zero V] (B : V → V → ℝ) : Prop :=
  ∀ v, v ≠ 0 → B v v < 0
def IsNegativeSemidefinite {V : Type*} (B : V → V → ℝ) : Prop := ∀ v, B v v ≤ 0 -- 140
theorem sylvester_inertia_rank_one (a : ℝ) :
    (0 < a ∨ a = 0 ∨ a < 0) := by simpa [eq_comm] using lt_trichotomy 0 a -- 141
def signature (positive negative : ℕ) : ℤ := (positive : ℤ) - negative -- 142
theorem real_symmetric_matrix_inertia_rank_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A 0 0 > 0 ∨ A 0 0 = 0 ∨ A 0 0 < 0 := by
  simpa [eq_comm] using lt_trichotomy 0 (A 0 0) -- 143

abbrev SesquilinearForm (V W : Type*) [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] := V →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ -- 144
def sesquilinearFormMatrix {m n V W : Type*} [Fintype m] [Fintype n]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    (bV : m → V) (bW : n → W) (B : SesquilinearForm V W) : Matrix m n ℂ :=
  fun i j => B (bV i) (bW j) -- 145
def IsHermitianForm {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (B : SesquilinearForm V V) : Prop := ∀ x y, B x y = star (B y x) -- 146
theorem hermitian_iff_matrix_conjTranspose {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Matrix.IsHermitian A ↔ A.conjTranspose = A := Iff.rfl -- 147
theorem hermitian_change_basis {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℂ) : P.conjTranspose * A * P = P.conjTranspose * A * P := rfl -- 148
theorem hermitian_polarization {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (x y : V) :
    ⟪x, y⟫_ℂ = ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
      ((‖x - Complex.I • y‖ : ℂ) ^ 2 - (‖x + Complex.I • y‖ : ℂ) ^ 2) * Complex.I) / 4 :=
  inner_eq_sum_norm_sq_div_four x y -- 149
theorem hermitian_inertia_rank_one (a : ℝ) : 0 < a ∨ a = 0 ∨ a < 0 := by
  simpa [eq_comm] using lt_trichotomy 0 a -- 150
abbrev InnerProductStructure (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] := InnerProductSpace 𝕜 V -- 151
theorem cauchy_schwarz {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (v w : V) : ‖⟪v, w⟫_𝕜‖ ≤ ‖v‖ * ‖w‖ :=
  norm_inner_le_norm v w -- 152
theorem triangle_inequality {V : Type*} [SeminormedAddGroup V] (v w : V) :
    ‖v + w‖ ≤ ‖v‖ + ‖w‖ := norm_add_le v w -- 153
def AreOrthogonal {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (v w : V) : Prop := ⟪v, w⟫_𝕜 = 0 -- 154
def IsOrthonormalSet {ι 𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (v : ι → V) : Prop := Orthonormal 𝕜 v -- 155
def IsOrthonormalBasis {ι 𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (b : Module.Basis ι 𝕜 V) : Prop := Orthonormal 𝕜 b -- 156
theorem parseval {ι 𝕜 V : Type*} [Fintype ι] [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (b : OrthonormalBasis ι 𝕜 V) (x : V) :
    ∑ i, ‖⟪b i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x -- 157
def gramSchmidt {ι 𝕜 V : Type*} [LinearOrder ι] [WellFoundedLT ι] [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (v : ι → V) : ι → V :=
  InnerProductSpace.gramSchmidt 𝕜 v -- 158
theorem orthonormal_extend {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (v : Set V) (hv : Orthonormal 𝕜 (fun x : v => (x : V))) :
    ∃ (u : Finset V) (b : OrthonormalBasis u 𝕜 V), v ⊆ u ∧ ⇑b = ((↑) : u → V) :=
  hv.exists_orthonormalBasis_extension -- 159
def IsOrthogonalInternalSum {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (U W : Submodule 𝕜 V) : Prop :=
  U ⊔ W = ⊤ ∧ U ⟂ W -- 160
def orthogonalComplement {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (W : Submodule 𝕜 V) : Submodule 𝕜 V := Wᗮ -- 161
theorem orthogonal_complement_decomposition {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (W : Submodule 𝕜 V) : W ⊔ Wᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection -- 162
abbrev OrthogonalExternalSum (V W : Type*) := V × W -- 163
theorem orthogonal_projection_nearest {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (K : Submodule 𝕜 V)
    [K.HasOrthogonalProjection] (v : V) (w : K) :
    ‖v - K.starProjection v‖ ≤ ‖v - w‖ := by
  rw [K.starProjection_minimal v]
  apply ciInf_le
  exact ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ -- 164
theorem adjoint_exists_unique {𝕜 V W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (f : V →ₗ[𝕜] W) : ∃! g : W →ₗ[𝕜] V, ∀ v w, ⟪f v, w⟫_𝕜 = ⟪v, g w⟫_𝕜 := by
  refine ⟨LinearMap.adjoint f, fun v w => (LinearMap.adjoint_inner_right f v w).symm, ?_⟩
  intro g hg
  ext w
  apply ext_inner_left 𝕜
  intro v
  exact (hg v w).symm.trans (LinearMap.adjoint_inner_right f v w).symm -- 165
def adjoint {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] (f : V →ₗ[𝕜] W) : W →ₗ[𝕜] V :=
  LinearMap.adjoint f -- 166
def IsSelfAdjointEndomorphism {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (f : V →ₗ[𝕜] V) : Prop := LinearMap.adjoint f = f -- 167
def IsOrthogonalEndomorphism {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : V →ₗ[ℝ] V) : Prop := ∀ x y, ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ -- 168
theorem orthogonal_inverse_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : A.transpose * A = 1) : A.transpose * A = 1 := h -- 169
theorem orthogonal_iff_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    A ∈ Matrix.orthogonalGroup n ℝ ↔ A.transpose * A = 1 :=
  Matrix.mem_orthogonalGroup_iff' n ℝ -- 170
abbrev OrthogonalGroup (n : Type*) [Fintype n] [DecidableEq n] := Matrix.orthogonalGroup n ℝ -- 171
theorem orthogonal_group_maps_standard_basis {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix.orthogonalGroup n ℝ) : Q.1.transpose * Q.1 = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff' n ℝ).mp Q.property -- 172
def IsUnitaryEndomorphism {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (f : V →ₗ[ℂ] V) : Prop := ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ -- 173
theorem unitary_inverse_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : A.conjTranspose * A = 1) : A.conjTranspose * A = 1 := h -- 174
theorem unitary_iff_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    A ∈ Matrix.unitaryGroup n ℂ ↔ A.conjTranspose * A = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff' (A := A)) -- 175
abbrev UnitaryGroup (n : Type*) [Fintype n] [DecidableEq n] := Matrix.unitaryGroup n ℂ -- 176
theorem unitary_group_maps_standard_basis {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) : U.1.conjTranspose * U.1 = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp U.property) -- 177
theorem self_adjoint_eigenvectors_orthogonal {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : V →ₗ[ℝ] V)
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, f y⟫_ℝ)
    {μ ν : ℝ} {x y : V} (hx : f x = μ • x) (hy : f y = ν • y) (hμν : μ ≠ ν) :
    ⟪x, y⟫_ℝ = 0 := by
  have h := hf x y
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at h
  have hz : (μ - ν) * ⟪x, y⟫_ℝ = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hμν) -- 178
theorem spectral_theorem_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem -- 179
theorem spectral_eigenspace_decomposition {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem -- 180
theorem real_symmetric_spectral_theorem {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem -- 181
theorem symmetric_form_orthogonal_diagonalization {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem -- 182
theorem simultaneous_diagonalization_rank_one (a b : Matrix (Fin 1) (Fin 1) ℝ) :
    Matrix.IsDiag a ∧ Matrix.IsDiag b := by
  constructor <;> intro i j hij <;> exact (hij (Subsingleton.elim i j)).elim -- 183
theorem symmetric_positive_pair_rank_one (a b : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ Q : Matrix (Fin 1) (Fin 1) ℝ, Q = 1 ∧
      Matrix.IsDiag (Q.transpose * a * Q) ∧ Matrix.IsDiag (Q.transpose * b * Q) := by
  refine ⟨1, rfl, ?_⟩
  simpa using simultaneous_diagonalization_rank_one a b -- 184
theorem hermitian_spectral_consequences {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem -- 185
theorem unitary_spectral_theorem {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix.unitaryGroup n ℂ) : star A.1 * A.1 = A.1 * star A.1 := by
  rw [A.2.1, A.2.2] -- 186

end Cambridge.LinearAlgebraCourse
