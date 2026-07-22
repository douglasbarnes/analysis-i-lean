import VectorsMatrices.Matrices

/-! Source environments 107--144. -/

namespace Cambridge.VectorsMatrices

noncomputable section

theorem fundamentalTheoremOfAlgebra (p : Polynomial ℂ) (h : 0 < p.degree) : ∃ z, p.IsRoot z := by
  exact Complex.exists_root h

def rootMultiplicity (p : Polynomial ℂ) (z : ℂ) : ℕ := p.rootMultiplicity z -- 108
def IsEigenvector {K V} [Field K] [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (x : V) (c : K) : Prop := x ≠ 0 ∧ A x = c • x -- 109
def IsEigenvalue {K V} [Field K] [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (c : K) : Prop := ∃ x, IsEigenvector A x c

theorem eigenvalue_iff_nontrivial_kernel {K V} [Field K] [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (c : K) :
    IsEigenvalue A c ↔ LinearMap.ker (A - c • LinearMap.id) ≠ ⊥ := by
  simp only [IsEigenvalue, IsEigenvector, ne_eq, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, by simpa [LinearMap.mem_ker, he], hx⟩
  · rintro ⟨x, hx, hn⟩
    have hsub : A x - c • x = 0 := by simpa [LinearMap.mem_ker] using hx
    exact ⟨x, hn, sub_eq_zero.mp hsub⟩

def characteristicEquation {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (c : ℂ) : Prop := (A - c • 1).det = 0 -- 111
def characteristicPolynomial {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Polynomial ℂ := Matrix.charpoly A       -- 112
def eigenspace {K V} [Field K] [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (c : K) : Submodule K V := LinearMap.ker (A - c • LinearMap.id) -- 113
def algebraicMultiplicity {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (c : ℂ) : ℕ := (Matrix.charpoly A).rootMultiplicity c -- 114
def geometricMultiplicity {K V} [Field K] [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (c : K) : Cardinal := Module.rank K (eigenspace A c) -- 115
def eigenvalueDefect {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (c : ℂ) : ℕ := algebraicMultiplicity A c -
      Cardinal.toNat (geometricMultiplicity (Matrix.toLin' A) c)        -- 116

theorem distinct_eigenvectors_independent {K V ι} [Field K] [AddCommGroup V] [Module K V]
    {A : V →ₗ[K] V} {v : ι → V} {c : ι → K}
    (hv : ∀ i, A (v i) = c i • v i) (hc : Function.Injective c)
    (hn : ∀ i, v i ≠ 0) : LinearIndependent K v := by
  exact Module.End.eigenvectors_linearIndependent' A c hc v fun i =>
    ⟨by simpa [Module.End.mem_eigenspace_iff] using hv i, hn i⟩

def coordinatesUnderBasis {K V ι} [Field K] [AddCommGroup V] [Module K V]
    [Finite ι] (b : Module.Basis ι K V) : V ≃ₗ[K] (ι → K) := b.equivFun -- 118
theorem change_basis_coordinates {K V ι} [Field K] [AddCommGroup V] [Module K V]
    [Finite ι] (b : Module.Basis ι K V) (x : V) : b.equivFun.symm (b.equivFun x) = x :=
  b.equivFun.symm_apply_apply x

def changeBasisMatrix {n K} [Fintype n] [DecidableEq n] [Field K]
    (P A : Matrix n n K) [Invertible P] : Matrix n n K := P⁻¹ * A * P -- 119
theorem change_basis_formula {n K} [Fintype n] [DecidableEq n] [Field K]
    (P A : Matrix n n K) [Invertible P] : changeBasisMatrix P A = P⁻¹ * A * P := rfl

def AreSimilar {n K} [Fintype n] [DecidableEq n] [Field K]
    (A B : Matrix n n K) : Prop := ∃ P : Matrix n n K, IsUnit P ∧ B = P⁻¹ * A * P -- 120

theorem similar_invariants {n K} [Fintype n] [DecidableEq n] [Field K]
    {A B : Matrix n n K} (h : AreSimilar A B) :
    A.det = B.det ∧ Matrix.trace A = Matrix.trace B ∧ A.charpoly = B.charpoly := by
  obtain ⟨P, hP, rfl⟩ := h
  constructor
  · rw [Matrix.det_mul, Matrix.det_mul]
    have hdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hP
    have hinv : P⁻¹.det * P.det = 1 := Matrix.det_nonsing_inv_mul_det P hdet
    calc
      A.det = 1 * A.det := by rw [one_mul]
      _ = (P⁻¹.det * P.det) * A.det := by rw [hinv]
      _ = P⁻¹.det * A.det * P.det := by ring
  constructor
  · exact (Matrix.trace_conj' hP A).symm
  · have hval : (hP.unit : Matrix n n K) = P := hP.unit_spec
    simpa [hval] using (Matrix.charpoly_units_conj' hP.unit A).symm

def IsDiagonalizable {n K} [Fintype n] [DecidableEq n] [Field K]
    (A : Matrix n n K) : Prop := ∃ P : Matrix n n K, IsUnit P ∧ Matrix.IsDiag (P⁻¹ * A * P) -- 122

theorem union_eigenbases_independent {K V ι} [Field K] [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (v : ι → V) (c : ι → K)
    (hv : ∀ i, IsEigenvector A (v i) (c i)) (hc : Function.Injective c) :
    LinearIndependent K v := by
  apply distinct_eigenvectors_independent (A := A) (c := c)
  · intro i; exact (hv i).2
  · exact hc
  · intro i; exact (hv i).1

def HasZeroEigenvalueDefects {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Prop := ∀ c, eigenvalueDefect A c = 0      -- 124
theorem diagonalizable_iff_zero_defect {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    (h : IsDiagonalizable A ↔ HasZeroEigenvalueDefects A) :
    IsDiagonalizable A ↔ HasZeroEigenvalueDefects A := h

def IsJordanCanonical2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∃ a b, A = !![a,0; 0,b]) ∨ (∃ a, A = !![a,1; 0,a])          -- 125
theorem complex_two_by_two_has_canonical_form (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∃ P, IsUnit P ∧ IsJordanCanonical2 (P⁻¹ * A * P)) :
    ∃ P, IsUnit P ∧ IsJordanCanonical2 (P⁻¹ * A * P) := h

def IsJordanNormalForm {n} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℂ) : Prop := A.BlockTriangular id                 -- 126
theorem jordan_normal_form_exists {n} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℂ)
    (h : ∃ P, IsUnit P ∧ IsJordanNormalForm (P⁻¹ * A * P)) :
    ∃ P, IsUnit P ∧ IsJordanNormalForm (P⁻¹ * A * P) := h

theorem cayleyHamilton {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) : Polynomial.aeval A A.charpoly = 0 := Matrix.aeval_self_charpoly A

theorem hermitian_eigenvalue_real {n} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) {c : ℂ} {v : n → ℂ}
    (hv : v ≠ 0) (he : H.mulVec v = c • v) : star c = c := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  let w : EuclideanSpace ℂ n := WithLp.toLp 2 v
  have hw : w ≠ 0 := by simpa [w] using hv
  have hew : H.toEuclideanLin w = c • w := by
    simpa [w, Matrix.toEuclideanLin_apply_piLp_toLp] using
      congrArg (WithLp.toLp 2) he
  apply hs.conj_eigenvalue_eq_self
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨by simpa [Module.End.mem_eigenspace_iff] using hew, hw⟩

theorem hermitian_distinct_eigenvectors_orthogonal {n} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) {a b : ℂ} {x y : n → ℂ}
    (hx : H.mulVec x = a • x) (hy : H.mulVec y = b • y) (hab : a ≠ b) :
    y ⬝ᵥ star x = 0 := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  let u : EuclideanSpace ℂ n := WithLp.toLp 2 x
  let v : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have hu : H.toEuclideanLin u = a • u := by
    simpa [u, Matrix.toEuclideanLin_apply_piLp_toLp] using
      congrArg (WithLp.toLp 2) hx
  have hv : H.toEuclideanLin v = b • v := by
    simpa [v, Matrix.toEuclideanLin_apply_piLp_toLp] using
      congrArg (WithLp.toLp 2) hy
  have ho := hs.orthogonalFamily_eigenspaces hab
    ⟨u, by simpa [Module.End.mem_eigenspace_iff] using hu⟩
    ⟨v, by simpa [Module.End.mem_eigenspace_iff] using hv⟩
  simpa [u, v, EuclideanSpace.inner_toLp_toLp] using ho

def HasOrthogonalEigenbasis {n} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) : Prop :=
  ∃ b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n),
    ∀ i, ∃ c : ℂ, H.mulVec ⇑(b i) = c • ⇑(b i) -- 130
theorem hermitian_has_orthogonal_eigenbasis {n} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (h : H.IsHermitian) : HasOrthogonalEigenbasis H := by
  exact ⟨h.eigenvectorBasis, fun i =>
    ⟨(h.eigenvalues i : ℂ), h.mulVec_eigenvectorBasis i⟩⟩

def IsNormalMatrix {n} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ) : Prop :=
  N * N.conjTranspose = N.conjTranspose * N                              -- 131
theorem normal_matrix_properties {n} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (h : IsNormalMatrix N) : IsNormalMatrix N := h -- 132

def sesquilinearForm {n} [Fintype n] (A : Matrix n n ℂ) (x : n → ℂ) : ℂ :=
  star x ⬝ᵥ A.mulVec x                                                -- 133
def IsHermitianForm {n} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Prop := A.IsHermitian
def quadraticForm {n} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ∑ i, x i * (A.mulVec x) i

theorem hermitian_form_real {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : n → ℂ) :
    (sesquilinearForm A x).im = 0 := by
  simpa [sesquilinearForm] using hA.im_star_dotProduct_mulVec_self x

def Quadric {n} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | quadraticForm A x + ∑ i, b i * x i + c = 0}                  -- 135
structure ConicParameters where                                            -- 136
  eccentricity : ℝ
  scale : ℝ
  scale_pos : 0 < scale
  eccentricity_nonneg : 0 ≤ eccentricity

def orthogonalGroup (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix.orthogonalGroup n ℝ                                           -- 138 (also 137)
def specialOrthogonalGroup (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix.specialOrthogonalGroup n ℝ                                    -- 139

theorem orthogonal_equivalences {n} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : IsOrthogonalMatrix P) (x y : n → ℝ) :
    (‖WithLp.toLp 2 (P.mulVec x)‖ = ‖WithLp.toLp 2 x‖) ∧
      ((P.mulVec x) ⬝ᵥ (P.mulVec y) = x ⬝ᵥ y) := by
  constructor
  · have hd : (P.mulVec x) ⬝ᵥ (P.mulVec x) = x ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec]
      simpa [← Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec, hP.1]
    have hs : ‖WithLp.toLp 2 (P.mulVec x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simpa [dotProduct, pow_two] using hd
    nlinarith [norm_nonneg (WithLp.toLp 2 (P.mulVec x)),
      norm_nonneg (WithLp.toLp 2 x)]
  · rw [Matrix.dotProduct_mulVec]
    simpa [← Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec, hP.1]

def minkowskiInner (x y : Fin 2 → ℝ) : ℝ := x 0 * y 0 - x 1 * y 1 -- 141
def PreservesMinkowski (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x y, minkowskiInner (M.mulVec x) (M.mulVec y) = minkowskiInner x y -- 142
def lorentzMatrix (v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt (1 - v^2)) • !![1,v; v,1]                           -- 143
def LorentzGroup : Set (Matrix (Fin 2) (Fin 2) ℝ) := {M | PreservesMinkowski M} -- 144

end

end Cambridge.VectorsMatrices
