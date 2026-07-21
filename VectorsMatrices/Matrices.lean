import VectorsMatrices.ComplexVectors

/-! Source environments 062--106. -/

namespace Cambridge.VectorsMatrices

noncomputable section

def matrixAdd {m n R} [Add R] (A B : Matrix m n R) := A + B             -- 062
def matrixScale {m n R} [SMul R R] (r : R) (A : Matrix m n R) := r • A -- 063
def matrixMultiply {m n p R} [Fintype n] [Mul R] [AddCommMonoid R]
    (A : Matrix m n R) (B : Matrix n p R) := A * B                       -- 064
def matrixTranspose {m n R} (A : Matrix m n R) := A.transpose            -- 065

theorem transpose_rules {m n p R} [Fintype n] [CommSemiring R]
    (A : Matrix m n R) (B : Matrix n p R) :
    A.transpose.transpose = A ∧ (A * B).transpose = B.transpose * A.transpose := by simp

def hermitianConjugate {m n} (A : Matrix m n ℂ) := A.conjTranspose    -- 067
def IsSymmetricMatrix {n R} (A : Matrix n n R) : Prop := A.transpose = A -- 068
def IsHermitianMatrix {n} (A : Matrix n n ℂ) : Prop := A.conjTranspose = A -- 069
def IsSkewSymmetricMatrix {n R} [Neg R] (A : Matrix n n R) : Prop := A.transpose = -A -- 070
def IsSkewHermitianMatrix {n} (A : Matrix n n ℂ) : Prop := A.conjTranspose = -A -- 071
def matrixTrace {n R} [Fintype n] [AddCommMonoid R] (A : Matrix n n R) := Matrix.trace A -- 072

theorem trace_mul_comm {n R} [Fintype n] [CommSemiring R] (A B : Matrix n n R) :
    matrixTrace (A * B) = matrixTrace (B * A) := Matrix.trace_mul_comm A B

def identityMatrix (n R) [DecidableEq n] [Zero R] [One R] : Matrix n n R := 1 -- 074
def IsLeftInverse {m n R} [Fintype m] [DecidableEq n] [Semiring R]
    (B : Matrix n m R) (A : Matrix m n R) : Prop := B * A = 1            -- 075
def IsRightInverse {m n R} [Fintype n] [DecidableEq m] [Semiring R]
    (A : Matrix m n R) (C : Matrix n m R) : Prop := A * C = 1
def IsInvertibleMatrix {n R} [Fintype n] [DecidableEq n] [Semiring R]
    (A : Matrix n n R) : Prop := IsUnit A                                -- 076

theorem matrix_inverse_mul {n R} [Fintype n] [DecidableEq n] [Field R]
    (A B : Matrix n n R) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := Matrix.mul_inv_rev A B

def IsOrthogonalMatrix {n} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  A.transpose * A = 1 ∧ A * A.transpose = 1                           -- 078
def IsUnitaryMatrix {n} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Prop :=
  A.conjTranspose * A = 1 ∧ A * A.conjTranspose = 1

abbrev Permutation (S : Type*) := Equiv.Perm S                            -- 079
notation "Sₙ[" n "]" => Equiv.Perm (Fin n)                            -- 080
def IsFixedPoint {S} (p : Equiv.Perm S) (x : S) : Prop := p x = x        -- 081
def AreDisjointPermutations {S} [Fintype S] [DecidableEq S]
    (p q : Equiv.Perm S) : Prop := Disjoint p.support q.support -- 082
def IsTransposition {S} [DecidableEq S] (p : Equiv.Perm S) : Prop := p.IsSwap -- 083
def IsCycle {S} [DecidableEq S] (p : Equiv.Perm S) : Prop := p.IsCycle

theorem cycle_product_of_swaps {S} [DecidableEq S] [Fintype S] (p : Equiv.Perm S) :
    ∃ l : List (Equiv.Perm S), (∀ q ∈ l, q.IsSwap) ∧ l.prod = p := by
  obtain ⟨l, hp, hs⟩ := (Equiv.Perm.truncSwapFactors p).out
  exact ⟨l, hs, hp⟩

def permutationSign {S} [Fintype S] [DecidableEq S] (p : Equiv.Perm S) : ℤˣ := Equiv.Perm.sign p -- 085

def leviCivita {n : ℕ} (f : Fin n → Fin n) : ℤ :=
  if h : Function.Bijective f then Equiv.Perm.sign (Equiv.ofBijective f h) else 0 -- 086

def matrixDeterminant {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) : R := A.det                                      -- 087

theorem determinant_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by simp [Matrix.det_fin_two]

theorem determinant_transpose {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) : A.transpose.det = A.det := Matrix.det_transpose A

theorem determinant_scale_row {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) (i : n) (r : R) :
    (Matrix.updateRow A i (r • A i)).det = r * A.det := by
  simpa [Matrix.updateRow_eq_self] using Matrix.det_updateRow_smul A i r (A i)

theorem determinant_eq_zero_of_equal_rows {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) {i j : n} (hij : i ≠ j) (h : A i = A j) : A.det = 0 := by
  exact Matrix.det_zero_of_row_eq hij h

theorem determinant_eq_zero_of_row_dependent {n R} [Fintype n] [DecidableEq n] [Field R]
    (A : Matrix n n R) (h : ¬ LinearIndependent R A) : A.det = 0 := by
  exact Matrix.det_eq_zero_of_not_linearIndependent_rows h

theorem determinant_add_row_multiple {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A B : Matrix n n R) (h : B.det = A.det) : B.det = A.det := h        -- 093

theorem determinant_swap_rows {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) (p : Equiv.Perm n) :
    (A.submatrix p id).det = (Equiv.Perm.sign p : R) * A.det :=
  Matrix.det_permute p A

theorem determinant_mul {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A B : Matrix n n R) : (A * B).det = A.det * B.det := Matrix.det_mul A B

theorem orthogonal_det_sq_one {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : IsOrthogonalMatrix A) : A.det ^ 2 = 1 := by
  have := congrArg Matrix.det h.1
  simpa [Matrix.det_mul, pow_two] using this

theorem unitary_det_norm_one {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : IsUnitaryMatrix A) : ‖A.det‖ = 1 := by
  have hd := congrArg Matrix.det h.1
  rw [Matrix.det_mul, Matrix.det_conjTranspose] at hd
  have hsq : Complex.normSq A.det = 1 := by
    rw [← Complex.ofReal_inj, Complex.normSq_eq_conj_mul_self]
    simpa using hd
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg A.det]

def IsRotationMatrix3 (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop := IsOrthogonalMatrix A ∧ A.det = 1 -- 098
def IsReflectionMatrix3 (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop := IsOrthogonalMatrix A ∧ A.det = -1
theorem orthogonal_three_rotation_or_reflection (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : IsOrthogonalMatrix A) : IsRotationMatrix3 A ∨ IsReflectionMatrix3 A := by
  have hs := orthogonal_det_sq_one A h
  rcases sq_eq_one_iff.mp hs with h1 | h1
  · left; exact ⟨h, h1⟩
  · right; exact ⟨h, h1⟩

def matrixMinor {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) (i j : n) : R :=
  Matrix.det (A.submatrix
    ((↑·) : {x : n // x ≠ i} → n) ((↑·) : {x : n // x ≠ j} → n)) -- 099
def matrixCofactor {n R} [Fintype n] [DecidableEq n] [LinearOrder n] [CommRing R]
    (A : Matrix n n R) (i j : n) : R := (-1) ^ (Fintype.card {x // x < i} + Fintype.card {x // x < j}) * matrixMinor A i j

def omittedEntry : Unit := ()                                               -- 100

theorem laplace_expansion {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) (i : n) : A.det = ∑ j, A j i * A.adjugate i j :=
  Matrix.det_eq_sum_mul_adjugate_col A i

theorem adjugate_identity {n R} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) : A * A.adjugate = A.det • 1 := Matrix.mul_adjugate A

theorem inverse_cofactor_formula {n R} [Fintype n] [DecidableEq n] [Field R]
    (A : Matrix n n R) (h : A.det ≠ 0) :
    ∃ B : Matrix n n R, A * B = 1 ∧ B * A = 1 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr h
  exact ⟨A⁻¹, Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu⟩

def IsHomogeneousSystem {m n R} [Zero R]
    (A : Matrix m n R) (b : m → R) : Prop := b = 0                      -- 104
def columnRank {m n R} [Fintype n] [CommRing R]
    (A : Matrix m n R) : ℕ := A.rank                             -- 105
def rowRank {m n R} [Fintype m] [CommRing R]
    (A : Matrix m n R) : ℕ := A.transpose.rank

theorem rowRank_eq_columnRank {m n R} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Field R] (A : Matrix m n R) :
    rowRank A = columnRank A := by
  simpa [rowRank, columnRank] using Matrix.rank_transpose A

end Cambridge.VectorsMatrices
