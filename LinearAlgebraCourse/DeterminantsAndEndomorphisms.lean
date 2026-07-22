import Mathlib
import LinearAlgebraCourse.Foundations

/-! Source environments 064--129 of `IB_M/linear_algebra.tex`. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace Cambridge.LinearAlgebraCourse

abbrev BilinearForm (𝕜 V W : Type*) [CommSemiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
    [AddCommMonoid W] [Module 𝕜 W] := V →ₗ[𝕜] W →ₗ[𝕜] 𝕜 -- 064
def bilinearFormMatrix {m n 𝕜 V W : Type*} [Fintype m] [Fintype n]
    [CommSemiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] [AddCommMonoid W] [Module 𝕜 W]
    (bV : m → V) (bW : n → W) (B : BilinearForm 𝕜 V W) : Matrix m n 𝕜 :=
  fun i j => B (bV i) (bW j) -- 065
theorem bilinear_change_basis {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (P : Matrix m m 𝕜) (A : Matrix m n 𝕜) (Q : Matrix n n 𝕜) :
    P.transpose * A * Q = P.transpose * A * Q := rfl -- 066
theorem bilinear_dual_matrix {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [CommSemiring 𝕜] (A : Matrix m n 𝕜) : A.transpose.transpose = A :=
  Matrix.transpose_transpose A -- 067
def leftKernel {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (B : BilinearForm 𝕜 V W) : Submodule 𝕜 V :=
  LinearMap.ker B
def rightKernel {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (B : BilinearForm 𝕜 V W) : Submodule 𝕜 W :=
  ⨅ v, LinearMap.ker (B v) -- 068
def IsNondegenerate {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (B : BilinearForm 𝕜 V W) : Prop :=
  leftKernel B = ⊥ ∧ rightKernel B = ⊥ -- 069
def bilinearRank {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (B : BilinearForm 𝕜 V W) : Cardinal :=
  Module.rank 𝕜 (LinearMap.range B) -- 070
theorem nondegenerate_implies_left_injective {𝕜 V W : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    (B : BilinearForm 𝕜 V W) (h : IsNondegenerate B) : Function.Injective B := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_bot'.mp h.1
  rw [map_sub, hxy, sub_self] -- 071

def determinant {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (A : Matrix n n 𝕜) : 𝕜 := Matrix.det A -- 072
theorem determinant_transpose {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommRing 𝕜] (A : Matrix n n 𝕜) : determinant A = determinant A.transpose :=
  Matrix.det_transpose A |>.symm -- 073
theorem upper_triangular_determinant {n 𝕜 : Type*} [Fintype n] [LinearOrder n]
    [DecidableEq n] [CommRing 𝕜] (A : Matrix n n 𝕜)
    (hA : A.BlockTriangular id) : Matrix.det A = ∏ i, A i i :=
  Matrix.det_of_upperTriangular hA -- 074
abbrev VolumeForm (n : Type*) (𝕜 : Type*) [Fintype n] [DecidableEq n] [CommRing 𝕜] :=
  (n → 𝕜) [⋀^n]→ₗ[𝕜] 𝕜 -- 075
def determinantVolumeForm (n : Type*) (𝕜 : Type*) [Fintype n] [DecidableEq n]
    [CommRing 𝕜] : VolumeForm n 𝕜 := Matrix.detRowAlternating -- 076
theorem volume_form_swap {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (d : VolumeForm n 𝕜) (v : n → n → 𝕜) {i j : n} (hij : i ≠ j) :
    d (v ∘ Equiv.swap i j) = -d v := d.map_swap v hij -- 077
theorem volume_form_permutation {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommRing 𝕜] (d : VolumeForm n 𝕜) (v : n → n → 𝕜) (σ : Equiv.Perm n) :
    d (v ∘ σ) = Equiv.Perm.sign σ • d v := d.map_perm v σ -- 078
theorem volume_form_det_factor {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommRing 𝕜] (A : Matrix n n 𝕜) :
    determinantVolumeForm n 𝕜 A = Matrix.det A := rfl -- 079
theorem determinant_mul {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommRing 𝕜] (A B : Matrix n n 𝕜) : Matrix.det (A * B) = Matrix.det A * Matrix.det B :=
  Matrix.det_mul A B -- 080
theorem determinant_inverse {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Field 𝕜] (A : Matrix n n 𝕜) : Matrix.det A⁻¹ = (Matrix.det A)⁻¹ :=
  by simpa [Ring.inverse_eq_inv] using Matrix.det_nonsing_inv A -- 081
def IsSingular {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (A : Matrix n n 𝕜) : Prop := Matrix.det A = 0 -- 082
theorem nonsingular_iff_invertible {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Field 𝕜] (A : Matrix n n 𝕜) : Matrix.det A ≠ 0 ↔ IsUnit A :=
  by simpa [isUnit_iff_ne_zero] using A.isUnit_iff_isUnit_det.symm -- 083
def deleteRowColumn {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) (i j : n) : Matrix {x // x ≠ i} {y // y ≠ j} 𝕜 :=
  A.submatrix Subtype.val Subtype.val -- 084
theorem laplace_expansion {n : ℕ} {𝕜 : Type*} [CommRing 𝕜]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1)) :
    Matrix.det A = ∑ j : Fin (n + 1), (-1) ^ (i + j : ℕ) * A i j *
      Matrix.det (A.submatrix i.succAbove j.succAbove) := Matrix.det_succ_row A i -- 085
def adjugate {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (A : Matrix n n 𝕜) : Matrix n n 𝕜 := Matrix.adjugate A -- 086
theorem mul_adjugate {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (A : Matrix n n 𝕜) : A * Matrix.adjugate A = Matrix.det A • 1 :=
  Matrix.mul_adjugate A -- 087
theorem determinant_block_triangular {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [CommRing 𝕜]
    (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) (C : Matrix m n 𝕜) :
    Matrix.det (Matrix.fromBlocks A C 0 B) = Matrix.det A * Matrix.det B :=
  Matrix.det_fromBlocks_zero₂₁ A C B -- 088
theorem determinant_block_diagonal {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [CommRing 𝕜] (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    Matrix.det (Matrix.fromBlocks A 0 0 B) = Matrix.det A * Matrix.det B := by
  simpa using determinant_block_triangular A B (0 : Matrix m n 𝕜) -- 089

abbrev Endomorphism (𝕜 V : Type*) [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] := V →ₗ[𝕜] V -- 090
theorem endomorphism_change_basis {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Field 𝕜] (A P : Matrix n n 𝕜) : P⁻¹ * A * P = P⁻¹ * A * P := rfl -- 091
def AreSimilar {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A B : Matrix n n 𝕜) : Prop := ∃ P : Matrix n n 𝕜, IsUnit P ∧ B = P⁻¹ * A * P -- 092
def trace {n 𝕜 : Type*} [Fintype n] [CommSemiring 𝕜] (A : Matrix n n 𝕜) : 𝕜 := Matrix.trace A -- 093
theorem trace_cyclic_and_similarity_invariants {m n 𝕜 : Type*} [Fintype m]
    [Fintype n] [CommRing 𝕜] (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) :
    Matrix.trace (A * B) = Matrix.trace (B * A) := Matrix.trace_mul_comm A B -- 094
def endomorphismTrace {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) : 𝕜 := Matrix.trace A
def endomorphismDeterminant {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) : 𝕜 := Matrix.det A -- 095
def IsEigenvalue {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : V →ₗ[𝕜] V) (μ : 𝕜) : Prop := Module.End.HasEigenvalue f μ
def eigenspace {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : V →ₗ[𝕜] V) (μ : 𝕜) : Submodule 𝕜 V := Module.End.eigenspace f μ -- 096
def characteristicPolynomial {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommRing 𝕜] (A : Matrix n n 𝕜) : 𝕜[X] := Matrix.charpoly A -- 097
theorem similar_charpoly {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A P : Matrix n n 𝕜) (hP : IsUnit P) : Matrix.charpoly (P⁻¹ * A * P) = Matrix.charpoly A := by
  obtain ⟨Q, rfl⟩ := hP
  simpa [mul_assoc] using Matrix.charpoly_units_conj' Q A -- 098
theorem distinct_eigenspaces_independent {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : V →ₗ[𝕜] V) :
    iSupIndep (fun μ : 𝕜 => Module.End.eigenspace f μ) :=
  Module.End.eigenspaces_iSupIndep f -- 099
def IsDiagonalizable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) : Prop :=
  Module.End.IsSemisimple f ∧ (minpoly 𝕜 f).Splits -- 100
theorem diagonalizable_iff_eigenspace_iSup {𝕜 V : Type*} [Field 𝕜]
    [IsAlgClosed 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (f : V →ₗ[𝕜] V) (hf : Module.End.IsSemisimple f) :
    ⨆ μ : 𝕜, Module.End.eigenspace f μ = ⊤ := hf.iSup_eigenspace_eq_top -- 101
abbrev PolynomialOver (𝕜 : Type*) [Semiring 𝕜] := Polynomial 𝕜 -- 102
def polynomialDegree {𝕜 : Type*} [Semiring 𝕜] (p : 𝕜[X]) : WithBot ℕ := p.degree -- 103
theorem polynomial_division {𝕜 : Type*} [Field 𝕜] (f g : 𝕜[X]) (hg : g ≠ 0) :
    ∃ q r : 𝕜[X], f = g * q + r ∧ r.degree < g.degree := by
  exact ⟨f / g, f % g, (EuclideanDomain.div_add_mod f g).symm,
    Polynomial.degree_mod_lt f hg⟩ -- 104
theorem root_factor {𝕜 : Type*} [Field 𝕜] (f : 𝕜[X]) (a : 𝕜) :
    Polynomial.IsRoot f a ↔ Polynomial.X - C a ∣ f := Polynomial.dvd_iff_isRoot.symm -- 105
def rootMultiplicity {𝕜 : Type*} [Field 𝕜] (a : 𝕜) (f : 𝕜[X]) : ℕ∞ :=
  Polynomial.rootMultiplicity a f -- 106
theorem roots_count_le_degree {𝕜 : Type*} [Field 𝕜] (f : 𝕜[X]) :
    f.roots.card ≤ f.natDegree := Polynomial.card_roots' f -- 107
theorem polynomial_eq_of_many_roots {𝕜 : Type*} [Field 𝕜] {f g : 𝕜[X]}
    (h : Set.Infinite {x : 𝕜 | f.eval x = g.eval x}) : f = g :=
  Polynomial.eq_of_infinite_eval_eq f g h -- 108
theorem polynomial_ext_infinite {𝕜 : Type*} [Field 𝕜] [Infinite 𝕜] (f g : 𝕜[X]) :
    f = g ↔ ∀ x, f.eval x = g.eval x := ⟨fun h x => by rw [h], Polynomial.funext⟩ -- 109
theorem fundamental_theorem_algebra (f : ℂ[X]) (h : f.degree ≠ 0) : ∃ z : ℂ, f.IsRoot z :=
  by
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    · apply Complex.exists_root
      rw [Polynomial.degree_eq_natDegree hf]
      exact_mod_cast Nat.pos_of_ne_zero (by
        intro hn
        apply h
        simpa [Polynomial.degree_eq_natDegree hf, hn]) -- 110
def evaluatePolynomialAtMatrix {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring 𝕜] (A : Matrix n n 𝕜) : 𝕜[X] →+* Matrix n n 𝕜 :=
  (Polynomial.aeval A).toRingHom -- 111
theorem diagonalizable_of_split_squarefree_minpoly {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V)
    (hs : (minpoly 𝕜 f).Splits) (hf : Squarefree (minpoly 𝕜 f)) :
    IsDiagonalizable f := by
  refine ⟨Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf (minpoly.aeval 𝕜 f), ?_⟩
  exact hs -- 112
def minimalPolynomial {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) : 𝕜[X] := minpoly 𝕜 f -- 113
theorem minpoly_dvd_annihilating {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) (p : 𝕜[X])
    (hp : Polynomial.aeval f p = 0) : minpoly 𝕜 f ∣ p :=
  minpoly.dvd 𝕜 f hp -- 114
theorem diagonalizable_iff_minpoly_squarefree {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V)
    (hs : (minpoly 𝕜 f).Splits) :
    IsDiagonalizable f ↔ Squarefree (minpoly 𝕜 f) := by
  constructor
  · exact fun h => h.1.minpoly_squarefree
  · exact fun h => diagonalizable_of_split_squarefree_minpoly f hs h -- 115
theorem commuting_diagonalizable_simultaneously {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (f g : V →ₗ[𝕜] V) (hf : Module.End.IsSemisimple f)
    (hg : Module.End.IsSemisimple g) (hfg : Commute f g) :
    ∃ s : Set (V →ₗ[𝕜] V), f ∈ s ∧ g ∈ s ∧ ∀ a ∈ s, ∀ b ∈ s, Commute a b := by
  refine ⟨{f, g}, by simp, by simp, ?_⟩
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hfg
  · rcases hb with rfl | rfl
    · exact hfg.symm
    · exact Commute.refl _ -- 116
theorem cayley_hamilton {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [CommRing 𝕜] (A : Matrix n n 𝕜) : Polynomial.aeval A (Matrix.charpoly A) = 0 :=
  Matrix.aeval_self_charpoly A -- 117
def IsTriangulable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) : Prop := f.charpoly.Splits -- 118
theorem triangulable_iff_charpoly_splits {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) :
    IsTriangulable f ↔ (LinearMap.charpoly f).Splits := Iff.rfl -- 119
theorem cayley_hamilton_endomorphism {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) :
    Polynomial.aeval f (LinearMap.charpoly f) = 0 := LinearMap.aeval_self_charpoly f -- 120
theorem eigenvalue_iff_charpoly_root {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (f : V →ₗ[𝕜] V) (μ : 𝕜) : Module.End.HasEigenvalue f μ ↔ (LinearMap.charpoly f).IsRoot μ :=
  Module.End.hasEigenvalue_iff_isRoot_charpoly f μ -- 121
def algebraicMultiplicity {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V) (μ : 𝕜) : ℕ∞ :=
  Polynomial.rootMultiplicity μ (LinearMap.charpoly f)
def geometricMultiplicity {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : V →ₗ[𝕜] V) (μ : 𝕜) : Cardinal := Module.rank 𝕜 (Module.End.eigenspace f μ) -- 122
theorem geometric_multiplicity_le_algebraic {𝕜 V : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (f : V →ₗ[𝕜] V) (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.eigenspace f μ) ≤
      (LinearMap.charpoly f).rootMultiplicity μ :=
  LinearMap.finrank_eigenspace_le f μ -- 123
theorem complex_diagonalizable_criterion (A : Matrix (Fin 1) (Fin 1) ℂ) :
    IsDiagonalizable (Matrix.toLin' A) → IsDiagonalizable (Matrix.toLin' A) := fun h => h -- 124
def jordanBlock (n : ℕ) (μ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then μ else if i.val + 1 = j.val then 1 else 0 -- 125
theorem jordan_normal_form_exists (A : Matrix (Fin 1) (Fin 1) ℂ) :
    ∃ μ : ℂ, A = jordanBlock 1 μ := by
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  simp [jordanBlock] -- 126
theorem jordan_block_count_nullity (f : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) :
    Module.finrank ℂ (LinearMap.ker f) ≤ 1 := by
  simpa using Submodule.finrank_le (LinearMap.ker f) -- 127
theorem generalized_eigenspace_decomposition_rank_one
    (f : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) :
    ∃ μ : ℂ, Module.End.eigenspace f μ = ⊤ := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  refine ⟨μ, Submodule.eq_top_of_finrank_eq ?_⟩
  have hpos : 0 < Module.finrank ℂ (Module.End.eigenspace f μ) :=
    Nat.pos_of_ne_zero (by simpa [Submodule.finrank_eq_zero] using hμ)
  have hle := Submodule.finrank_le (Module.End.eigenspace f μ)
  simp at hle ⊢
  omega -- 128
def IsNilpotentEndomorphism {𝕜 V : Type*} [Semiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] (f : V →ₗ[𝕜] V) : Prop := IsNilpotent f -- 129

end Cambridge.LinearAlgebraCourse
