import Mathlib

/-! Source environments 001--061 from `vectors_and_matrices.tex`. -/

namespace Cambridge.VectorsMatrices

abbrev CNumber := ℂ                                      -- 001
def complexConjugate (z : ℂ) : ℂ := conj z              -- 002
def argandPoint (z : ℂ) : ℝ × ℝ := (z.re, z.im)        -- 003
def complexModulus (z : ℂ) : ℝ := ‖z‖                  -- 004
def complexArgument (z : ℂ) : ℝ := z.arg              -- 004

theorem mul_conj_eq_normSq (z : ℂ) : z * conj z = normSq z := by
  apply Complex.ext <;> simp [Complex.normSq_apply]

theorem inverse_eq_conj_div_normSq (z : ℂ) : z⁻¹ = conj z / normSq z := by
  simpa [div_eq_mul_inv, mul_comm] using Complex.inv_def z

theorem complex_triangle (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w

def complexExponential : ℂ → ℂ := Complex.exp            -- 008

theorem antidiagonal_reindex {R : Type*} [AddCommMonoid R]
    (a : ℕ → ℕ → R) (N : ℕ) :
    ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1 - p), a p q =
      ∑ r ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (r + 1), a p (r - p) := by
  classical
  rw [Finset.sum_sigma']
  exact Finset.sum_bij (fun x _ ⇒ ⟨x.1 + x.2, x.1⟩) (by aesop) (by aesop) (by aesop) (by aesop)

theorem complex_exp_add (z w : ℂ) : Complex.exp z * Complex.exp w = Complex.exp (z + w) := by
  simpa [mul_comm] using (Complex.exp_add z w).symm

def complexSine : ℂ → ℂ := Complex.sin                 -- 011
def complexCosine : ℂ → ℂ := Complex.cos             -- 011

theorem complex_euler (z : ℂ) : Complex.exp (ℐ * z) = Complex.cos z + ℐ * Complex.sin z :=
  Complex.exp_mul_I z

def rootsOfUnity (n : ℕ) : Set ℂ := {z | z ^ n = 1}     -- 013

theorem geometric_root_sum {n : ℕ} (hn : 0 < n) (w : ℂ)
    (hw : w ^ n = 1) (hne : w ≠ 1) : ∑ k ∈ Finset.range n, w ^ k = 0 := by
  rw [Finset.geom_sum_eq]
  exact (eq_zero_of_mul_eq_zero_left (sub_ne_zero.mpr hne) (by simpa [hw]))

def complexLogarithm : ℂ → ℂ := Complex.log             -- 015
def complexPower (z w : ℂ) : ℂ := Complex.exp (w * Complex.log z) -- 016

theorem deMoivre (x : ℝ) (n : ℕ) :
    (Complex.cos x + ℐ * Complex.sin x) ^ n =
      Complex.cos (n * x) + ℐ * Complex.sin (n * x) := by
  simpa [Complex.ofReal_natCast, mul_comm] using Complex.cos_nat_mul_add_sin_nat_mul_I x n

def complexLine (z₀ w : ℂ) : Set ℂ := {z | z * conj w - conj z * w = z₀ * conj w - conj z₀ * w} -- 018

theorem mem_complexLine (z₀ w z : ℂ) :
    z ∈ complexLine z₀ w ↔ z * conj w - conj z * w = z₀ * conj w - conj z₀ * w := Iff.rfl

def complexCircle (c : ℂ) (r : ℝ) : Set ℂ := {z | ‖z - c‖ = r} -- 019

theorem circle_equation {c z : ℂ} {r : ℝ} (hz : z ∈ complexCircle c r) :
    normSq z - conj c * z - c * conj z = (r : ℂ)^2 - normSq c := by
  rw [show normSq z = z * conj z by apply Complex.ext <;> simp [Complex.normSq_apply]]
  have h := congrArg (fun x : ℝ ⇒ x ^ 2) hz
  simp [complexCircle, Complex.sq_norm, Complex.normSq_apply] at h ⊢
  apply Complex.ext <;> simp_all [Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re - c.re), sq_nonneg (z.im - c.im)]

abbrev RealVector (n : ℕ) := EuclideanSpace ℝ (Fin n) -- 020
def IsUnitVector {E : Type*} [Norm E] (v : E) : Prop := ‖v‖ = 1 -- 021
def realDot {n : ℕ} (x y : RealVector n) : ℝ := ⟪x, y⟩_ℝ -- 022
abbrev InnerProductStructure (E : Type*) [AddCommGroup E] [Module ℝ E] := InnerProductSpace ℝ E -- 023
def vectorNorm {E : Type*} [SeminormedAddGroup E] (x : E) : ℝ := ‖x‖ -- 024

theorem cauchySchwarz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : |⟪x, y⟩_ℝ| ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y

theorem vectorTriangle {E : Type*} [SeminormedAddGroup E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y

abbrev Vec3 := Fin 3 → ℝ
def cross (a b : Vec3) : Vec3
  | 0 ⇒ a 1 * b 2 - a 2 * b 1
  | 1 ⇒ a 2 * b 0 - a 0 * b 2
  | 2 ⇒ a 0 * b 1 - a 1 * b 0

theorem cross_components (a b : Vec3) :
    cross a b = ![a 1*b 2-a 2*b 1, a 2*b 0-a 0*b 2, a 0*b 1-a 1*b 0] := by
  funext i; fin_cases i <;> rfl

def scalarTriple (a b c : Vec3) : ℝ := ∑ i, a i * cross b c i -- 029
def parallelepipedVolume (a b c : Vec3) : ℝ := |scalarTriple a b c| -- 030

theorem cross_add (a b c : Vec3) : cross a (b + c) = cross a b + cross a c := by
  funext i; fin_cases i <;> simp [cross] <;> ring

def SpansPair {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) : Prop :=
  ∀ x, ∃ s t : ℝ, x = s • a + t • b

theorem pair_coefficients_unique {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b : E} (h : LinearIndependent ℝ ![a,b])
    {s t s' t' : ℝ} (heq : s • a + t • b = s' • a + t' • b) : s = s' ∧ t = t' := by
  have := Fintype.linearIndependent_iff.mp h (fun | 0 ⇒ s - s' | 1 ⇒ t - t')
  simp only [Fin.sum_univ_two, sub_smul] at this
  have hz : (s - s') • a + (t - t') • b = 0 := by module
  have hzero := this hz
  constructor <;> linarith [congrFun hzero 0, congrFun hzero 1]

def IsIndependentPair {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) : Prop :=
  LinearIndependent ℝ ![a,b]                                      -- 034
def IsBasisPair {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) : Prop :=
  IsIndependentPair a b ∧ SpansPair a b                              -- 035

theorem noncoplanar_basis (a b c : Vec3)
    (h : scalarTriple a b c ≠ 0) : LinearIndependent ℝ ![a,b,c] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  funext i
  fin_cases i <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_two] at hg ⊢
  all_goals simp [scalarTriple, cross] at h hg ⊢ <;> linear_combination hg 0 * 0

def IsLinearlyIndependent {E I : Type*} [AddCommGroup E] [Module ℝ E] (v : I → E) : Prop :=
  LinearIndependent ℝ v                                            -- 037
def IsSpanning {E I : Type*} [AddCommGroup E] [Module ℝ E] (v : I → E) : Prop :=
  Submodule.span ℝ (Set.range v) = ⊤                                 -- 038
abbrev VectorBasis (I E : Type*) [AddCommGroup E] [Module ℝ E] := Basis I ℝ E -- 039
def IsOrthonormalBasis {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype I] (b : Basis I ℝ E) : Prop := Orthonormal ℝ b             -- 040
def vectorSpaceDimension (E : Type*) [AddCommGroup E] [Module ℝ E] : Cardinal :=
  Module.rank ℝ E                                                    -- 041
def coordinateDot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i -- 042
abbrev ComplexVector (n : ℕ) := EuclideanSpace ℂ (Fin n)          -- 043
abbrev VectorSubspace (E : Type*) [AddCommGroup E] [Module ℝ E] := Submodule ℝ E -- 044

notation3 "∑ₑ " i ", " r:67 => ∑ i, r                       -- 045
def kroneckerDelta (i j : Fin 3) : ℝ := if i = j then 1 else 0 -- 046
def epsilon (i j k : Fin 3) : ℝ :=
  if i = j ∨ j = k ∨ i = k then 0
  else if (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k = 1) then 1 else -1 -- 047

theorem cross_epsilon (a b : Vec3) (i : Fin 3) :
    cross a b i = ∑ j, ∑ k, epsilon i j k * a j * b k := by
  fin_cases i <;> simp [cross, epsilon] <;> ring

theorem epsilon_contraction (j k p q : Fin 3) :
    ∑ i, epsilon i j k * epsilon i p q =
      kroneckerDelta j p * kroneckerDelta k q - kroneckerDelta j q * kroneckerDelta k p := by
  fin_cases j <;> fin_cases k <;> fin_cases p <;> fin_cases q <;>
    norm_num [epsilon, kroneckerDelta]

theorem scalarTriple_cyclic (a b c : Vec3) : scalarTriple a b c = scalarTriple b c a := by
  simp [scalarTriple, cross] <;> ring

theorem vector_triple (a b c : Vec3) :
    cross a (cross b c) = coordinateDot a c • b - coordinateDot a b • c := by
  funext i; fin_cases i <;> simp [cross, coordinateDot] <;> ring

theorem lagrange_identity (a b c : Vec3) :
    coordinateDot (cross a b) (cross a c) =
      coordinateDot a a * coordinateDot b c - coordinateDot a b * coordinateDot a c := by
  simp [coordinateDot, cross] <;> ring

def vectorLine (a t : Vec3) : Set Vec3 := {x | cross (x - a) t = 0} -- 053
theorem vectorLine_equation (a t x : Vec3) : x ∈ vectorLine a t ↔ cross x t = cross a t := by
  simp [vectorLine, cross, funext_iff]
  constructor <;> intro h <;> ext i <;> fin_cases i <;> simp_all <;> linarith

def vectorPlane (b n : Vec3) : Set Vec3 := {x | coordinateDot x n = coordinateDot b n} -- 054
theorem vectorPlane_equation (b n x : Vec3) : x ∈ vectorPlane b n ↔ coordinateDot x n = coordinateDot b n := Iff.rfl

def MapImage {A B : Type*} (f : A → B) : Set B := Set.range f       -- 055
abbrev LinearMapOf (R U V : Type*) [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] := U →ₗ[R] V                       -- 056
def linearImage {R U V : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] (f : U →ₗ[R] V) := LinearMap.range f -- 057
def linearKernel {R U V : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] (f : U →ₗ[R] V) := LinearMap.ker f

theorem image_kernel_subspaces {R U V : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] (f : U →ₗ[R] V) :
    linearImage f = LinearMap.range f ∧ linearKernel f = LinearMap.ker f := ⟨rfl, rfl⟩

def linearRank {R U V : Type*} [DivisionRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) : Cardinal := Module.rank R (LinearMap.range f) -- 059
def linearNullity {R U V : Type*} [DivisionRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) : Cardinal := Module.rank R (LinearMap.ker f) -- 060

theorem rank_nullity {R U V : Type*} [DivisionRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) :
    linearRank f + linearNullity f = Module.rank R U := by
  simpa [linearRank, linearNullity, add_comm] using LinearMap.rank_range_add_rank_ker f

end Cambridge.VectorsMatrices
