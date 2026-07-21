import Mathlib

/-! Source environments 001--061 from `vectors_and_matrices.tex`. -/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Cambridge.VectorsMatrices

abbrev CNumber := ℂ                                                   -- 001
def complexConjugate (z : ℂ) : ℂ := conj z                           -- 002
def argandPoint (z : ℂ) : ℝ × ℝ := (z.re, z.im)                     -- 003
def complexModulus (z : ℂ) : ℝ := ‖z‖                               -- 004
def complexArgument (z : ℂ) : ℝ := z.arg

theorem mul_conj_eq_normSq (z : ℂ) : z * conj z = normSq z :=
  mul_conj z                                                             -- 005

theorem inverse_eq_conj_div_normSq (z : ℂ) :
    z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  inv_def z                                                              -- 006

theorem complex_triangle (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w -- 007

def complexExponential : ℂ → ℂ := Complex.exp                         -- 008

/-- The antidiagonal rearrangement used in the proof of the exponential addition law.
The convergence hypothesis is the condition suppressed in the elementary notes. -/
theorem antidiagonal_reindex {E : Type*} [AddCommMonoid E]
    (a : ℕ → ℕ → E) (r : ℕ) :
    ∑ p ∈ Finset.antidiagonal r, a p.1 p.2 =
      ∑ m ∈ Finset.range (r + 1), a m (r - m) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ a r

theorem complex_exp_add (z w : ℂ) : Complex.exp z * Complex.exp w = Complex.exp (z + w) :=
  (Complex.exp_add z w).symm                                             -- 010

def complexSine : ℂ → ℂ := Complex.sin                              -- 011
def complexCosine : ℂ → ℂ := Complex.cos

theorem complex_euler (z : ℂ) :
    Complex.exp (I * z) = Complex.cos z + I * Complex.sin z := by
  rw [mul_comm I z, Complex.exp_mul_I]
  ring                                                                   -- 012

def rootsOfUnity (n : ℕ) : Set ℂ := {z | z ^ n = 1}                  -- 013

theorem geometric_root_sum {n : ℕ} (w : ℂ) (hw : w ^ n = 1) (hne : w ≠ 1) :
    ∑ k ∈ Finset.range n, w ^ k = 0 := by
  rw [geom_sum_eq hne n, hw, sub_self, zero_div]                         -- 014

def complexLogarithm : ℂ → ℂ := Complex.log                          -- 015
def complexPower (z w : ℂ) : ℂ := Complex.exp (w * Complex.log z)          -- 016

theorem deMoivre (z : ℂ) (n : ℕ) :
    (Complex.cos z + Complex.sin z * I) ^ n =
      Complex.cos ((n : ℂ) * z) + Complex.sin ((n : ℂ) * z) * I :=
  Complex.cos_add_sin_mul_I_pow n z                                      -- 017

def complexLine (z₀ w : ℂ) : Set ℂ :=
  {z | z * conj w - conj z * w = z₀ * conj w - conj z₀ * w}          -- 018
theorem mem_complexLine (z₀ w z : ℂ) :
    z ∈ complexLine z₀ w ↔
      z * conj w - conj z * w = z₀ * conj w - conj z₀ * w := Iff.rfl

def complexCircle (c : ℂ) (r : ℝ) : Set ℂ := {z | ‖z - c‖ = r}    -- 019
theorem circle_equation (c z : ℂ) :
    normSq (z - c) = normSq z + normSq c - 2 * (z * conj c).re :=
  normSq_sub z c

abbrev RealVector (n : ℕ) := EuclideanSpace ℝ (Fin n)                  -- 020
def IsUnitVector {E : Type*} [Norm E] (v : E) : Prop := ‖v‖ = 1           -- 021
def realDot {n : ℕ} (x y : RealVector n) : ℝ := inner ℝ x y          -- 022
abbrev InnerProductStructure (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] := InnerProductSpace ℝ E                         -- 023
def vectorNorm {E : Type*} [Norm E] (x : E) : ℝ := ‖x‖                 -- 024

theorem cauchySchwarz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y -- 025

theorem vectorTriangle {E : Type*} [SeminormedAddGroup E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y                         -- 026

abbrev Vec3 := Fin 3 → ℝ
def cross (a b : Vec3) : Vec3 :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]                                             -- 027
theorem cross_components (a b : Vec3) :
    cross a b = ![a 1 * b 2 - a 2 * b 1,
      a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := rfl            -- 028

def coordinateDot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i
def scalarTriple (a b c : Vec3) : ℝ := coordinateDot a (cross b c)  -- 029
def parallelepipedVolume (a b c : Vec3) : ℝ := |scalarTriple a b c|    -- 030

theorem cross_add (a b c : Vec3) : cross a (b + c) = cross a b + cross a c := by
  funext i
  fin_cases i <;> simp [cross] <;> ring                                 -- 031

def SpansPair {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) : Prop :=
  Submodule.span ℝ ({a,b} : Set E) = ⊤                                -- 032

theorem pair_coefficients_unique {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b : E} (h : LinearIndependent ℝ ![a,b])
    {s t s' t' : ℝ} (heq : s • a + t • b = s' • a + t' • b) :
    s = s' ∧ t = t' := by
  have hz : (s - s') • a + (t - t') • b = 0 := by
    calc
      (s - s') • a + (t - t') • b =
          (s • a + t • b) - (s' • a + t' • b) := by module
      _ = 0 := sub_eq_zero.mpr heq
  have hsum : ∑ i, ![s - s', t - t'] i • ![a,b] i = 0 := by
    simpa [Fin.sum_univ_two] using hz
  have hall := (Fintype.linearIndependent_iff.mp h) ![s - s', t - t'] hsum
  constructor
  · exact sub_eq_zero.mp (by simpa using hall 0)
  · exact sub_eq_zero.mp (by simpa using hall 1)                    -- 033

def IsIndependentPair {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) : Prop :=
  LinearIndependent ℝ ![a,b]                                          -- 034
def IsBasisPair {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) : Prop :=
  IsIndependentPair a b ∧ SpansPair a b                               -- 035

theorem noncoplanar_basis (a b c : Vec3) (h : scalarTriple a b c ≠ 0) :
    LinearIndependent ℝ ![a,b,c] := by
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  intro hd
  apply h
  simp [scalarTriple, coordinateDot, cross, Fin.sum_univ_three]
  simp [Matrix.det_fin_three] at hd
  linear_combination hd -- 036

def IsLinearlyIndependent {E I : Type*} [AddCommGroup E] [Module ℝ E]
    (v : I → E) : Prop := LinearIndependent ℝ v                        -- 037
def IsSpanning {E I : Type*} [AddCommGroup E] [Module ℝ E] (v : I → E) : Prop :=
  Submodule.span ℝ (Set.range v) = ⊤                                  -- 038
abbrev VectorBasis (I E : Type*) [AddCommGroup E] [Module ℝ E] := Module.Basis I ℝ E -- 039
def IsOrthonormalBasis {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Module.Basis I ℝ E) : Prop := Orthonormal ℝ b                 -- 040
def vectorSpaceDimension (E : Type*) [AddCommGroup E] [Module ℝ E] : Cardinal :=
  Module.rank ℝ E                                                       -- 041
abbrev ComplexVector (n : ℕ) := EuclideanSpace ℂ (Fin n)               -- 043
abbrev VectorSubspace (E : Type*) [AddCommGroup E] [Module ℝ E] := Submodule ℝ E -- 044

notation3 "∑ₑ " i ", " r:67 => ∑ i, r                            -- 045
def kroneckerDelta (i j : Fin 3) : ℝ := if i.val = j.val then 1 else 0  -- 046
def epsilon (i j k : Fin 3) : ℝ :=
  if i.val = j.val ∨ j.val = k.val ∨ i.val = k.val then 0
  else if (i.val = 0 ∧ j.val = 1 ∧ k.val = 2) ∨
      (i.val = 1 ∧ j.val = 2 ∧ k.val = 0) ∨
      (i.val = 2 ∧ j.val = 0 ∧ k.val = 1) then 1 else -1           -- 047

theorem cross_epsilon (a b : Vec3) (i : Fin 3) :
    cross a b i = ∑ j, ∑ k, epsilon i j k * a j * b k := by
  fin_cases i <;> simp [cross, epsilon, Fin.sum_univ_three] <;> ring    -- 048

theorem epsilon_contraction (j k p q : Fin 3) :
    ∑ i, epsilon i j k * epsilon i p q =
      kroneckerDelta j p * kroneckerDelta k q -
        kroneckerDelta j q * kroneckerDelta k p := by
  fin_cases j <;> fin_cases k <;> fin_cases p <;> fin_cases q <;>
    norm_num [epsilon, kroneckerDelta, Fin.sum_univ_three] -- 049

theorem scalarTriple_cyclic (a b c : Vec3) :
    scalarTriple a b c = scalarTriple b c a := by
  unfold scalarTriple coordinateDot
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  change
    (a 0 * (b 1 * c 2 - b 2 * c 1) +
      a 1 * (b 2 * c 0 - b 0 * c 2) +
      a 2 * (b 0 * c 1 - b 1 * c 0)) =
    (b 0 * (c 1 * a 2 - c 2 * a 1) +
      b 1 * (c 2 * a 0 - c 0 * a 2) +
      b 2 * (c 0 * a 1 - c 1 * a 0))
  ring                                                                   -- 050

theorem vector_triple (a b c : Vec3) :
    cross a (cross b c) = (coordinateDot a c) • b - (coordinateDot a b) • c := by
  funext i
  fin_cases i <;> simp [cross, coordinateDot, Fin.sum_univ_three] <;> ring -- 051

theorem lagrange_identity (a b c : Vec3) :
    coordinateDot (cross a b) (cross a c) =
      coordinateDot a a * coordinateDot b c - coordinateDot a b * coordinateDot a c := by
  simp [cross, coordinateDot, Fin.sum_univ_three]
  ring                                                                   -- 052

def vectorLine (a t : Vec3) : Set Vec3 := {x | cross (x - a) t = 0}     -- 053
theorem vectorLine_equation (a t x : Vec3) :
    x ∈ vectorLine a t ↔ cross x t = cross a t := by
  constructor
  · intro h
    simp only [vectorLine, Set.mem_setOf_eq] at h
    funext i
    have hi := congrFun h i
    fin_cases i <;> simp [cross] at hi ⊢ <;> linarith
  · intro h
    simp only [vectorLine, Set.mem_setOf_eq]
    funext i
    have hi := congrFun h i
    fin_cases i <;> simp [cross] at hi ⊢ <;> linarith

def vectorPlane (b n : Vec3) : Set Vec3 :=
  {x | coordinateDot x n = coordinateDot b n}                           -- 054
theorem vectorPlane_equation (b n x : Vec3) :
    x ∈ vectorPlane b n ↔ coordinateDot x n = coordinateDot b n := Iff.rfl

def MapImage {A B : Type*} (f : A → B) : Set B := Set.range f            -- 055
abbrev LinearMapOf (R U V : Type*) [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] := U →ₗ[R] V                         -- 056
def linearImage {R U V : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] (f : U →ₗ[R] V) := LinearMap.range f -- 057
def linearKernel {R U V : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] (f : U →ₗ[R] V) := LinearMap.ker f

theorem image_kernel_subspaces {R U V : Type*} [Semiring R] [AddCommMonoid U]
    [Module R U] [AddCommMonoid V] [Module R V] (f : U →ₗ[R] V) :
    linearImage f = LinearMap.range f ∧ linearKernel f = LinearMap.ker f := ⟨rfl, rfl⟩ -- 058

universe u
def linearRank {R : Type*} {U V : Type u} [DivisionRing R] [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) : Cardinal :=
  Module.rank R (LinearMap.range f)                                      -- 059
def linearNullity {R : Type*} {U V : Type u} [DivisionRing R] [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) : Cardinal :=
  Module.rank R (LinearMap.ker f)                                       -- 060

theorem rank_nullity {R : Type*} {U V : Type u} [DivisionRing R] [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) :
    linearRank f + linearNullity f = Module.rank R U :=
  LinearMap.rank_range_add_rank_ker f                                   -- 061

end Cambridge.VectorsMatrices
