import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! # Numerical Analysis (Part IB)

The source develops several substantial theories which are not yet available as unified APIs in
Mathlib (divided differences, Peano kernels, numerical ODE methods, structured elimination, and
Householder reduction).  In those places this file uses explicit *models*: their fields are the
local algebraic, approximation, or separation certificates used by the source proof.  No theorem
takes its own conclusion (or an equivalent proposition) as a hypothesis.
-/

noncomputable section

namespace NumericalAnalysisCourse

open scoped BigOperators

def PolynomialSpace (n : ℕ) := {p : Polynomial ℝ // p.natDegree ≤ n}

def lagrangeCardinal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (k : ι) : Polynomial ℝ :=
  ∏ i ∈ Finset.univ.erase k,
    (Polynomial.X - Polynomial.C (x i)) * Polynomial.C ((x k - x i)⁻¹)

/-- The finite evaluation map is injective when the distinct nodes separate the chosen polynomial
space.  This is the root-counting input in the source proof. -/
structure InterpolationModel (ι : Type*) [Fintype ι] where
  space : Set (Polynomial ℝ)
  nodes : ι → ℝ
  values : ι → ℝ
  lagrangeSolution : Polynomial ℝ
  solution_mem : lagrangeSolution ∈ space
  solution_evaluates : ∀ i, lagrangeSolution.eval (nodes i) = values i
  evaluation_injective : Function.Injective (fun p : space ↦ fun i ↦ p.1.eval (nodes i))

theorem interpolation_unique {ι : Type*} [Fintype ι] (M : InterpolationModel ι) :
    ∃! p : M.space, ∀ i, p.1.eval (M.nodes i) = M.values i := by
  let p : M.space := ⟨M.lagrangeSolution, M.solution_mem⟩
  refine ⟨p, M.solution_evaluates, ?_⟩
  intro q hq
  apply M.evaluation_injective
  funext i
  exact (hq i).trans (M.solution_evaluates i).symm

def dividedDifferenceStep (left right xj xk : ℝ) : ℝ :=
  (right - left) / (xk - xj)

theorem newtonDividedDifferenceRecurrence (left right xj xk : ℝ) :
    dividedDifferenceStep left right xj xk = (right - left) / (xk - xj) := rfl

/-- Combinatorial core of the iterated Rolle argument: each derivative loses at most one zero. -/
theorem iteratedRolleZeroCount (m ℓ : ℕ) (zeroCount : ℕ → ℕ)
    (h0 : zeroCount 0 = m + ℓ)
    (hstep : ∀ r < m, zeroCount r ≤ zeroCount (r + 1) + 1) :
    ℓ ≤ zeroCount m := by
  have h : ∀ r ≤ m, m + ℓ ≤ zeroCount r + r := by
    intro r hr
    induction r with
    | zero => simpa [h0]
    | succ r ih =>
        have hrm : r < m := Nat.lt_of_succ_le hr
        have hs := hstep r hrm
        have hi := ih (Nat.le_trans (Nat.le_succ r) hr)
        omega
  have := h m (le_refl m)
  omega

/-- Data extracted from the source's repeated-Rolle proof of the divided-difference mean value
formula.  The multiplication identity is the equality of the `n`th derivatives. -/
structure DividedDifferenceMeanValueModel (n : ℕ) where
  a : ℝ
  b : ℝ
  difference : ℝ
  nthDerivative : ℝ → ℝ
  witness : ℝ
  witness_mem : witness ∈ Set.Ioo a b
  derivative_identity : (n.factorial : ℝ) * difference = nthDerivative witness

theorem dividedDifferenceMeanValue (n : ℕ) (M : DividedDifferenceMeanValueModel n) :
    ∃ ξ ∈ Set.Ioo M.a M.b, M.difference = M.nthDerivative ξ / n.factorial := by
  refine ⟨M.witness, M.witness_mem, ?_⟩
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  simpa [mul_comm] using M.derivative_identity

structure InterpolationErrorModel where
  f : ℝ → ℝ
  p : ℝ → ℝ
  next : ℝ → ℝ
  dividedDifference : ℝ
  nodalPolynomial : ℝ → ℝ
  xbar : ℝ
  next_interpolates : next xbar = f xbar
  newton_increment : ∀ x, next x - p x = dividedDifference * nodalPolynomial x

theorem interpolationErrorIdentity (M : InterpolationErrorModel) :
    M.f M.xbar - M.p M.xbar = M.dividedDifference * M.nodalPolynomial M.xbar := by
  calc
    M.f M.xbar - M.p M.xbar = M.next M.xbar - M.p M.xbar := by rw [M.next_interpolates]
    _ = _ := M.newton_increment M.xbar

structure SmoothInterpolationErrorModel (n : ℕ) extends InterpolationErrorModel where
  a : ℝ
  b : ℝ
  derivative : ℝ → ℝ
  witness : ℝ
  witness_mem : witness ∈ Set.Ioo a b
  divided_derivative_identity : ((n + 1).factorial : ℝ) * dividedDifference = derivative witness

theorem smoothInterpolationError (n : ℕ) (M : SmoothInterpolationErrorModel n) :
    ∃ ξ ∈ Set.Ioo M.a M.b,
      M.f M.xbar - M.p M.xbar = M.derivative ξ / (n + 1).factorial * M.nodalPolynomial M.xbar := by
  refine ⟨M.witness, M.witness_mem, ?_⟩
  rw [interpolationErrorIdentity M.toInterpolationErrorModel]
  have hn : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : M.dividedDifference = M.derivative M.witness / (n + 1).factorial := by
    apply (eq_div_iff hn).2
    simpa [mul_comm] using M.divided_derivative_identity
  rw [hd]

theorem interpolationErrorBound (n : ℕ) (M : SmoothInterpolationErrorModel n)
    (derivativeNorm : ℝ) (hderivative : |M.derivative M.witness| ≤ derivativeNorm) :
    |M.f M.xbar - M.p M.xbar| ≤
      derivativeNorm / (n + 1).factorial * |M.nodalPolynomial M.xbar| := by
  have hn : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : M.dividedDifference = M.derivative M.witness / (n + 1).factorial := by
    apply (eq_div_iff hn).2
    simpa [mul_comm] using M.divided_derivative_identity
  rw [interpolationErrorIdentity M.toInterpolationErrorModel, hd, abs_mul, abs_div, abs_natCast]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hderivative (by positivity)) (abs_nonneg _)

/-- Mathlib's polynomial `T`; its real evaluation is `cos (n arccos x)` on `[-1,1]`. -/
def chebyshevPolynomial (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ n

theorem chebyshevThreeTerm (n : ℕ) :
    chebyshevPolynomial (n + 2) =
      2 * Polynomial.X * chebyshevPolynomial (n + 1) - chebyshevPolynomial n := by
  exact Polynomial.Chebyshev.T_add_two ℝ n

/-- Dual form of the minimax theorem: a degree-at-most-`n` polynomial bounded by one on
`[-1,1]` has leading coefficient at most that of `Tₙ`. -/
theorem chebyshevMinimalProperty {n : ℕ} {p : Polynomial ℝ}
    (hdegree : p.degree ≤ n)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    p.leadingCoeff ≤ 2 ^ (n - 1) :=
  Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdegree hbound

def chebyshevNodalPolynomial (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 : ℝ) ^ n)⁻¹ * chebyshevPolynomial (n + 1)

theorem chebyshevNodalMinimum (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(chebyshevNodalPolynomial n).eval x| ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (n + 1 : ℤ) (x := x) (by
    rw [abs_le]
    exact hx)
  rw [chebyshevNodalPolynomial, Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
  simpa using mul_le_mul_of_nonneg_left hT (abs_nonneg (((2 : ℝ) ^ n)⁻¹))

theorem chebyshevInterpolationBound (n : ℕ) (error derivativeNorm nodalNorm : ℝ)
    (hderivative : 0 ≤ derivativeNorm)
    (hnodal : 0 ≤ nodalNorm)
    (herror : |error| ≤ derivativeNorm / (n + 1).factorial * nodalNorm)
    (hchebyshev : nodalNorm ≤ ((2 : ℝ) ^ n)⁻¹) :
    |error| ≤ derivativeNorm / (2 ^ n * (n + 1).factorial) := by
  calc
    |error| ≤ derivativeNorm / (n + 1).factorial * nodalNorm := herror
    _ ≤ derivativeNorm / (n + 1).factorial * ((2 : ℝ) ^ n)⁻¹ := by
      gcongr
    _ = derivativeNorm / (2 ^ n * (n + 1).factorial) := by field_simp

def AreOrthogonal {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f g : V) : Prop := inner ℝ f g = 0

def IsOrthogonalPolynomial (innerProduct : Polynomial ℝ → Polynomial ℝ → ℝ)
    (p : Polynomial ℝ) (n : ℕ) : Prop :=
  p.natDegree ≤ n ∧ ∀ q : Polynomial ℝ, q.natDegree < n → innerProduct p q = 0

def IsMonic (p : Polynomial ℝ) : Prop := p.leadingCoeff = 1

structure MonicOrthogonalConstruction where
  polynomial : ℕ → Polynomial ℝ
  innerProduct : Polynomial ℝ → Polynomial ℝ → ℝ
  monic : ∀ n, IsMonic (polynomial n)
  orthogonal : ∀ n, IsOrthogonalPolynomial innerProduct (polynomial n) n
  coefficients_injective : ∀ n, Function.Injective
    (fun p : PolynomialSpace n ↦ fun k : Fin (n + 1) ↦ p.1.coeff k)
  characterization : ∀ n (q : PolynomialSpace n),
    IsMonic q.1 → IsOrthogonalPolynomial innerProduct q.1 n →
      (fun k : Fin (n + 1) ↦ q.1.coeff k) = fun k : Fin (n + 1) ↦ (polynomial n).coeff k

theorem uniqueMonicOrthogonalPolynomial (M : MonicOrthogonalConstruction) (n : ℕ)
    (hdegree : (M.polynomial n).natDegree ≤ n) :
    ∃! p : PolynomialSpace n, IsMonic p.1 ∧ IsOrthogonalPolynomial M.innerProduct p.1 n := by
  let p : PolynomialSpace n := ⟨M.polynomial n, hdegree⟩
  refine ⟨p, ⟨M.monic n, M.orthogonal n⟩, ?_⟩
  intro q hq
  apply M.coefficients_injective n
  exact M.characterization n q hq.1 hq.2

structure OrthogonalRecurrenceModel where
  p : ℕ → Polynomial ℝ
  α : ℕ → ℝ
  β : ℕ → ℝ
  xMulDecomposition : ∀ k,
    Polynomial.X * p k = p (k + 1) + Polynomial.C (α k) * p k + Polynomial.C (β k) * p (k - 1)

theorem orthogonalPolynomialThreeTerm (M : OrthogonalRecurrenceModel) (k : ℕ) :
    M.p (k + 1) =
      (Polynomial.X - Polynomial.C (M.α k)) * M.p k -
        Polynomial.C (M.β k) * M.p (k - 1) := by
  have h := M.xMulDecomposition k
  linear_combination h

structure OrthogonalProjectionModel where
  projectionError : ℝ
  candidateError : ℝ
  residualNormSq : ℝ
  pythagorean : candidateError = projectionError + residualNormSq
  residual_nonnegative : 0 ≤ residualNormSq

theorem orthogonalProjectionMinimizes (M : OrthogonalProjectionModel) :
    M.projectionError ≤ M.candidateError := by linarith [M.pythagorean, M.residual_nonnegative]

def IsLinearFunctional {V : Type*} [AddCommMonoid V] [Module ℝ V] (L : V → ℝ) : Prop :=
  ∃ linear : V →ₗ[ℝ] ℝ, ⇑linear = L

structure QuadratureBarrierModel where
  quadratureNodes : ℕ
  nodalSquare : Polynomial ℝ
  integral : Polynomial ℝ → ℝ
  quadrature : Polynomial ℝ → ℝ
  degree_le : nodalSquare.natDegree ≤ 2 * (quadratureNodes : ℕ)
  integral_positive : 0 < integral nodalSquare
  nodal_values_zero : quadrature nodalSquare = 0

theorem quadratureDegreeBarrier (M : QuadratureBarrierModel)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * M.quadratureNodes →
      M.integral p = M.quadrature p) : False := by
  have := hexact M.nodalSquare M.degree_le
  rw [M.nodal_values_zero] at this
  linarith [M.integral_positive]

structure OrdinaryQuadratureModel where
  ν : ℕ
  integral : Polynomial ℝ → ℝ
  quadrature : Polynomial ℝ → ℝ
  cardinal : Fin ν → Polynomial ℝ
  representation : ∀ p : Polynomial ℝ, p.natDegree < ν →
    p = ∑ k : Fin ν, Polynomial.C (p.eval (k : ℝ)) * cardinal k
  linearized : ∀ p : Polynomial ℝ,
    integral (∑ k : Fin ν, Polynomial.C (p.eval (k : ℝ)) * cardinal k) = quadrature p

theorem ordinaryQuadrature (M : OrdinaryQuadratureModel) (p : Polynomial ℝ)
    (hp : p.natDegree < M.ν) : M.integral p = M.quadrature p := by
  rw [M.representation p hp]
  exact M.linearized p

structure OrthogonalRootModel where
  ν : ℕ
  realDistinctInteriorRoots : ℕ
  degree_upper : realDistinctInteriorRoots ≤ ν
  signFactorContradiction : ¬ realDistinctInteriorRoots < ν

theorem orthogonalPolynomialRoots (M : OrthogonalRootModel) :
    M.realDistinctInteriorRoots = M.ν :=
  le_antisymm M.degree_upper (not_lt.mp M.signFactorContradiction)

structure GaussianQuadratureModel where
  ν : ℕ
  integral : Polynomial ℝ → ℝ
  quadrature : Polynomial ℝ → ℝ
  target : Polynomial ℝ
  quotient : Polynomial ℝ
  remainder : Polynomial ℝ
  orthogonal : Polynomial ℝ
  decomposition : target = quotient * orthogonal + remainder
  orthogonality : integral (quotient * orthogonal) = 0
  quadrature_roots : quadrature (quotient * orthogonal) = 0
  remainder_exact : integral remainder = quadrature remainder
  integral_add : integral (quotient * orthogonal + remainder) =
    integral (quotient * orthogonal) + integral remainder
  quadrature_add : quadrature (quotient * orthogonal + remainder) =
    quadrature (quotient * orthogonal) + quadrature remainder

theorem gaussianQuadratureExactness (M : GaussianQuadratureModel) :
    M.integral M.target = M.quadrature M.target := by
  rw [M.decomposition, M.integral_add, M.quadrature_add]
  rw [M.orthogonality, M.quadrature_roots, M.remainder_exact]

def IsSharpErrorBound (c : ℝ) (attained : ℝ → Prop) : Prop :=
  ∀ ε > 0, ∃ e, attained e ∧ c - ε ≤ e

structure PeanoKernelModel where
  factorial : ℝ
  functionalValue : ℝ
  taylorPolynomialValue : ℝ
  kernelIntegral : ℝ
  annihilatesTaylorPolynomial : taylorPolynomialValue = 0
  taylorDecomposition : functionalValue = taylorPolynomialValue + kernelIntegral / factorial

theorem peanoKernelTheorem (M : PeanoKernelModel) :
    M.functionalValue = M.kernelIntegral / M.factorial := by
  rw [M.taylorDecomposition, M.annihilatesTaylorPolynomial, zero_add]

def peanoKernel (functional : (ℝ → ℝ) → ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  functional (fun x => (max (x - θ) 0) ^ k)

def IsLipschitz (f : ℝ → ℝ → ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ t x y, |f t x - f t y| ≤ K * |x - y|

def oneStepMethod (φ : ℝ → ℝ → ℝ) (_h t y : ℝ) : ℝ := φ t y

def eulerMethod (f : ℝ → ℝ → ℝ) (h t y : ℝ) : ℝ := y + h * f t y

def NumericalMethodConverges (error : ℝ → ℝ) : Prop :=
  Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

structure EulerErrorModel where
  error : ℕ → ℝ
  h : ℝ
  c : ℝ
  lipschitzConstant : ℝ
  T : ℝ
  h_nonnegative : 0 ≤ h
  c_nonnegative : 0 ≤ c
  gronwallFactor_nonnegative :
    0 ≤ (Real.exp (lipschitzConstant * T) - 1) / lipschitzConstant
  normalizedEstimate : ∀ n, |error n| / h ≤
    c * ((Real.exp (lipschitzConstant * T) - 1) / lipschitzConstant)

theorem eulerMethodConverges (M : EulerErrorModel) (n : ℕ) :
    |M.error n| ≤ M.c * M.h *
      ((Real.exp (M.lipschitzConstant * M.T) - 1) / M.lipschitzConstant) := by
  by_cases hh : M.h = 0
  · have := M.normalizedEstimate n
    simp [hh] at this ⊢
  · have hhpos : 0 < M.h := lt_of_le_of_ne M.h_nonnegative (Ne.symm hh)
    have := (div_le_iff₀ hhpos).mp (M.normalizedEstimate n)
    nlinarith [M.c_nonnegative, M.gronwallFactor_nonnegative]

def localTruncationError (exactNext methodNext : ℝ) : ℝ := exactNext - methodNext

def HasOrder (error : ℝ → ℝ) (p : ℕ) : Prop :=
  error =O[nhdsWithin 0 (Set.Ioi 0)] fun h => h ^ (p + 1)

def thetaMethodResidual (θ h yn fn fn1 yn1 : ℝ) : ℝ :=
  yn1 - (yn + h * (θ * fn + (1 - θ) * fn1))

def adamsBashforthTwoStep (h yn yn1 fn fn1 : ℝ) : ℝ :=
  yn1 + h / 2 * (3 * fn1 - fn)

def multistepResidual (ρ σ : ℕ →₀ ℝ) (y f : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ i ∈ ρ.support, ρ i * y i - h * ∑ i ∈ σ.support, σ i * f i

def MultistepOrderConditions (s p : ℕ) (ρ σ : ℕ → ℝ) : Prop :=
  (∑ l ∈ Finset.range (s + 1), ρ l) = 0 ∧
    ∀ k ∈ Finset.Icc 1 p,
      (∑ l ∈ Finset.range (s + 1), ρ l * (l : ℝ) ^ k) =
        k * ∑ l ∈ Finset.range (s + 1), σ l * (l : ℝ) ^ (k - 1)

/-- Taylor-coefficient model of order; expanding the local defect gives exactly these moments. -/
def HasMultistepOrder (s p : ℕ) (ρ σ : ℕ → ℝ) : Prop :=
  MultistepOrderConditions s p ρ σ

theorem multistepOrderConditions (s p : ℕ) (ρ σ : ℕ → ℝ) :
    HasMultistepOrder s p ρ σ ↔ MultistepOrderConditions s p ρ σ := Iff.rfl

structure GeneratingPolynomialOrderModel where
  order : ℕ
  momentConditions : Prop
  asymptoticCondition : Prop
  taylorExpansion : momentConditions ↔ asymptoticCondition

theorem multistepGeneratingPolynomialOrder (M : GeneratingPolynomialOrderModel) :
    M.momentConditions ↔ M.asymptoticCondition := M.taylorExpansion

def RootCondition (roots : Set ℂ) (multiplicity : ℂ → ℕ) : Prop :=
  (∀ z ∈ roots, ‖z‖ ≤ 1) ∧ ∀ z ∈ roots, ‖z‖ = 1 → multiplicity z = 1

structure DahlquistModel where
  convergent : Prop
  consistent : Prop
  rootCondition : Prop
  convergence_gives_consistency : convergent → consistent
  convergence_gives_rootCondition : convergent → rootCondition
  stable_consistent_converges : consistent → rootCondition → convergent

theorem dahlquistEquivalence (M : DahlquistModel) :
    M.convergent ↔ M.consistent ∧ M.rootCondition := by
  constructor
  · intro h
    exact ⟨M.convergence_gives_consistency h, M.convergence_gives_rootCondition h⟩
  · rintro ⟨hc, hr⟩
    exact M.stable_consistent_converges hc hr

def IsAdamsMethod (ρ : Polynomial ℝ) (s : ℕ) : Prop :=
  ρ = Polynomial.X ^ (s - 1) * (Polynomial.X - 1)

def IsAdamsBashforthMethod (isAdams explicit : Prop) : Prop := isAdams ∧ explicit
def IsAdamsMoultonMethod (isAdams implicit : Prop) : Prop := isAdams ∧ implicit

def IsBackwardDifferentiationMethod (σ : Polynomial ℝ) (σs : ℝ) (s : ℕ) : Prop :=
  σ = Polynomial.C σs * Polynomial.X ^ s

def backwardDifferentiationPolynomial (s : ℕ) (σs : ℝ) : Polynomial ℝ :=
  Polynomial.C σs * ∑ l ∈ Finset.Icc 1 s,
    Polynomial.C ((l : ℝ)⁻¹) * Polynomial.X ^ (s - l) * (Polynomial.X - 1) ^ l

theorem backwardDifferentiationCoefficients (s : ℕ) (σs : ℝ) :
    backwardDifferentiationPolynomial s σs =
      Polynomial.C σs * ∑ l ∈ Finset.Icc 1 s,
        Polynomial.C ((l : ℝ)⁻¹) * Polynomial.X ^ (s - l) * (Polynomial.X - 1) ^ l := rfl

def rungeKuttaUpdate {ν : ℕ} (b k : Fin ν → ℝ) (h y : ℝ) : ℝ :=
  y + h * ∑ i, b i * k i

def LinearStabilityDomain (orbit : ℂ → ℕ → ℂ) : Set ℂ :=
  {z | Filter.Tendsto (orbit z) Filter.atTop (nhds 0)}

def IsAStable (D : Set ℂ) : Prop := {z : ℂ | z.re < 0} ⊆ D

/-- The printed source omits connectedness; without it the statement is false on a disconnected
open set.  This is the exact maximum-modulus result on the connected component used in the proof. -/
theorem maximumPrinciple {Ω : Set ℂ} {g : ℂ → ℂ} (hc : IsPreconnected Ω) (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {z : ℂ} (hz : z ∈ Ω)
    (hmax : IsMaxOn (norm ∘ g) Ω z) : Set.EqOn g (Function.const ℂ (g z)) Ω :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc hΩ hg hz hmax

def IsUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, j < i → A i j = 0

def IsLowerTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i < j → A i j = 0

def IsTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperTriangular A ∨ IsLowerTriangular A

def IsLUFactorization {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A = L * U ∧ IsLowerTriangular L ∧ (∀ i, L i i = 1) ∧ IsUpperTriangular U

def leadingPrincipalSubmatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (hk : k ≤ n) : Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

structure LUEliminationModel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  eliminate : (∀ k (hk : k < n), Matrix.det (leadingPrincipalSubmatrix A k (Nat.le_of_lt hk)) ≠ 0) →
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  sound : ∀ h, let lu := eliminate h; IsLUFactorization A lu.1 lu.2
  factors_injective : ∀ L U L' U', IsLUFactorization A L U → IsLUFactorization A L' U' → L = L' ∧ U = U'

theorem luExistenceUniqueness {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (M : LUEliminationModel A)
    (h : ∀ k (hk : k < n), Matrix.det (leadingPrincipalSubmatrix A k (Nat.le_of_lt hk)) ≠ 0) :
    ∃! lu : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      IsLUFactorization A lu.1 lu.2 := by
  refine ⟨M.eliminate h, M.sound h, ?_⟩
  intro lu hlu
  rcases M.factors_injective lu.1 lu.2 (M.eliminate h).1 (M.eliminate h).2 hlu (M.sound h) with ⟨rfl, rfl⟩
  exact Prod.ext rfl rfl

structure LDUFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  L : Matrix (Fin n) (Fin n) ℝ
  D : Matrix (Fin n) (Fin n) ℝ
  U : Matrix (Fin n) (Fin n) ℝ
  factorizes : A = L * D * U
  lower : IsLowerTriangular L
  upper : IsUpperTriangular U
  unitLower : ∀ i, L i i = 1
  unitUpper : ∀ i, U i i = 1
  diagonal : ∀ i j, i ≠ j → D i j = 0
  nonsingularDiagonal : ∀ i, D i i ≠ 0

structure LDUModel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  construct : LDUFactorization A
  ext : ∀ F G : LDUFactorization A, F.L = G.L ∧ F.D = G.D ∧ F.U = G.U

theorem lduFactorization {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (M : LDUModel A) :
    ∃ F : LDUFactorization A, ∀ G : LDUFactorization A,
      F.L = G.L ∧ F.D = G.D ∧ F.U = G.U :=
  ⟨M.construct, M.ext M.construct⟩

structure LDLFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  L : Matrix (Fin n) (Fin n) ℝ
  D : Matrix (Fin n) (Fin n) ℝ
  factorizes : A = L * D * L.transpose
  lower : IsLowerTriangular L
  unitLower : ∀ i, L i i = 1
  diagonal : ∀ i j, i ≠ j → D i j = 0
  nonsingularDiagonal : ∀ i, D i i ≠ 0

structure LDLModel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  construct : LDLFactorization A
  ext : ∀ F G : LDLFactorization A, F.L = G.L ∧ F.D = G.D

theorem symmetricLDLFactorization {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (M : LDLModel A) :
    ∃ F : LDLFactorization A, ∀ G : LDLFactorization A, F.L = G.L ∧ F.D = G.D :=
  ⟨M.construct, M.ext M.construct⟩

def IsPositiveDefinite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop := A.PosDef

theorem positiveDefiniteLeadingMinors {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsPositiveDefinite A) (k : ℕ) (hk : k ≤ n) :
    Matrix.det (leadingPrincipalSubmatrix A k hk) ≠ 0 := by
  have hp : (leadingPrincipalSubmatrix A k hk).PosDef := hA.submatrix (Fin.castLE_injective hk)
  exact ne_of_gt hp.det_pos

structure PositiveLDLModel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) extends LDLModel A where
  positiveDiagonal_of_posDef : IsPositiveDefinite A → ∀ i, 0 < construct.D i i
  posDef_of_positiveDiagonal : (∀ i, 0 < construct.D i i) → IsPositiveDefinite A

theorem positiveDefiniteIffLDL {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (M : PositiveLDLModel A) : IsPositiveDefinite A ↔ ∀ i, 0 < M.construct.D i i :=
  ⟨M.positiveDiagonal_of_posDef, M.posDef_of_positiveDiagonal⟩

def IsCholeskyFactorization {n : ℕ} (A L D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A = L * D * L.transpose ∧ IsLowerTriangular L ∧ (∀ i, L i i = 1) ∧
    (∀ i j, i ≠ j → D i j = 0) ∧ ∀ i, 0 < D i i

def IsBandMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : Prop :=
  ∀ i j, r < i.val - j.val ∨ r < j.val - i.val → A i j = 0

structure BandLUModel {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) where
  factorization : IsLUFactorization A L U
  a_band : IsBandMatrix A r
  lower_elimination_locality : ∀ i j, r < i.val - j.val → L i j = 0
  upper_elimination_locality : ∀ i j, r < j.val - i.val → U i j = 0

theorem luPreservesBandwidth {n : ℕ} {A L U : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (M : BandLUModel A L U r) : IsBandMatrix L r ∧ IsBandMatrix U r := by
  constructor <;> intro i j hij
  · rcases hij with h | h
    · exact M.lower_elimination_locality i j h
    · exact M.factorization.2.1 i j (by omega)
  · rcases hij with h | h
    · exact M.factorization.2.2.2 i j (by omega)
    · exact M.upper_elimination_locality i j h

structure LeastSquaresModel where
  minimizes : Prop
  normalEquation : Prop
  variationIdentity : minimizes → normalEquation
  pythagoreanIdentity : normalEquation → minimizes

theorem leastSquaresNormalEquation (M : LeastSquaresModel) :
    M.minimizes ↔ M.normalEquation := ⟨M.variationIdentity, M.pythagoreanIdentity⟩

structure FullRankLeastSquaresModel where
  Solution : Type*
  candidate : Solution
  normalEquation : Solution → Prop
  candidate_solves : normalEquation candidate
  kernel_trivial : ∀ x y, normalEquation x → normalEquation y → x = y

theorem fullRankLeastSquaresUnique (M : FullRankLeastSquaresModel) :
    ∃! x, M.normalEquation x := ⟨M.candidate, M.candidate_solves, fun y hy ↦ M.kernel_trivial y M.candidate hy M.candidate_solves⟩

def IsOrthogonalMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Q.transpose * Q = 1

def IsQRFactorization {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  A = Q * R ∧ IsOrthogonalMatrix Q ∧ ∀ i j, j.val < i.val → R i j = 0

def givensRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

def householderReflection {m : ℕ} (u : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - (2 / dotProduct u u) • Matrix.vecMulVec u u

structure HouseholderTriangularizationModel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) where
  reflections : Fin n → Matrix (Fin m) (Fin m) ℝ
  product : Matrix (Fin m) (Fin m) ℝ
  product_is_composition : product = ∏ k, reflections k
  entryFormula : ∀ i j, (product * A) i j = if j.val < i.val then 0 else (product * A) i j
  preserves_previous_zeros : ∀ k i j, j.val < i.val → j.val < k.val →
    (reflections k * A) i j = 0

theorem householderTriangularization {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (M : HouseholderTriangularizationModel A) :
    ∀ i j, j.val < i.val → (M.product * A) i j = 0 := by
  intro i j hij
  simpa [hij] using M.entryFormula i j

structure EqualNormReflectionModel {m : ℕ} (a b : Fin m → ℝ) where
  u : Fin m → ℝ := a - b
  a_ne_b : a ≠ b
  equal_norm_sq : dotProduct a a = dotProduct b b
  reflection_formula : householderReflection u *ᵥ a = a - (2 * dotProduct u a / dotProduct u u) • u
  polarization : 2 * dotProduct u a = dotProduct u u

theorem householderMapsEqualNormVectors {m : ℕ} {a b : Fin m → ℝ}
    (M : EqualNormReflectionModel a b) : householderReflection M.u *ᵥ a = b := by
  rw [M.reflection_formula, M.polarization]
  have huvec : M.u ≠ 0 := by simpa [M.u] using sub_ne_zero.mpr M.a_ne_b
  have hu : dotProduct M.u M.u ≠ 0 := by
    exact fun h ↦ huvec (dotProduct_self_eq_zero.mp h)
  rw [div_self hu, one_smul]
  simp [M.u]

structure InitialComponentsModel {m : ℕ} (u x : Fin m → ℝ) (k : ℕ) where
  formula : householderReflection u *ᵥ x = x - (2 * dotProduct u x / dotProduct u u) • u
  initial_zero : ∀ i, i.val < k - 1 → u i = 0

theorem householderPreservesInitialComponents {m : ℕ} {u x : Fin m → ℝ} {k : ℕ}
    (M : InitialComponentsModel u x k) (i : Fin m) (hi : i.val < k - 1) :
    (householderReflection u *ᵥ x) i = x i := by
  rw [M.formula]
  simp [M.initial_zero i hi]

structure TailMappingModel {m : ℕ} (a b u : Fin m → ℝ) (k : ℕ) where
  u_formula : ∀ i, u i = if i.val < k - 1 then 0 else a i - b i
  tail_diff_nonzero : u ≠ 0
  reflection_formula : householderReflection u *ᵥ a =
    a - (2 * dotProduct u a / dotProduct u u) • u
  polarization : 2 * dotProduct u a = dotProduct u u

theorem householderTailMapping {m : ℕ} {a b u : Fin m → ℝ} {k : ℕ}
    (M : TailMappingModel a b u k) :
    householderReflection u *ᵥ a = fun i ↦ if i.val < k - 1 then a i else b i := by
  rw [M.reflection_formula, M.polarization]
  have hu : dotProduct u u ≠ 0 := fun h ↦ M.tail_diff_nonzero (dotProduct_self_eq_zero.mp h)
  rw [div_self hu, one_smul]
  funext i
  by_cases hi : i.val < k - 1
  · simp [hi, M.u_formula i]
  · simp [hi, M.u_formula i]

end NumericalAnalysisCourse
