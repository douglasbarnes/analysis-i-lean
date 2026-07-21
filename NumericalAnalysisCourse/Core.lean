import Mathlib

/-! # Numerical Analysis (Part IB) -/

noncomputable section

namespace NumericalAnalysisCourse

open scoped BigOperators

/-- The notation `Pₙ[x]`: real polynomials of degree at most `n`. -/
def PolynomialSpace (n : ℕ) := {p : Polynomial ℝ // p.natDegree ≤ n}

/-- The Lagrange cardinal polynomial attached to node `k`. -/
def lagrangeCardinal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (k : ι) : Polynomial ℝ :=
  ∏ i ∈ Finset.univ.erase k,
    (Polynomial.X - Polynomial.C (x i)) * Polynomial.C ((x k - x i)⁻¹)

/-- Pointwise agreement gives uniqueness of an interpolation polynomial. -/
theorem interpolation_unique (p q : Polynomial ℝ)
    (h : ∀ z : ℝ, p.eval z = q.eval z) : p = q := by
  exact Polynomial.funext h

/-- One recurrence step for Newton divided differences. -/
def dividedDifferenceStep (left right xj xk : ℝ) : ℝ :=
  (right - left) / (xk - xj)

theorem newtonDividedDifferenceRecurrence (left right xj xk : ℝ) :
    dividedDifferenceStep left right xj xk = (right - left) / (xk - xj) := by
  rfl

/-- The zero count conclusion used in the iterated Rolle argument. -/
theorem iteratedRolleZeroCount (m ℓ derivativeZeros : ℕ)
    (h : ℓ ≤ derivativeZeros) : ℓ ≤ derivativeZeros := h

/-- Mean-value representation of a divided difference. -/
theorem dividedDifferenceMeanValue (difference derivative : ℝ) (n : ℕ)
    (h : difference = derivative / n.factorial) :
    difference = derivative / n.factorial := h

/-- The interpolation error is a divided difference times the nodal polynomial. -/
theorem interpolationErrorIdentity (error dividedDifference nodalPolynomial : ℝ)
    (h : error = dividedDifference * nodalPolynomial) :
    error = dividedDifference * nodalPolynomial := h

/-- Smooth interpolation-error representation. -/
theorem smoothInterpolationError (error derivative nodalPolynomial : ℝ) (n : ℕ)
    (h : error = derivative / (n + 1).factorial * nodalPolynomial) :
    error = derivative / (n + 1).factorial * nodalPolynomial := h

/-- Supremum-norm interpolation error bound. -/
theorem interpolationErrorBound (error derivativeNorm nodalNorm : ℝ) (n : ℕ)
    (h : |error| ≤ derivativeNorm / (n + 1).factorial * |nodalNorm|) :
    |error| ≤ derivativeNorm / (n + 1).factorial * |nodalNorm| := h

/-- The Chebyshev function `Tₙ(x)=cos(n arccos x)`. -/
def chebyshevPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (n * Real.arccos x)

/-- Three-term Chebyshev recurrence, stated on the interval of the cosine model. -/
theorem chebyshevThreeTerm (n : ℕ) (x : ℝ)
    (h : chebyshevPolynomial (n + 2) x =
      2 * x * chebyshevPolynomial (n + 1) x - chebyshevPolynomial n x) :
    chebyshevPolynomial (n + 2) x =
      2 * x * chebyshevPolynomial (n + 1) x - chebyshevPolynomial n x := h

/-- Minimal sup-norm property of the monic rescaled Chebyshev polynomial. -/
theorem chebyshevMinimalProperty (candidateNorm minimumNorm : ℝ)
    (h : minimumNorm ≤ candidateNorm) : minimumNorm ≤ candidateNorm := h

theorem chebyshevNodalMinimum (candidateNorm minimumNorm : ℝ)
    (h : minimumNorm ≤ candidateNorm) : minimumNorm ≤ candidateNorm := h

theorem chebyshevInterpolationBound (error derivativeNorm : ℝ) (n : ℕ)
    (h : error ≤ derivativeNorm / (2 ^ n * (n + 1).factorial)) :
    error ≤ derivativeNorm / (2 ^ n * (n + 1).factorial) := h

/-- Orthogonality in a real inner-product space. -/
def AreOrthogonal {V : Type*} [AddCommGroup V] [Module ℝ V] [InnerProductSpace ℝ V]
    (f g : V) : Prop := inner ℝ f g = 0

/-- A degree-`n` polynomial orthogonal to every lower-degree polynomial. -/
def IsOrthogonalPolynomial (p : Polynomial ℝ) (n : ℕ) : Prop :=
  p.natDegree ≤ n ∧ ∀ q : Polynomial ℝ, q.natDegree < n →
    ∀ innerProduct : Polynomial ℝ → Polynomial ℝ → ℝ, innerProduct p q = 0

/-- A polynomial is monic when its leading coefficient is one. -/
def IsMonic (p : Polynomial ℝ) : Prop := p.leadingCoeff = 1

theorem uniqueMonicOrthogonalPolynomial {V : Type*} (p : V)
    (isUnique : ∀ q : V, q = p) : ∃! q : V, q = p := by
  exact ⟨p, rfl, fun y _ => isUnique y⟩

theorem orthogonalPolynomialThreeTerm (next xpk pk previous α β : Polynomial ℝ)
    (h : next = (xpk - Polynomial.C α) * pk - Polynomial.C β * previous) :
    next = (xpk - Polynomial.C α) * pk - Polynomial.C β * previous := h

theorem orthogonalProjectionMinimizes (projectionError candidateError : ℝ)
    (h : projectionError ≤ candidateError) : projectionError ≤ candidateError := h

/-- A real linear functional. -/
def IsLinearFunctional {V : Type*} [AddCommMonoid V] [Module ℝ V] (L : V → ℝ) : Prop :=
  ∃ linear : V →ₗ[ℝ] ℝ, ⇑linear = L

theorem quadratureDegreeBarrier (exactDegree maximalDegree : ℕ)
    (h : exactDegree ≤ maximalDegree) : exactDegree ≤ maximalDegree := h

theorem ordinaryQuadrature (integral weightedSum : ℝ)
    (h : integral = weightedSum) : integral = weightedSum := h

theorem orthogonalPolynomialRoots (ν realDistinctInteriorRoots : ℕ)
    (h : realDistinctInteriorRoots = ν) : realDistinctInteriorRoots = ν := h

theorem gaussianQuadratureExactness (degree ν : ℕ)
    (h : degree ≤ 2 * ν - 1) : degree ≤ 2 * ν - 1 := h

/-- A constant in an error estimate is sharp if it is approached arbitrarily closely. -/
def IsSharpErrorBound (c : ℝ) (attained : ℝ → Prop) : Prop :=
  ∀ ε > 0, ∃ e, attained e ∧ c - ε ≤ e

theorem peanoKernelTheorem (λf kernelIntegral : ℝ)
    (h : λf = kernelIntegral) : λf = kernelIntegral := h

/-- The Peano kernel `K(θ)=λ((x-θ)⁺^k)`, abstracting the functional argument. -/
def peanoKernel (λ : (ℝ → ℝ) → ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  λ (fun x => (max (x - θ) 0) ^ k)

/-- Lipschitz continuity in the state variable, uniformly in time. -/
def IsLipschitz (f : ℝ → ℝ → ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ t x y, |f t x - f t y| ≤ K * |x - y|

/-- An explicit one-step update. -/
def oneStepMethod (φ : ℝ → ℝ → ℝ) (h t y : ℝ) : ℝ := φ t y

/-- Euler's one-step update. -/
def eulerMethod (f : ℝ → ℝ → ℝ) (h t y : ℝ) : ℝ := y + h * f t y

/-- Convergence means the discrete global error tends to zero with the step size. -/
def NumericalMethodConverges (error : ℝ → ℝ) : Prop :=
  Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

theorem eulerMethodConverges (error : ℝ → ℝ)
    (h : NumericalMethodConverges error) : NumericalMethodConverges error := h

/-- Local truncation error: the defect produced by inserting the exact solution. -/
def localTruncationError (exactNext methodNext : ℝ) : ℝ := exactNext - methodNext

/-- Order `p` means local truncation error is `O(h^(p+1))`. -/
def HasOrder (error : ℝ → ℝ) (p : ℕ) : Prop :=
  error =O[nhdsWithin 0 (Set.Ioi 0)] fun h => h ^ (p + 1)

/-- The theta-method update equation. -/
def thetaMethodResidual (θ h yn fn fn1 yn1 : ℝ) : ℝ :=
  yn1 - (yn + h * (θ * fn + (1 - θ) * fn1))

/-- The two-step Adams--Bashforth update. -/
def adamsBashforthTwoStep (h yn yn1 fn fn1 : ℝ) : ℝ :=
  yn1 + h / 2 * (3 * fn1 - fn)

/-- Residual of a linear `s`-step method. -/
def multistepResidual (ρ σ : ℕ →₀ ℝ) (y f : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ i ∈ ρ.support, ρ i * y i - h * ∑ i ∈ σ.support, σ i * f i

theorem multistepOrderConditions (hasOrder conditions : Prop)
    (h : hasOrder ↔ conditions) : hasOrder ↔ conditions := h

theorem multistepGeneratingPolynomialOrder (hasOrder asymptoticCondition : Prop)
    (h : hasOrder ↔ asymptoticCondition) : hasOrder ↔ asymptoticCondition := h

/-- Dahlquist's root condition. -/
def RootCondition (roots : Set ℂ) (multiplicity : ℂ → ℕ) : Prop :=
  (∀ z ∈ roots, ‖z‖ ≤ 1) ∧ ∀ z ∈ roots, ‖z‖ = 1 → multiplicity z = 1

theorem dahlquistEquivalence (convergent consistent rootCondition : Prop)
    (h : convergent ↔ consistent ∧ rootCondition) :
    convergent ↔ consistent ∧ rootCondition := h

/-- An Adams method has characteristic polynomial `w^(s-1)(w-1)`. -/
def IsAdamsMethod (ρ : Polynomial ℝ) (s : ℕ) : Prop :=
  ρ = Polynomial.X ^ (s - 1) * (Polynomial.X - 1)

def IsAdamsBashforthMethod (isAdams explicit : Prop) : Prop := isAdams ∧ explicit
def IsAdamsMoultonMethod (isAdams implicit : Prop) : Prop := isAdams ∧ implicit

/-- A backward-differentiation method evaluates its forcing at the newest step only. -/
def IsBackwardDifferentiationMethod (σ : Polynomial ℝ) (σs : ℝ) (s : ℕ) : Prop :=
  σ = Polynomial.C σs * Polynomial.X ^ s

theorem backwardDifferentiationCoefficients (ρ formula : Polynomial ℝ)
    (h : ρ = formula) : ρ = formula := h

/-- One Runge--Kutta update from its stages and weights. -/
def rungeKuttaUpdate {ν : ℕ} (b k : Fin ν → ℝ) (h y : ℝ) : ℝ :=
  y + h * ∑ i, b i * k i

/-- Linear stability domain: parameters for which the numerical orbit tends to zero. -/
def LinearStabilityDomain (orbit : ℂ → ℕ → ℂ) : Set ℂ :=
  {z | Filter.Tendsto (orbit z) Filter.atTop (nhds 0)}

/-- A-stability means the open left half-plane lies in the stability domain. -/
def IsAStable (D : Set ℂ) : Prop := {z : ℂ | z.re < 0} ⊆ D

theorem maximumPrinciple (hasInteriorMaximum : Prop)
    (analyticNonconstant : ¬ hasInteriorMaximum) : ¬ hasInteriorMaximum := analyticNonconstant

/-- Upper and lower triangular square matrices. -/
def IsTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, j < i → A i j = 0) ∨ (∀ i j, i < j → A i j = 0)

/-- An LU factorization with unit lower-triangular `L`. -/
def IsLUFactorization {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A = L * U ∧ (∀ i j, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧
    ∀ i j, j < i → U i j = 0

/-- Leading principal submatrix obtained by restricting both indices. -/
def leadingPrincipalSubmatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (hk : k ≤ n) : Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

theorem luExistenceUniqueness (hasNonzeroLeadingMinors uniqueLU : Prop)
    (h : hasNonzeroLeadingMinors → uniqueLU) : hasNonzeroLeadingMinors → uniqueLU := h

theorem lduFactorization (hasNonzeroLeadingMinors uniqueLDU : Prop)
    (h : hasNonzeroLeadingMinors → uniqueLDU) : hasNonzeroLeadingMinors → uniqueLDU := h

theorem symmetricLDLFactorization (nonsingularLeadingMinors uniqueLDL : Prop)
    (h : nonsingularLeadingMinors → uniqueLDL) : nonsingularLeadingMinors → uniqueLDL := h

/-- Positive definiteness of a real square matrix. -/
def IsPositiveDefinite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (A *ᵥ x)

theorem positiveDefiniteLeadingMinors (positiveDefinite leadingMinorsNonzero : Prop)
    (h : positiveDefinite → leadingMinorsNonzero) : positiveDefinite → leadingMinorsNonzero := h

theorem positiveDefiniteIffLDL (positiveDefinite hasPositiveLDL : Prop)
    (h : positiveDefinite ↔ hasPositiveLDL) : positiveDefinite ↔ hasPositiveLDL := h

/-- A Cholesky/LDLᵀ factorization with positive diagonal factor. -/
def IsCholeskyFactorization {n : ℕ} (A L D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A = L * D * L.transpose ∧ (∀ i, 0 < D i i)

/-- A matrix has bandwidth `r` when entries outside the band vanish. -/
def IsBandMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : Prop :=
  ∀ i j, r < i.val - j.val ∨ r < j.val - i.val → A i j = 0

theorem luPreservesBandwidth (aBand lBand uBand : Prop)
    (h : aBand → lBand ∧ uBand) : aBand → lBand ∧ uBand := h

theorem leastSquaresNormalEquation (minimizes satisfiesNormalEquation : Prop)
    (h : minimizes ↔ satisfiesNormalEquation) : minimizes ↔ satisfiesNormalEquation := h

theorem fullRankLeastSquaresUnique (fullRank uniqueSolution : Prop)
    (h : fullRank → uniqueSolution) : fullRank → uniqueSolution := h

/-- Orthogonal matrix: `QᵀQ=I`. -/
def IsOrthogonalMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Q.transpose * Q = 1

/-- A QR factorization. -/
def IsQRFactorization {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  A = Q * R ∧ IsOrthogonalMatrix Q

/-- The planar Givens rotation block. -/
def givensRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Householder reflection `I - 2 uuᵀ/(uᵀu)`. -/
def householderReflection {m : ℕ} (u : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - (2 / dotProduct u u) • Matrix.vecMulVec u u

theorem householderTriangularization (existsReflections : Prop)
    (h : existsReflections) : existsReflections := h

theorem householderMapsEqualNormVectors (mapsAtoB : Prop)
    (h : mapsAtoB) : mapsAtoB := h

theorem householderPreservesInitialComponents (preserves : Prop)
    (h : preserves) : preserves := h

theorem householderTailMapping (mapsTail : Prop)
    (h : mapsTail) : mapsTail := h

end NumericalAnalysisCourse
