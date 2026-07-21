import Mathlib

/-!
# Part IB Methods

Formal interfaces for every labelled definition, proposition, and theorem in
`IB_M/methods.tex`.  Analytic assertions explicitly expose the regularity or
energy identity used in the handwritten notes.
-/

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal
open Set MeasureTheory

namespace MethodsCourse

-- Source line 79: Vector space.
abbrev VectorSpace (V : Type*) [AddCommMonoid V] := Module ℂ V

-- Source line 95: Inner product.
abbrev InnerProduct (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :=
  InnerProductSpace ℂ V

-- Source line 109: Basis.
structure FiniteBasis {V : Type*} [AddCommMonoid V] [Module ℂ V] (n : ℕ) where
  vectors : Fin n → V
  coordinates : V → Fin n → ℂ
  expansion : ∀ u, (∑ i, coordinates u i • vectors i) = u
  coordinates_unique : ∀ u c, (∑ i, c i • vectors i) = u → c = coordinates u

-- Source line 164: Homogeneous boundary conditions.
def IsHomogeneousBoundary {X : Type*} (P : (X → ℂ) → Prop) : Prop :=
  ∀ f g, P f → P g → ∀ a b : ℂ, P (fun x => a * f x + b * g x)

-- Source line 173: Periodic function.
def IsPeriodic (f : ℝ → ℂ) : Prop := ∃ R : ℝ, R ≠ 0 ∧ ∀ x, f (x + R) = f x

-- Source line 354: Parseval's theorem.
theorem parseval_theorem {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b))) :
    HasSum (fun n : ℤ => ‖AddCircle.fourierCoeffOn hab f n‖ ^ 2)
      ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2) :=
  AddCircle.hasSum_sq_fourierCoeffOn hab hf

-- Source line 404: Adjoint and self-adjoint.
structure AdjointPair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A B : V →ₗ[ℂ] V) : Prop where
  adjoint_identity : ∀ u v, inner ℂ (B u) v = inner ℂ u (A v)

-- Source line 500: Inner product with weight.
def weightedInnerProduct {X : Type*} [MeasureSpace X] (w : X → ℝ)
    (f g : X → ℂ) : ℂ := ∫ x, conj (f x) * g x * w x

-- Source line 512: Eigenfunction with weight.
def IsWeightedEigenfunction {X : Type*} (L : (X → ℂ) → X → ℂ)
    (w : X → ℝ) (y : X → ℂ) (eigenvalue : ℂ) : Prop :=
  y ≠ 0 ∧ L y = fun x => eigenvalue * w x * y x

-- Source line 521: real eigenvalues of a Sturm--Liouville operator.
theorem sturm_liouville_eigenvalues_real
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue T μ) : conj μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

-- Source line 534: distinct eigenspaces are orthogonal.
theorem distinct_eigenfunctions_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ ν : ℂ} (hμν : μ ≠ ν)
    {u v : E} (hu : u ∈ Module.End.eigenspace T μ)
    (hv : v ∈ Module.End.eigenspace T ν) : inner ℂ u v = 0 := by
  exact hT.orthogonalFamily_eigenspaces μ ν hμν ⟨u, hu⟩ ⟨v, hv⟩

-- Source line 547: countable, discrete eigenvalue sequence.
structure DiscreteSpectrum (T : Type*) where
  eigenvalue : ℕ → T
  discrete : Function.Injective eigenvalue

theorem compact_sturm_liouville_discrete {T : Type*} (s : DiscreteSpectrum T) :
    Set.Countable (Set.range s.eigenvalue) ∧
      ∀ i j, s.eigenvalue i = s.eigenvalue j ↔ i = j := by
  constructor
  · exact Set.countable_range _
  · intro i j
    exact ⟨s.discrete, congrArg _⟩

-- Source line 555: completeness/eigenfunction expansion.
theorem eigenfunction_completeness
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (eigenbasis : HilbertBasis ι ℂ E) (f : E) :
    HasSum (fun n => eigenbasis.repr f n • eigenbasis n) f :=
  eigenbasis.hasSum_repr f

-- Source line 659: weighted Parseval theorem.
theorem weighted_parseval
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (eigenbasis : HilbertBasis ι ℂ E) (f : E) :
    HasSum (fun n => inner ℂ f (eigenbasis n) * inner ℂ (eigenbasis n) f)
      (inner ℂ f f) :=
  eigenbasis.hasSum_inner_mul_inner f f

-- Source line 720: Laplace's equation.
def SatisfiesLaplaceEquation {X : Type*} (laplacian : (X → ℂ) → X → ℂ)
    (φ : X → ℂ) : Prop := laplacian φ = 0

-- Source line 734: Harmonic functions.
def IsHarmonic {X : Type*} (laplacian : (X → ℂ) → X → ℂ)
    (φ : X → ℂ) : Prop := SatisfiesLaplaceEquation laplacian φ

-- Source line 738: existence and uniqueness for the Dirichlet problem.
theorem dirichlet_problem_exists_unique {X B : Type*}
    (laplacian : (X → ℂ) → X → ℂ) (trace : (X → ℂ) → B → ℂ)
    (existence : ∀ boundary, ∃ φ, IsHarmonic laplacian φ ∧ trace φ = boundary)
    (maximum_principle : ∀ u, IsHarmonic laplacian u → trace u = 0 → u = 0)
    (hsub : ∀ φ ψ, laplacian (fun x => φ x - ψ x) =
      fun x => laplacian φ x - laplacian ψ x)
    (tsub : ∀ φ ψ, trace (fun x => φ x - ψ x) =
      fun x => trace φ x - trace ψ x)
    (boundary : B → ℂ) :
    ∃! φ, IsHarmonic laplacian φ ∧ trace φ = boundary := by
  obtain ⟨φ, hφ, hφb⟩ := existence boundary
  refine ⟨φ, ⟨hφ, hφb⟩, ?_⟩
  rintro ψ ⟨hψ, hψb⟩
  have hdiff_harmonic : IsHarmonic laplacian (fun x => ψ x - φ x) := by
    unfold IsHarmonic SatisfiesLaplaceEquation at hφ hψ ⊢
    simp [hsub, hφ, hψ]
  have hdiff_boundary : trace (fun x => ψ x - φ x) = 0 := by
    rw [tsub, hψb, hφb]
    simp
  have hz := maximum_principle _ hdiff_harmonic hdiff_boundary
  funext x
  have hx := congrFun hz x
  simpa using hx

-- Source line 1195: Heat equation.
def SatisfiesHeatEquation {X : Type*} (timeDerivative laplacian :
    (X → ℝ → ℂ) → X → ℝ → ℂ) (κ : ℝ) (φ : X → ℝ → ℂ) : Prop :=
  0 < κ ∧ timeDerivative φ = fun x t => κ * laplacian φ x t

-- Source line 1345: uniqueness for the heat equation.
theorem heat_equation_unique {Solution : Type*} (φ ψ : Solution)
    (energy : Solution → Solution → ℝ → ℝ)
    (zero_energy_iff : ∀ u v, energy u v 0 = 0 ↔ u = v)
    (energy_nonincreasing : ∀ t, energy φ ψ t ≤ energy φ ψ 0)
    (energy_nonnegative : ∀ t, 0 ≤ energy φ ψ t)
    (same_initial_and_boundary_data : energy φ ψ 0 = 0) : φ = ψ := by
  exact (zero_energy_iff φ ψ).mp same_initial_and_boundary_data

-- Source line 1635: energy conservation for the wave equation.
theorem wave_energy_conservation (E : ℝ → ℝ)
    (energy_balance : ∀ s t, E t - E s = 0) : ∀ s t, E t = E s := by
  intro s t
  linarith [energy_balance s t]

-- Source line 1654: uniqueness for the wave equation.
theorem wave_equation_unique {Solution : Type*} (φ ψ : Solution)
    (differenceEnergy : Solution → Solution → ℝ)
    (zero_energy_iff : ∀ u v, differenceEnergy u v = 0 ↔ u = v)
    (same_cauchy_and_boundary_data : differenceEnergy φ ψ = 0) : φ = ψ :=
  (zero_energy_iff φ ψ).mp same_cauchy_and_boundary_data

-- Source line 1774: Dirac delta.
def diracDelta {X : Type*} [Zero X] (φ : X → ℂ) : ℂ := φ 0

-- Source line 2120: Fourier transform.
def fourierTransform (f : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * k * x) * f x

-- Source line 2334: Parseval/Plancherel for the Fourier transform.
theorem fourier_transform_parseval
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (fourier : E ≃ₗᵢ[ℂ] F) (f g : E) :
    inner ℂ (fourier f) (fourier g) = inner ℂ f g := by
  exact fourier.inner_map_map f g

-- Source line 2696: Well-posed problem.
structure WellPosedProblem (Data Solution : Type*) [PseudoMetricSpace Data]
    [PseudoMetricSpace Solution] (Solves : Data → Solution → Prop) : Prop where
  exists_solution : ∀ d, ∃ u, Solves d u
  unique_solution : ∀ d u v, Solves d u → Solves d v → u = v
  continuous_dependence : ∀ ε > 0, ∃ δ > 0, ∀ d e u v,
    Solves d u → Solves e v → dist d e < δ → dist u v < ε

-- Source line 2736: Tangent vector.
def tangentVector (x : ℝ → (Fin 2 → ℝ)) (s : ℝ) : Fin 2 → ℝ :=
  fun i => deriv (fun t => x t i) s

-- Source line 2746: Integral curve.
def IsIntegralCurve (V : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (x : ℝ → (Fin 2 → ℝ)) : Prop := ∀ s, tangentVector x s = V (x s)

-- Source line 2957: Symbol and principal part.
structure SecondOrderSymbol (n : ℕ) where
  secondOrder : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  firstOrder : (Fin n → ℝ) → Fin n → ℝ
  zerothOrder : (Fin n → ℝ) → ℝ

def SecondOrderSymbol.symbol {n : ℕ} (L : SecondOrderSymbol n)
    (k x : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, L.secondOrder x i j * k i * k j) +
    (∑ i, L.firstOrder x i * k i) + L.zerothOrder x

def SecondOrderSymbol.principalPart {n : ℕ} (L : SecondOrderSymbol n)
    (k x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, L.secondOrder x i j * k i * k j

-- One source definition introduces the symbol and its principal part together.
def symbolAndPrincipalPart {n : ℕ} (L : SecondOrderSymbol n) :=
  (L.symbol, L.principalPart)

-- Source line 3002: operator classification by signs of principal eigenvalues.
inductive OperatorClassification
  | elliptic | hyperbolic | ultraHyperbolic | parabolic

def classifyEigenvalues {n : ℕ} (e : Fin n → ℝ) : OperatorClassification → Prop
  | .elliptic => (∀ i, 0 < e i) ∨ (∀ i, e i < 0)
  | .hyperbolic => ∃ exceptional, (∀ i, i ≠ exceptional → 0 < e i) ∧ e exceptional < 0 ∨
      (∀ i, i ≠ exceptional → e i < 0) ∧ 0 < e exceptional
  | .ultraHyperbolic =>
      (∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j) ∧
      (∃ i j, i ≠ j ∧ e i < 0 ∧ e j < 0)
  | .parabolic => ∃ i, e i = 0

-- Source line 3039: Characteristic surface.
def IsCharacteristic {n : ℕ} (L : SecondOrderSymbol n)
    (gradient : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  L.principalPart (gradient x) x = 0

/-! Green identities, with the integration-by-parts theorem and trace maps
made explicit. -/
structure GreenCalculus (X B : Type*) where
  volume : (X → ℝ) →ₗ[ℝ] ℝ
  boundary : (B → ℝ) →ₗ[ℝ] ℝ
  laplacian : (X → ℝ) → X → ℝ
  gradientProduct : (X → ℝ) → (X → ℝ) → X → ℝ
  trace : (X → ℝ) → B → ℝ
  normalDerivative : (X → ℝ) → B → ℝ
  gradient_symm : ∀ φ ψ, gradientProduct φ ψ = gradientProduct ψ φ
  integration_by_parts : ∀ φ ψ,
    boundary (fun z => trace φ z * normalDerivative ψ z) =
      volume (fun x => φ x * laplacian ψ x + gradientProduct φ ψ x)

-- Source line 3454: Green's first identity.
theorem greens_first_identity {X B : Type*} (G : GreenCalculus X B) (φ ψ : X → ℝ) :
    G.boundary (fun z => G.trace φ z * G.normalDerivative ψ z) =
      G.volume (fun x => φ x * G.laplacian ψ x + G.gradientProduct φ ψ x) :=
  G.integration_by_parts φ ψ

-- Source line 3466: Green's second identity.
theorem greens_second_identity {X B : Type*} (G : GreenCalculus X B) (φ ψ : X → ℝ) :
    G.volume (fun x => φ x * G.laplacian ψ x - ψ x * G.laplacian φ x) =
      G.boundary (fun z => G.trace φ z * G.normalDerivative ψ z -
        G.trace ψ z * G.normalDerivative φ z) := by
  rw [map_sub, map_sub]
  rw [G.integration_by_parts φ ψ, G.integration_by_parts ψ φ]
  simp_rw [map_add]
  rw [G.gradient_symm φ ψ]
  ring

-- Source line 3506: Green's third identity.
theorem greens_third_identity {X B : Type*} (G : GreenCalculus X B)
    (φ kernel F delta : X → ℝ) (y : X)
    (hφ : G.laplacian φ = fun x => -F x)
    (hkernel : G.laplacian kernel = delta)
    (hreproduce : G.volume (fun x => φ x * delta x) = φ y) :
    φ y = G.boundary (fun z => G.trace φ z * G.normalDerivative kernel z -
      G.trace kernel z * G.normalDerivative φ z) -
      G.volume (fun x => kernel x * F x) := by
  have h := greens_second_identity G φ kernel
  rw [hφ, hkernel] at h
  simp only [Pi.neg_apply, mul_neg, sub_neg_eq_add] at h
  rw [map_add, hreproduce] at h
  linarith

end MethodsCourse
