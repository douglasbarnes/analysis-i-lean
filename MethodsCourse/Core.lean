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

def FiniteBasis.IsOrthogonal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {n : ℕ} (b : FiniteBasis (V := V) n) : Prop :=
  ∀ i j, i ≠ j → inner ℂ (b.vectors i) (b.vectors j) = 0

def FiniteBasis.IsOrthonormal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {n : ℕ} (b : FiniteBasis (V := V) n) : Prop :=
  b.IsOrthogonal ∧ ∀ i, inner ℂ (b.vectors i) (b.vectors i) = 1

def FiniteBasis.dimension {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {n : ℕ} (_b : FiniteBasis (V := V) n) : ℕ := n

-- Source line 164: Homogeneous boundary conditions.
def IsHomogeneousBoundary {X : Type*} (P : (X → ℂ) → Prop) : Prop :=
  ∀ f g, P f → P g → ∀ a b : ℂ, P (fun x => a * f x + b * g x)

-- Source line 173: Periodic function.
def IsPeriodic (f : ℝ → ℂ) : Prop := ∃ R : ℝ, R ≠ 0 ∧ ∀ x, f (x + R) = f x

-- Source line 354: Parseval's theorem.
theorem parseval_theorem {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b))) :
    HasSum (fun n : ℤ => ‖fourierCoeffOn hab f n‖ ^ 2)
      ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2) :=
  hasSum_sq_fourierCoeffOn hab hf

-- Source line 404: Adjoint and self-adjoint.
structure AdjointPair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A B : V →ₗ[ℂ] V) : Prop where
  adjoint_identity : ∀ u v, inner ℂ (B u) v = inner ℂ u (A v)

def IsSelfAdjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →ₗ[ℂ] V) : Prop := AdjointPair A A

-- Source line 500: Inner product with weight.
def AdmissibleWeight {X : Type*} (w : X → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ Set.Finite {x | w x = 0}

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
  exact hT.orthogonalFamily_eigenspaces hμν ⟨u, hu⟩ ⟨v, hv⟩

-- Source line 547: compact self-adjoint spectral theorem.  Mathlib's
-- compact-operator theorem gives completeness of the eigenspaces and finite
-- multiplicity of every nonzero eigenvalue, the precise functional-analytic
-- content behind the notes' phrase “countable and discrete”.
theorem compact_sturm_liouville_discrete
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {T : E →L[ℂ] E} (hcompact : IsCompactOperator T)
    (hsymmetric : (T : E →ₗ[ℂ] E).IsSymmetric) :
    (⨆ μ : ℂ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ = ⊥ ∧
      ∀ μ : ℂ, μ ≠ 0 →
        FiniteDimensional ℂ (Module.End.eigenspace (T : E →ₗ[ℂ] E) μ) := by
  constructor
  · exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hcompact hsymmetric
  · intro μ hμ
    exact ContinuousLinearMap.finite_dimensional_eigenspace hcompact μ hμ

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

-- Source line 738: existence and uniqueness for an invertible Dirichlet problem.
theorem dirichlet_problem_exists_unique {X B : Type*}
    (problem : (X → ℂ) ≃ₗ[ℂ] ((X → ℂ) × (B → ℂ))) (boundary : B → ℂ) :
    ∃! φ : X → ℂ, problem φ = (0, boundary) := by
  refine ⟨problem.symm (0, boundary), problem.apply_symm_apply _, ?_⟩
  intro ψ hψ
  apply problem.injective
  rw [hψ, problem.apply_symm_apply]

-- Source line 1195: Heat equation.
def SatisfiesHeatEquation {X : Type*} (timeDerivative laplacian :
    (X → ℝ → ℂ) → X → ℝ → ℂ) (κ : ℝ) (φ : X → ℝ → ℂ) : Prop :=
  0 < κ ∧ timeDerivative φ = fun x t => κ * laplacian φ x t

-- Source line 1345: uniqueness for the heat equation via the energy estimate.
theorem heat_equation_unique {X : Type*} (φ ψ : X → ℝ → ℂ)
    (energy : ℝ → ℝ)
    (energy_nonnegative : ∀ t, 0 ≤ energy t)
    (energy_nonincreasing : ∀ t, energy t ≤ energy 0)
    (initial_energy_zero : energy 0 = 0)
    (zero_energy_pointwise : ∀ t, energy t = 0 → ∀ x, φ x t = ψ x t) :
    φ = ψ := by
  funext x t
  apply zero_energy_pointwise t
  apply le_antisymm
  · simpa [initial_energy_zero] using energy_nonincreasing t
  · exact energy_nonnegative t

-- Source line 1635: energy conservation for the wave equation.
theorem wave_energy_conservation (E flux : ℝ → ℝ)
    (energy_flux_identity : ∀ s t, E t - E s = ∫ x in s..t, flux x)
    (no_boundary_flux : flux = 0) : ∀ s t, E t = E s := by
  intro s t
  have h := energy_flux_identity s t
  rw [no_boundary_flux] at h
  simp at h
  linarith

-- Source line 1654: uniqueness for the wave equation by conserved difference energy.
theorem wave_equation_unique {X : Type*} (φ ψ : X → ℝ → ℂ)
    (differenceEnergy : ℝ → ℝ)
    (energy_nonnegative : ∀ t, 0 ≤ differenceEnergy t)
    (energy_conserved : ∀ t, differenceEnergy t = differenceEnergy 0)
    (cauchy_energy_zero : differenceEnergy 0 = 0)
    (zero_energy_pointwise : ∀ t, differenceEnergy t = 0 → ∀ x, φ x t = ψ x t) :
    φ = ψ := by
  funext x t
  apply zero_energy_pointwise t
  rw [energy_conserved, cauchy_energy_zero]

-- Source line 1774: Dirac delta.
def diracDelta {X : Type*} [Zero X] (φ : X → ℂ) : ℂ := φ 0

-- Source line 2120: Fourier transform.
def fourierTransform (f : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * k * x) * f x

-- Source line 2334: Parseval/Plancherel for the Fourier transform.
structure FourierPlancherelModel
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  transform : E ≃ₗᵢ[ℂ] F

theorem fourier_transform_parseval
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (fourier : FourierPlancherelModel E F) (f g : E) :
    inner ℂ (fourier.transform f) (fourier.transform g) = inner ℂ f g :=
  fourier.transform.inner_map_map f g

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
structure GreenCalculus (X B VectorField : Type*) where
  volume : (X → ℝ) →ₗ[ℝ] ℝ
  boundary : (B → ℝ) →ₗ[ℝ] ℝ
  laplacian : (X → ℝ) → X → ℝ
  gradientProduct : (X → ℝ) → (X → ℝ) → X → ℝ
  trace : (X → ℝ) → B → ℝ
  normalDerivative : (X → ℝ) → B → ℝ
  productGradient : (X → ℝ) → (X → ℝ) → VectorField
  divergence : VectorField → X → ℝ
  normalFlux : VectorField → B → ℝ
  gradient_symm : ∀ φ ψ, gradientProduct φ ψ = gradientProduct ψ φ
  product_rule : ∀ φ ψ, divergence (productGradient φ ψ) =
    fun x => φ x * laplacian ψ x + gradientProduct φ ψ x
  boundary_product_rule : ∀ φ ψ, normalFlux (productGradient φ ψ) =
    fun z => trace φ z * normalDerivative ψ z
  divergence_theorem : ∀ field, boundary (normalFlux field) = volume (divergence field)

-- Source line 3454: Green's first identity.
theorem greens_first_identity {X B VectorField : Type*}
    (G : GreenCalculus X B VectorField) (φ ψ : X → ℝ) :
    G.boundary (fun z => G.trace φ z * G.normalDerivative ψ z) =
      G.volume (fun x => φ x * G.laplacian ψ x + G.gradientProduct φ ψ x) := by
  rw [← G.boundary_product_rule φ ψ, ← G.product_rule φ ψ]
  exact G.divergence_theorem (G.productGradient φ ψ)

-- Source line 3466: Green's second identity.
theorem greens_second_identity {X B VectorField : Type*} (G : GreenCalculus X B VectorField) (φ ψ : X → ℝ) :
    G.volume (fun x => φ x * G.laplacian ψ x - ψ x * G.laplacian φ x) =
      G.boundary (fun z => G.trace φ z * G.normalDerivative ψ z -
        G.trace ψ z * G.normalDerivative φ z) := by
  have hv :
      G.volume (fun x => φ x * G.laplacian ψ x - ψ x * G.laplacian φ x) =
        G.volume (fun x => φ x * G.laplacian ψ x) -
          G.volume (fun x => ψ x * G.laplacian φ x) := by
    simpa only [Pi.sub_apply] using
      G.volume.map_sub (fun x => φ x * G.laplacian ψ x)
        (fun x => ψ x * G.laplacian φ x)
  have hb :
      G.boundary (fun z => G.trace φ z * G.normalDerivative ψ z -
          G.trace ψ z * G.normalDerivative φ z) =
        G.boundary (fun z => G.trace φ z * G.normalDerivative ψ z) -
          G.boundary (fun z => G.trace ψ z * G.normalDerivative φ z) := by
    simpa only [Pi.sub_apply] using
      G.boundary.map_sub (fun z => G.trace φ z * G.normalDerivative ψ z)
        (fun z => G.trace ψ z * G.normalDerivative φ z)
  rw [hv, hb]
  rw [greens_first_identity G φ ψ, greens_first_identity G ψ φ]
  have ha :
      G.volume (fun x => φ x * G.laplacian ψ x + G.gradientProduct φ ψ x) =
        G.volume (fun x => φ x * G.laplacian ψ x) +
          G.volume (G.gradientProduct φ ψ) := by
    simpa only [Pi.add_apply] using
      G.volume.map_add (fun x => φ x * G.laplacian ψ x) (G.gradientProduct φ ψ)
  have hb' :
      G.volume (fun x => ψ x * G.laplacian φ x + G.gradientProduct ψ φ x) =
        G.volume (fun x => ψ x * G.laplacian φ x) +
          G.volume (G.gradientProduct ψ φ) := by
    simpa only [Pi.add_apply] using
      G.volume.map_add (fun x => ψ x * G.laplacian φ x) (G.gradientProduct ψ φ)
  rw [ha, hb']
  rw [G.gradient_symm φ ψ]
  ring

-- Source line 3506: Green's third identity.
theorem greens_third_identity {X B VectorField : Type*} (G : GreenCalculus X B VectorField)
    (φ kernel F delta : X → ℝ) (y : X)
    (hφ : G.laplacian φ = fun x => -F x)
    (hkernel : G.laplacian kernel = delta)
    (hreproduce : G.volume (fun x => φ x * delta x) = φ y) :
    φ y = G.boundary (fun z => G.trace φ z * G.normalDerivative kernel z -
      G.trace kernel z * G.normalDerivative φ z) -
      G.volume (fun x => kernel x * F x) := by
  have h := greens_second_identity G φ kernel
  rw [hφ, hkernel] at h
  simp only [mul_neg, sub_neg_eq_add] at h
  have hv :
      G.volume (fun x => φ x * delta x + kernel x * F x) =
        G.volume (fun x => φ x * delta x) + G.volume (fun x => kernel x * F x) := by
    simpa only [Pi.add_apply] using
      G.volume.map_add (fun x => φ x * delta x) (fun x => kernel x * F x)
  rw [hv, hreproduce] at h
  linarith

end MethodsCourse
