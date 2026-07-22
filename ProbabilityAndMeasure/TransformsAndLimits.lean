import ProbabilityAndMeasure.FunctionSpaces

/-!
# Probability and Measure: transforms, Gaussian laws, ergodic theory, and limit theorems

Definitions used in the final chapters of the notes.  Mathlib witnesses for Fourier inversion,
characteristic-function uniqueness, laws of large numbers, and the central limit theorem are
collected in `LibraryCoverage.lean`.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory Function

namespace ProbabilityAndMeasure

/-- Fourier transform of an integrable complex-valued function on `ℝ`. -/
def fourierTransform (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (Complex.I * (((u * x : ℝ) : ℂ)))

/-- Characteristic function of a real random variable. -/
def characteristicFunction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (u : ℝ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (((u * X ω : ℝ) : ℂ))) ∂P

/-- Convolution of two measures on the real line. -/
def measureConvolution (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun z : ℝ × ℝ ↦ z.1 + z.2)

/-- Convolution of a function with a finite measure. -/
def functionMeasureConvolution (f : ℝ → ℂ) (ν : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) ∂ν

/-- The real Gaussian density with mean `m` and standard deviation `σ`. -/
def gaussianDensity (m σ x : ℝ) : ℝ :=
  (1 / (Real.sqrt (2 * Real.pi) * σ)) *
    Real.exp (-((x - m) ^ 2) / (2 * σ ^ 2))

/-- A real random variable is Gaussian when it has the corresponding density, including
    the degenerate constant case. -/
def IsGaussianReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∃ m : ℝ, ∀ᵐ ω ∂P, X ω = m) ∨
    ∃ m σ : ℝ, 0 < σ ∧
      P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianDensity m σ x))

/-- A vector is Gaussian when every real linear functional of it is Gaussian. -/
def IsGaussianVector {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (X : Ω → E) : Prop :=
  ∀ L : E →L[ℝ] ℝ, IsGaussianReal P (fun ω ↦ L (X ω))

/-- Weak convergence of finite measures, tested against bounded continuous real functions. -/
def WeaklyConverges {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    (μ : ℕ → Measure α) (ν : Measure α) : Prop :=
  ∀ f : α → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
    Tendsto (fun n ↦ ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- A measurable transformation preserving a measure. -/
def IsMeasurePreserving {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → α) : Prop :=
  MeasurePreserving T μ μ

/-- Invariance of an event. -/
def InvariantSet {α : Type*} (T : α → α) (A : Set α) : Prop :=
  T ⁻¹' A = A

/-- Invariance of a function. -/
def InvariantFunction {α E : Type*} (T : α → α) (f : α → E) : Prop :=
  f ∘ T = f

/-- Ergodicity: every measurable invariant event is trivial modulo the measure. -/
def IsErgodic {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → α) : Prop :=
  ∀ A : Set α, MeasurableSet A → InvariantSet T A → μ A = 0 ∨ μ Aᶜ = 0

/-- The `n`th ergodic average. -/
def ergodicAverage {α : Type*} (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  (∑ k ∈ Finset.range n, f ((T^[k]) x)) / n

/-- Partial sums of a sequence of real random variables. -/
def partialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, X k ω

/-- Identically distributed random variables have equal pushforward laws. -/
def IdenticallyDistributed {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (X : ℕ → Ω → S) : Prop :=
  ∀ n, P.map (X n) = P.map (X 0)

/-- Independent and identically distributed. -/
def IID {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (X : ℕ → Ω → S) : Prop :=
  ProbabilityTheory.iIndepFun X P ∧ IdenticallyDistributed P X

/-- The algebraic normalization used by the central limit theorem. -/
def cltNormalization {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹.sqrt * partialSum X n ω

end ProbabilityAndMeasure
