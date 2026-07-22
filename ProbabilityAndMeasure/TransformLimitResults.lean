import ProbabilityAndMeasure.FunctionalAnalysisResults
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# Probability and Measure: transforms, Gaussian laws, ergodic averages, and limit theorems
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology FourierTransform RealInnerProductSpace
open Set Filter MeasureTheory ProbabilityTheory Finset Function

namespace ProbabilityAndMeasure

/-! ## Fourier transforms and characteristic functions -/

/-- Source lines 3287--3291: the characteristic function of a finite measure is bounded by its
mass. -/
theorem characteristic_function_bound_source {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure E) (t : E) :
    ‖MeasureTheory.charFun μ t‖ ≤ μ.real Set.univ :=
  MeasureTheory.norm_charFun_le t

/-- Source lines 3294--3296: the characteristic function is measurable (indeed continuous under
the usual finite-measure hypotheses). -/
theorem characteristic_function_measurable_source {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ : Measure E) [SFinite μ] : Measurable (MeasureTheory.charFun μ) :=
  MeasureTheory.measurable_charFun

/-- Source lines 3356--3359 and 3376--3381: the characteristic function of a convolution is the
product of the characteristic functions. -/
theorem characteristic_function_convolution_source {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    MeasureTheory.charFun (μ ∗ ν) t =
      MeasureTheory.charFun μ t * MeasureTheory.charFun ν t :=
  MeasureTheory.charFun_conv t

/-- Source lines 3392--3397 and 3557--3563: Fourier inversion in Mathlib's normalized Fourier
convention. -/
theorem fourier_inversion_source {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : V → E} (hf : Integrable f) (hF : Integrable (𝓕 f))
    {v : V} (hv : ContinuousAt f v) :
    𝓕⁻ (𝓕 f) v = f v :=
  hf.fourierInv_fourier_eq hF hv

/-- Source lines 3640--3645, Plancherel's identity for the `L²` Fourier transform. -/
theorem plancherel_source {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : MeasureTheory.Lp F 2 (volume : Measure E)) :
    ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- Source lines 3683--3688: the Fourier transform on `L²` is a linear isometric equivalence. -/
noncomputable def fourier_l2_equiv_source {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    (MeasureTheory.Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℂ]
      (MeasureTheory.Lp F 2 (volume : Measure E)) :=
  MeasureTheory.Lp.fourierTransformₗᵢ E F

/-- Source lines 3715--3717: finite measures are determined by their characteristic functions. -/
theorem characteristic_function_unique_source {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : MeasureTheory.charFun μ = MeasureTheory.charFun ν) : μ = ν :=
  MeasureTheory.Measure.ext_of_charFun h

/-- Source lines 3752--3754, Lévy's convergence theorem. -/
theorem levy_convergence_source {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → MeasureTheory.ProbabilityMeasure E)
    (μ₀ : MeasureTheory.ProbabilityMeasure E) :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : E, Tendsto (fun n ↦ MeasureTheory.charFun (μ n) t) atTop
        (𝓝 (MeasureTheory.charFun μ₀ t)) :=
  MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun

/-! ## Gaussian laws -/

/-- Source lines 3421--3425 and 3779--3787: the characteristic function of a real Gaussian. -/
theorem gaussian_characteristic_function_source (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    MeasureTheory.charFun (ProbabilityTheory.gaussianReal m v) t =
      Complex.exp (t * m * Complex.I - v * t ^ 2 / 2) :=
  ProbabilityTheory.charFun_gaussianReal t

/-- The mean of a Gaussian law is its location parameter. -/
theorem gaussian_mean_source (m : ℝ) (v : ℝ≥0) :
    (∫ x, x ∂ProbabilityTheory.gaussianReal m v) = m :=
  ProbabilityTheory.integral_id_gaussianReal

/-- The variance of a Gaussian law is its variance parameter. -/
theorem gaussian_variance_source (m : ℝ) (v : ℝ≥0) :
    ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal m v) = v :=
  ProbabilityTheory.variance_id_gaussianReal

/-- Source lines 3781--3790: affine images of Gaussian random variables are Gaussian. -/
theorem gaussian_affine_source {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hX : ProbabilityTheory.HasLaw X (ProbabilityTheory.gaussianReal m v) P)
    (a b : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ a * X ω + b)
      (ProbabilityTheory.gaussianReal (a * m + b)
        (NNReal.mk (a ^ 2) (sq_nonneg a) * v)) P := by
  exact (ProbabilityTheory.gaussianReal_const_mul hX a).add_const b

/-! ## Ergodic and probabilistic limit theorems -/

/-- Source lines 4088--4092, von Neumann's mean ergodic theorem in Hilbert-space form. -/
theorem von_neumann_mean_ergodic_source {𝕜 E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1) (x : E) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop
      (𝓝 ((LinearMap.eqLocus T 1).orthogonalProjection x)) :=
  T.tendsto_birkhoffAverage_orthogonalProjection hT x

/-- Source lines 4319--4323, the strong law of large numbers. -/
theorem strong_law_source {Ω E : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (X : ℕ → Ω → E) (hInt : Integrable (X 0) P)
    (hInd : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
        atTop (𝓝 (∫ ω, X 0 ω ∂P)) :=
  ProbabilityTheory.strong_law_ae X hInt hInd hIdent

/-- Source lines 4363--4369, the central limit theorem in the general variance normalization. -/
theorem central_limit_source {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (Var[X 0; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hInd : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hInd hIdent

end ProbabilityAndMeasure
