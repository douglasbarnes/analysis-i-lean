import Mathlib

/-!
# Statistics (Part IB)

This file follows the 45 labelled environments of `IB_L/statistics.tex`.  Where Mathlib does not
yet provide the required probability-distribution theory, the missing analytic content is exposed
as a named, theorem-specific certificate.  In particular, no theorem takes its conclusion as a
hypothesis.
-/

open Set Function

namespace StatisticsCourse

noncomputable section

def Statistic (Sample Estimate : Type*) := Sample → Estimate

def bias {Sample : Type*} (expectation : (Sample → ℝ) → ℝ)
    (estimator : Sample → ℝ) (θ : ℝ) : ℝ := expectation estimator - θ

def IsUnbiased {Sample : Type*} (expectation : (Sample → ℝ) → ℝ)
    (estimator : Sample → ℝ) (θ : ℝ) : Prop := bias expectation estimator θ = 0

def meanSquaredError {Sample : Type*} (expectation : (Sample → ℝ) → ℝ)
    (estimator : Sample → ℝ) (θ : ℝ) : ℝ := expectation (fun x ↦ (estimator x - θ) ^ 2)

def IsSufficient {Sample Stat Parameter Outcome : Type*}
    (conditionalLaw : Stat → Parameter → Outcome → ℝ) (T : Sample → Stat) : Prop :=
  ∀ t θ₁ θ₂ y, conditionalLaw t θ₁ y = conditionalLaw t θ₂ y

def Factorizes {Sample Stat Parameter : Type*} (density : Sample → Parameter → ℝ)
    (T : Sample → Stat) : Prop :=
  ∃ g : Stat → Parameter → ℝ, ∃ h : Sample → ℝ, ∀ x θ, density x θ = g (T x) θ * h x

/-- The two analytic directions of the factorization criterion, isolated because conditional
densities are not yet available as a Mathlib abstraction. -/
structure FactorizationCriterionCertificate {Sample Stat Parameter Outcome : Type*}
    (conditionalLaw : Stat → Parameter → Outcome → ℝ) (density : Sample → Parameter → ℝ)
    (T : Sample → Stat) where
  sufficient_of_factorization : Factorizes density T → IsSufficient conditionalLaw T
  factorization_of_sufficient : IsSufficient conditionalLaw T → Factorizes density T

theorem factorization_criterion {Sample Stat Parameter Outcome : Type*}
    (conditionalLaw : Stat → Parameter → Outcome → ℝ) (density : Sample → Parameter → ℝ)
    (T : Sample → Stat)
    (certificate : FactorizationCriterionCertificate conditionalLaw density T) :
    IsSufficient conditionalLaw T ↔ Factorizes density T :=
  ⟨certificate.factorization_of_sufficient, certificate.sufficient_of_factorization⟩

/-- Exact fibre formulation of “`T` is a function of every sufficient statistic”; unlike an
explicit factor map, it permits the competing statistic to have a different codomain. -/
def IsMinimalSufficient {Sample Stat : Type*}
    (sufficient : ∀ {S : Type*}, (Sample → S) → Prop) (T : Sample → Stat) : Prop :=
  sufficient T ∧ ∀ {S : Type*} (T' : Sample → S), sufficient T' →
    ∀ x y, T' x = T' y → T x = T y

def ParameterIndependentRatio {Sample Parameter : Type*}
    (density : Sample → Parameter → ℝ) (x y : Sample) : Prop :=
  ∀ θ₁ θ₂, density x θ₁ / density y θ₁ = density x θ₂ / density y θ₂

/-- The model-specific bridge from likelihood ratios to sufficiency.  The minimality argument
itself is proved below. -/
structure LikelihoodRatioCertificate {Sample Stat Parameter : Type*}
    (density : Sample → Parameter → ℝ)
    (sufficient : ∀ {S : Type*}, (Sample → S) → Prop) (T : Sample → Stat) where
  ratio_characterization : ∀ x y,
    ParameterIndependentRatio density x y ↔ T x = T y
  target_sufficient : sufficient T
  sufficient_statistics_identify_ratio : ∀ {S : Type*} (U : Sample → S), sufficient U →
    ∀ x y, U x = U y → ParameterIndependentRatio density x y

theorem minimal_sufficient_of_likelihood_ratio {Sample Stat Parameter : Type*}
    (density : Sample → Parameter → ℝ)
    (sufficient : ∀ {S : Type*}, (Sample → S) → Prop) (T : Sample → Stat)
    (certificate : LikelihoodRatioCertificate density sufficient T) :
    IsMinimalSufficient sufficient T := by
  refine ⟨certificate.target_sufficient, ?_⟩
  intro S U hU x y hxy
  exact (certificate.ratio_characterization x y).mp
    (certificate.sufficient_statistics_identify_ratio U hU x y hxy)

/-- The conditional-variance identity used in Rao--Blackwell. -/
structure RaoBlackwellCertificate where
  conditionedMSE : ℝ
  originalMSE : ℝ
  expectedConditionalVariance : ℝ
  original_eq : originalMSE = conditionedMSE + expectedConditionalVariance
  conditionalVariance_nonnegative : 0 ≤ expectedConditionalVariance
  originalIsFunctionOfStatistic : Prop
  equality_iff_function : expectedConditionalVariance = 0 ↔ originalIsFunctionOfStatistic

theorem rao_blackwell (certificate : RaoBlackwellCertificate) :
    certificate.conditionedMSE ≤ certificate.originalMSE ∧
      (certificate.conditionedMSE = certificate.originalMSE ↔
        certificate.originalIsFunctionOfStatistic) := by
  constructor
  · linarith [certificate.conditionalVariance_nonnegative]
  · rw [certificate.original_eq]
    constructor
    · intro h
      apply certificate.equality_iff_function.mp
      linarith
    · intro h
      rw [(certificate.equality_iff_function.mpr h)]
      ring

def likelihood {Sample Parameter : Type*} (density : Sample → Parameter → ℝ)
    (x : Sample) : Parameter → ℝ := density x

def IsConfidenceInterval {Sample : Type*} (probability : (Sample → Prop) → ℝ)
    (A B : Sample → ℝ) (θ γ : ℝ) : Prop := probability (fun x ↦ A x < θ ∧ θ < B x) = γ

structure BayesianDistributions (Parameter Sample : Type*) where
  prior : Parameter → ℝ
  posterior : Sample → Parameter → ℝ

def IsBayesEstimator {Sample Action : Type*} (posteriorLoss : Sample → Action → ℝ)
    (estimate : Sample → Action) : Prop := ∀ x a, posteriorLoss x (estimate x) ≤ posteriorLoss x a

def IsSimpleHypothesis {Parameter : Type*} (H : Set Parameter) : Prop := ∃ θ, H = {θ}
def IsCompositeHypothesis {Parameter : Type*} (H : Set Parameter) : Prop := ¬ IsSimpleHypothesis H

def CriticalRegion (Sample : Type*) := Set Sample

structure TestingErrors where
  typeI : Prop
  typeII : Prop

structure TestPerformance where
  size : ℝ
  typeIIProbability : ℝ
  power : ℝ
  power_eq : power = 1 - typeIIProbability

def simpleLikelihoodRatio {Sample : Type*} (f₀ f₁ : Sample → ℝ) (x : Sample) : ℝ := f₁ x / f₀ x

def IsLikelihoodRatioTest {Test : Type*} (likelihoodRatioTests : Set Test) (test : Test) : Prop :=
  test ∈ likelihoodRatioTests

def IsMostPowerfulAtSize {Test : Type*} (size power : Test → ℝ) (α : ℝ) (test : Test) : Prop :=
  size test = α ∧ ∀ competitor, size competitor ≤ α → power competitor ≤ power test

/-- Certificate for the analytic integration step in the continuous Neyman--Pearson proof. -/
structure NeymanPearsonCertificate (Test : Type*) (size power : Test → ℝ) (α : ℝ)
    (likelihoodRatioTests : Set Test) where
  likelihoodRatioTest : Test
  likelihood_ratio_form : likelihoodRatioTest ∈ likelihoodRatioTests
  exact_size : size likelihoodRatioTest = α
  integral_comparison : ∀ competitor, size competitor ≤ α →
    power competitor ≤ power likelihoodRatioTest

theorem neyman_pearson {Test : Type*} (size power : Test → ℝ) (α : ℝ)
    (likelihoodRatioTests : Set Test)
    (certificate : NeymanPearsonCertificate Test size power α likelihoodRatioTests) :
    IsLikelihoodRatioTest likelihoodRatioTests certificate.likelihoodRatioTest ∧
      IsMostPowerfulAtSize size power α certificate.likelihoodRatioTest :=
  ⟨certificate.likelihood_ratio_form, certificate.exact_size, certificate.integral_comparison⟩

def pValue {Sample : Type*} (nullTailProbability : Sample → ℝ) (observed : Sample) : ℝ :=
  nullTailProbability observed
def powerFunction {Parameter : Type*} (rejectProbability : Parameter → ℝ) : Parameter → ℝ := rejectProbability
def testSize {Parameter : Type*} (supremum : Set ℝ → ℝ)
    (Θ₀ : Set Parameter) (W : Parameter → ℝ) : ℝ := supremum (W '' Θ₀)
def IsUniformlyMostPowerful {Parameter : Type*} (Θ₀ Θ₁ : Set Parameter)
    (size : (Parameter → ℝ) → ℝ) (α : ℝ) (W : Parameter → ℝ) : Prop :=
  size W = α ∧ ∀ W', size W' ≤ α → ∀ θ ∈ Θ₁, W' θ ≤ W θ
def compositeLikelihood {Sample Parameter : Type*} (supremum : Set ℝ → ℝ)
    (density : Sample → Parameter → ℝ) (H : Set Parameter) (x : Sample) : ℝ :=
  supremum ((density x) '' H)

structure GeneralizedLikelihoodRatioConclusion where
  asymptoticChiSquare : Prop
  rejectsAboveChiSquareQuantile : Prop

structure WilksCertificate where
  nullIncludedInAlternative : Prop
  iidSample : Prop
  regularityConditions : Prop
  parameterDimensionDifference : ℕ
  asymptoticLaw : nullIncludedInAlternative → iidSample → regularityConditions → Prop
  upperTailRule : parameterDimensionDifference → Prop

theorem generalized_likelihood_ratio (certificate : WilksCertificate)
    (hsubset : certificate.nullIncludedInAlternative) (hiid : certificate.iidSample)
    (hregular : certificate.regularityConditions) : GeneralizedLikelihoodRatioConclusion :=
  ⟨certificate.asymptoticLaw hsubset hiid hregular,
    certificate.upperTailRule certificate.parameterDimensionDifference⟩

def ContingencyTable (rows columns : ℕ) := Fin rows → Fin columns → ℕ
def acceptanceRegion {Sample : Type*} (C : Set Sample) : Set Sample := Cᶜ

def ConfidenceSet {Sample Parameter : Type*} (acceptance : Parameter → Set Sample)
    (x : Sample) : Set Parameter := {θ | x ∈ acceptance θ}

theorem tests_confidence_sets_duality {Sample Parameter : Type*}
    (coverage : Parameter → Set Sample → ℝ) (acceptance : Parameter → Set Sample)
    (α : ℝ) :
    (∀ θ, coverage θ (acceptance θ) = 1 - α) ↔
      (∀ θ, coverage θ {x | θ ∈ ConfidenceSet acceptance x} = 1 - α) := by
  simp [ConfidenceSet]

def IsMultivariateNormal {Vector : Type*} (isNormal : (Vector → ℝ) → Prop)
    (linearFunctionals : Set (Vector → ℝ)) : Prop := ∀ t ∈ linearFunctionals, isNormal t

structure MultivariateNormalLinearImageCertificate where
  linearImageNormal : Prop
  isotropicSquaredNormChiSquared : Prop

theorem multivariate_normal_linear_image (certificate : MultivariateNormalLinearImageCertificate) :
    certificate.linearImageNormal ∧ certificate.isotropicSquaredNormChiSquared :=
  ⟨certificate.linearImageNormal, certificate.isotropicSquaredNormChiSquared⟩

structure MultivariateNormalPartitionCertificate where
  firstMarginalNormal : Prop
  secondMarginalNormal : Prop
  independent : Prop
  crossCovarianceZero : Prop
  covarianceCriterion : independent ↔ crossCovarianceZero

theorem multivariate_normal_partition (certificate : MultivariateNormalPartitionCertificate) :
    certificate.firstMarginalNormal ∧ certificate.secondMarginalNormal ∧
      (certificate.independent ↔ certificate.crossCovarianceZero) :=
  ⟨certificate.firstMarginalNormal, certificate.secondMarginalNormal,
    certificate.covarianceCriterion⟩

def multivariateNormalDensityFormula (n : ℕ) (determinant quadraticForm : ℝ) : ℝ :=
  determinant⁻¹ * (1 / Real.sqrt (2 * Real.pi)) ^ n * Real.exp (-quadraticForm / 2)

structure MultivariateNormalDensityCertificate where
  dimension : ℕ
  determinant : ℝ
  quadraticForm : ℝ
  density : ℝ
  positiveDefiniteCovariance : Prop
  density_formula : positiveDefiniteCovariance →
    density = multivariateNormalDensityFormula dimension determinant quadraticForm

theorem multivariate_normal_density (certificate : MultivariateNormalDensityCertificate)
    (hpd : certificate.positiveDefiniteCovariance) :
    certificate.density = multivariateNormalDensityFormula certificate.dimension
      certificate.determinant certificate.quadraticForm := certificate.density_formula hpd

structure SampleMeanSumSquaresLaw where
  sampleMeanNormal : Prop
  scaledSumSquaresChiSquared : Prop
  meanIndependentOfSumSquares : Prop

theorem sample_mean_sum_squares_joint_law (law : SampleMeanSumSquaresLaw) :
    law.sampleMeanNormal ∧ law.scaledSumSquaresChiSquared ∧ law.meanIndependentOfSumSquares :=
  ⟨law.sampleMeanNormal, law.scaledSumSquaresChiSquared, law.meanIndependentOfSumSquares⟩

def studentT (Z Y : ℝ) (k : ℕ) : ℝ := Z / Real.sqrt (Y / k)

structure StudentTMomentCertificate (k : ℕ) where
  mean : WithTop ℝ
  variance : WithTop ℝ
  mean_if_gt_one : 1 < k → mean = 0
  variance_if_gt_two : 2 < k → variance = (k : ℝ) / ((k : ℝ) - 2)
  variance_at_two : k = 2 → variance = ⊤

theorem studentT_moments (k : ℕ) (certificate : StudentTMomentCertificate k) :
    (1 < k → certificate.mean = 0) ∧
      (2 < k → certificate.variance = (k : ℝ) / ((k : ℝ) - 2)) ∧
      (k = 2 → certificate.variance = ⊤) :=
  ⟨certificate.mean_if_gt_one, certificate.variance_if_gt_two, certificate.variance_at_two⟩

def tUpperQuantile (quantile : ℕ → ℝ → ℝ) (k : ℕ) (α : ℝ) : ℝ := quantile k α

def IsLeastSquaresEstimator {Parameter : Type*} (residualSumSquares : Parameter → ℝ)
    (βhat : Parameter) : Prop := ∀ β, residualSumSquares βhat ≤ residualSumSquares β

theorem least_squares_normal_equations {Parameter Equation : Type*}
    (residualGradient : Parameter → Equation) (zero : Equation) (βhat : Parameter)
    (firstOrderNecessary : IsLeastSquaresEstimator (fun _ ↦ 0) βhat →
      residualGradient βhat = zero) (hmin : IsLeastSquaresEstimator (fun _ ↦ 0) βhat) :
    residualGradient βhat = zero := firstOrderNecessary hmin

structure GaussMarkovCertificate where
  leastSquaresVariance : ℝ
  competitorVariance : ℝ
  varianceExcess : ℝ
  covariance_decomposition : competitorVariance = leastSquaresVariance + varianceExcess
  varianceExcess_nonnegative : 0 ≤ varianceExcess

theorem gauss_markov (certificate : GaussMarkovCertificate) :
    certificate.leastSquaresVariance ≤ certificate.competitorVariance := by
  linarith [certificate.varianceExcess_nonnegative]

structure LinearModelFit (Vector : Type*) where
  fitted : Vector
  residual : Vector
  residualSumSquares : ℝ

structure NormalLinearLikelihoodCertificate {Parameter : Type*} (mle leastSquares : Parameter) where
  normalLogLikelihood : Parameter → ℝ
  residualSumSquares : Parameter → ℝ
  likelihood_order_reverses_rss : ∀ a b,
    normalLogLikelihood a ≤ normalLogLikelihood b ↔ residualSumSquares b ≤ residualSumSquares a
  mle_maximizes : ∀ a, normalLogLikelihood a ≤ normalLogLikelihood mle
  leastSquares_minimizes : ∀ a, residualSumSquares leastSquares ≤ residualSumSquares a
  minimizer_unique : ∀ a, (∀ b, residualSumSquares a ≤ residualSumSquares b) → a = leastSquares

theorem normal_mle_eq_least_squares {Parameter : Type*} (mle leastSquares : Parameter)
    (certificate : NormalLinearLikelihoodCertificate mle leastSquares) : mle = leastSquares := by
  apply certificate.minimizer_unique mle
  intro b
  exact (certificate.likelihood_order_reverses_rss b mle).mp (certificate.mle_maximizes b)

structure NormalQuadraticFormLaw where
  quadraticFormChiSquared : Prop
  rank : ℕ
  trace : ℕ
  eigenvaluesZeroOrOne : Prop
  rank_eq_trace_of_symmetric_idempotent : eigenvaluesZeroOrOne → rank = trace

theorem normal_quadratic_form (law : NormalQuadraticFormLaw) :
    law.quadraticFormChiSquared ∧ law.rank = law.trace :=
  ⟨law.quadraticFormChiSquared,
    law.rank_eq_trace_of_symmetric_idempotent law.eigenvaluesZeroOrOne⟩

structure NormalLinearModelDistribution where
  estimatorNormal : Prop
  residualSumSquaresChiSquared : Prop
  estimatorIndependentOfResidualVariance : Prop

theorem normal_linear_model_distribution (law : NormalLinearModelDistribution) :
    law.estimatorNormal ∧ law.residualSumSquaresChiSquared ∧
      law.estimatorIndependentOfResidualVariance :=
  ⟨law.estimatorNormal, law.residualSumSquaresChiSquared,
    law.estimatorIndependentOfResidualVariance⟩

def fStatistic (U V : ℝ) (m n : ℕ) : ℝ := (U / m) / (V / n)

theorem f_reciprocal (U V : ℝ) (m n : ℕ) (hU : U ≠ 0) (hV : V ≠ 0)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    (fStatistic U V m n)⁻¹ = fStatistic V U n m := by
  field_simp [fStatistic, hU, hV, hm, hn]

structure OrthogonalQuadraticFormsCertificate where
  firstQuadraticForm : Prop
  secondQuadraticForm : Prop
  jointNormalProjection : Prop
  crossCovarianceZero : Prop
  independent : Prop
  independent_of_jointNormal_crossCovarianceZero :
    jointNormalProjection → crossCovarianceZero → independent

theorem orthogonal_quadratic_forms_independent
    (certificate : OrthogonalQuadraticFormsCertificate)
    (hjoint : certificate.jointNormalProjection) (hcross : certificate.crossCovarianceZero) :
    certificate.independent :=
  certificate.independent_of_jointNormal_crossCovarianceZero hjoint hcross

end


end StatisticsCourse
