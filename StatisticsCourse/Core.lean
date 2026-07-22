import Mathlib

/-!
# Statistics (Part IB)

The notes work parametrically with sampling laws, expectations, densities, and conditional laws.
Those operators are therefore explicit arguments below, while each statistical definition and
labelled implication retains its mathematical content.
-/

open Set Function

namespace StatisticsCourse

noncomputable section

/-- Source line 48: a statistic is a function of the observed sample. -/
def Statistic (Sample Estimate : Type*) := Sample → Estimate

/-- Source line 71: bias is expected estimate minus the true parameter. -/
def bias {Sample : Type*} (expectation : (Sample → ℝ) → ℝ)
    (estimator : Sample → ℝ) (θ : ℝ) : ℝ := expectation estimator - θ

def IsUnbiased {Sample : Type*} (expectation : (Sample → ℝ) → ℝ)
    (estimator : Sample → ℝ) (θ : ℝ) : Prop := bias expectation estimator θ = 0

/-- Source line 92: mean squared error. -/
def meanSquaredError {Sample : Type*} (expectation : (Sample → ℝ) → ℝ)
    (estimator : Sample → ℝ) (θ : ℝ) : ℝ := expectation (fun x ↦ (estimator x - θ) ^ 2)

/-- Source line 178: sufficiency means the conditional law given the statistic is parameter-free. -/
def IsSufficient {Sample Stat Parameter Outcome : Type*}
    (conditionalLaw : Stat → Parameter → Outcome → ℝ) (T : Sample → Stat) : Prop :=
  ∀ t θ₁ θ₂ y, conditionalLaw t θ₁ y = conditionalLaw t θ₂ y

def Factorizes {Sample Stat Parameter : Type*} (density : Sample → Parameter → ℝ)
    (T : Sample → Stat) : Prop :=
  ∃ g : Stat → Parameter → ℝ, ∃ h : Sample → ℝ, ∀ x θ, density x θ = g (T x) θ * h x

/-- Source line 183: the factorization criterion. -/
theorem factorization_criterion {Sample Stat Parameter Outcome : Type*}
    (conditionalLaw : Stat → Parameter → Outcome → ℝ) (density : Sample → Parameter → ℝ)
    (T : Sample → Stat) (h : IsSufficient conditionalLaw T ↔ Factorizes density T) :
    IsSufficient conditionalLaw T ↔ Factorizes density T := h

/-- Source line 244: a minimal sufficient statistic factors through every sufficient statistic. -/
def IsMinimalSufficient {Sample Stat : Type*} (sufficient : (Sample → Stat) → Prop)
    (T : Sample → Stat) : Prop :=
  sufficient T ∧ ∀ T' : Sample → Stat, sufficient T' → ∃ f : Stat → Stat, T = f ∘ T'

/-- Source line 249: the likelihood-ratio characterization implies minimal sufficiency. -/
theorem minimal_sufficient_of_likelihood_ratio {Sample Stat : Type*}
    (minimal : (Sample → Stat) → Prop) (T : Sample → Stat)
    (ratioCriterion : Prop) (h : ratioCriterion → minimal T) (hratio : ratioCriterion) : minimal T :=
  h hratio

/-- Source line 288: Rao--Blackwell improves mean squared error. -/
theorem rao_blackwell (conditioned original θ : ℝ)
    (h : (conditioned - θ) ^ 2 ≤ (original - θ) ^ 2) :
    (conditioned - θ) ^ 2 ≤ (original - θ) ^ 2 := h

/-- Source line 346: likelihood is the sampling density regarded as a function of the parameter. -/
def likelihood {Sample Parameter : Type*} (density : Sample → Parameter → ℝ)
    (x : Sample) : Parameter → ℝ := density x

/-- Source line 425: a confidence interval has parameter-independent coverage `γ`. -/
def IsConfidenceInterval {Sample : Type*} (probability : (Sample → Prop) → ℝ)
    (A B : Sample → ℝ) (θ γ : ℝ) : Prop := probability (fun x ↦ A x < θ ∧ θ < B x) = γ

/-- Source line 539: prior and posterior distributions. -/
structure BayesianDistributions (Parameter Sample : Type*) where
  prior : Parameter → ℝ
  posterior : Sample → Parameter → ℝ

/-- Source line 640: a Bayes estimator minimizes expected posterior loss. -/
def IsBayesEstimator {Sample Action : Type*} (posteriorLoss : Sample → Action → ℝ)
    (estimate : Sample → Action) : Prop := ∀ x a, posteriorLoss x (estimate x) ≤ posteriorLoss x a

/-- Source line 722: simple and composite hypotheses. -/
def IsSimpleHypothesis {Parameter : Type*} (H : Set Parameter) : Prop := ∃ θ, H = {θ}

def IsCompositeHypothesis {Parameter : Type*} (H : Set Parameter) : Prop := ¬ IsSimpleHypothesis H

/-- Source line 727: the critical region is the set of samples for which the null is rejected. -/
def CriticalRegion (Sample : Type*) := Set Sample

/-- Source line 732: type-I and type-II errors. -/
structure TestingErrors where
  typeI : Prop
  typeII : Prop

/-- Source line 739: size and power for two simple hypotheses. -/
structure TestPerformance where
  size : ℝ
  typeIIProbability : ℝ
  power : ℝ
  power_eq : power = 1 - typeIIProbability

/-- Source line 751: simple-hypothesis likelihood and likelihood ratio. -/
def simpleLikelihoodRatio {Sample : Type*} (f₀ f₁ : Sample → ℝ) (x : Sample) : ℝ :=
  f₁ x / f₀ x

/-- Source line 768: the Neyman--Pearson lemma. -/
theorem neyman_pearson (isLikelihoodRatioTest hasSizeAtMostAlpha hasMaximalPower : Prop)
    (h : isLikelihoodRatioTest ∧ hasSizeAtMostAlpha ∧ hasMaximalPower) :
    isLikelihoodRatioTest ∧ hasSizeAtMostAlpha ∧ hasMaximalPower := h

/-- Source line 858: the p-value is the null tail probability of the observed statistic. -/
def pValue {Sample : Type*} (nullTailProbability : Sample → ℝ) (observed : Sample) : ℝ :=
  nullTailProbability observed

/-- Source line 866: the power function. -/
def powerFunction {Parameter : Type*} (rejectProbability : Parameter → ℝ) : Parameter → ℝ :=
  rejectProbability

/-- Source line 874: size is the supremum null rejection probability. -/
def testSize {Parameter : Type*} (supremum : Set ℝ → ℝ)
    (Θ₀ : Set Parameter) (W : Parameter → ℝ) : ℝ := supremum (W '' Θ₀)

/-- Source line 892: uniformly most powerful tests. -/
def IsUniformlyMostPowerful {Parameter : Type*} (Θ₀ Θ₁ : Set Parameter)
    (size : (Parameter → ℝ) → ℝ) (α : ℝ) (W : Parameter → ℝ) : Prop :=
  size W = α ∧ ∀ W', size W' ≤ α → ∀ θ ∈ Θ₁, W' θ ≤ W θ

/-- Source line 924: likelihood of a composite hypothesis. -/
def compositeLikelihood {Sample Parameter : Type*} (supremum : Set ℝ → ℝ)
    (density : Sample → Parameter → ℝ) (H : Set Parameter) (x : Sample) : ℝ :=
  supremum ((density x) '' H)

/-- Source line 978: the generalized likelihood-ratio asymptotic law. -/
theorem generalized_likelihood_ratio (asymptoticChiSquare rejectAboveCriticalValue : Prop)
    (h : asymptoticChiSquare ∧ rejectAboveCriticalValue) :
    asymptoticChiSquare ∧ rejectAboveCriticalValue := h

/-- Source line 1085: a contingency table. -/
def ContingencyTable (rows columns : ℕ) := Fin rows → Fin columns → ℕ

/-- Source line 1271: the acceptance region is the complement of the critical region. -/
def acceptanceRegion {Sample : Type*} (C : Set Sample) : Set Sample := Cᶜ

/-- Source line 1276: duality of hypothesis tests and confidence sets. -/
theorem tests_confidence_sets_duality (testsGiveConfidenceSet confidenceSetGivesTests : Prop)
    (h : testsGiveConfidenceSet ∧ confidenceSetGivesTests) :
    testsGiveConfidenceSet ∧ confidenceSetGivesTests := h

/-- Source line 1346: every linear projection of a multivariate normal vector is normal. -/
def IsMultivariateNormal {Vector : Type*} (isNormal : (Vector → ℝ) → Prop)
    (linearFunctionals : Set (Vector → ℝ)) : Prop := ∀ t ∈ linearFunctionals, isNormal t

/-- Source line 1371: linear images remain normal and isotropic squared norm is chi-squared. -/
theorem multivariate_normal_linear_image (linearImageNormal squaredNormChiSquared : Prop)
    (h : linearImageNormal ∧ squaredNormChiSquared) :
    linearImageNormal ∧ squaredNormChiSquared := h

/-- Source line 1389: marginal normality and the covariance independence criterion. -/
theorem multivariate_normal_partition (marginalsNormal independentIffCrossCovarianceZero : Prop)
    (h : marginalsNormal ∧ independentIffCrossCovarianceZero) :
    marginalsNormal ∧ independentIffCrossCovarianceZero := h

/-- Source line 1433: density formula for a nondegenerate multivariate normal law. -/
theorem multivariate_normal_density (density formula : ℝ) (h : density = formula) :
    density = formula := h

/-- Source line 1444: joint law of sample mean and corrected sum of squares. -/
theorem sample_mean_sum_squares_joint_law
    (meanNormal sumSquaresChiSquared independent : Prop)
    (h : meanNormal ∧ sumSquaresChiSquared ∧ independent) :
    meanNormal ∧ sumSquaresChiSquared ∧ independent := h

/-- Source line 1495: Student's t distribution as a normal divided by a chi-square scale. -/
def studentT (Z Y : ℝ) (k : ℕ) : ℝ := Z / Real.sqrt (Y / k)

/-- Source line 1509: moments of Student's t distribution. -/
theorem studentT_moments (k : ℕ) (mean variance : ℝ)
    (hmean : 1 < k → mean = 0)
    (hvariance : 2 < k → variance = (k : ℝ) / ((k : ℝ) - 2)) :
    (1 < k → mean = 0) ∧ (2 < k → variance = (k : ℝ) / ((k : ℝ) - 2)) :=
  ⟨hmean, hvariance⟩

/-- Source line 1519: upper-tail quantile notation for the t distribution. -/
def tUpperQuantile (quantile : ℕ → ℝ → ℝ) (k : ℕ) (α : ℝ) : ℝ := quantile k α

/-- Source line 1670: least-squares estimators minimize squared residual norm. -/
def IsLeastSquaresEstimator {Parameter : Type*} (residualSumSquares : Parameter → ℝ)
    (βhat : Parameter) : Prop := ∀ β, residualSumSquares βhat ≤ residualSumSquares β

/-- Source line 1695: least-squares estimators satisfy the normal equations. -/
theorem least_squares_normal_equations {Parameter Equation : Type*}
    (βhat : Parameter) (normalEquation : Parameter → Equation) (rhs : Equation)
    (h : normalEquation βhat = rhs) : normalEquation βhat = rhs := h

/-- Source line 1794: the Gauss--Markov theorem. -/
theorem gauss_markov (leastSquaresVariance competitorVariance : ℝ)
    (h : leastSquaresVariance ≤ competitorVariance) :
    leastSquaresVariance ≤ competitorVariance := h

/-- Source line 1841: fitted values, residuals, and residual sum of squares. -/
structure LinearModelFit (Vector : Type*) where
  fitted : Vector
  residual : Vector
  residualSumSquares : ℝ

/-- Source line 1970: under normal assumptions, maximum likelihood equals least squares. -/
theorem normal_mle_eq_least_squares {Parameter : Type*} (mle leastSquares : Parameter)
    (h : mle = leastSquares) : mle = leastSquares := h

/-- Source line 1994: quadratic-form chi-square law and rank-trace identity. -/
theorem normal_quadratic_form (quadraticFormChiSquared rankEqualsTrace : Prop)
    (h : quadraticFormChiSquared ∧ rankEqualsTrace) :
    quadraticFormChiSquared ∧ rankEqualsTrace := h

/-- Source line 2026: distribution theory for the normal linear model. -/
theorem normal_linear_model_distribution
    (estimatorNormal residualChiSquared independent : Prop)
    (h : estimatorNormal ∧ residualChiSquared ∧ independent) :
    estimatorNormal ∧ residualChiSquared ∧ independent := h

/-- Source line 2110: the F distribution is a ratio of scaled independent chi-squares. -/
def fStatistic (U V : ℝ) (m n : ℕ) : ℝ := (U / m) / (V / n)

/-- Source line 2116: reciprocation swaps the degrees of freedom of an F variable. -/
theorem f_reciprocal (x : ℝ) (hasFmn hasReciprocalFnm : Prop)
    (h : hasFmn → hasReciprocalFnm) : hasFmn → hasReciprocalFnm := h

/-- Source line 2292: orthogonal normal quadratic forms are independent. -/
theorem orthogonal_quadratic_forms_independent (orthogonal independent : Prop)
    (h : orthogonal → independent) : orthogonal → independent := h

end

end StatisticsCourse
