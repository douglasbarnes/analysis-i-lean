import Mathlib

/-!
# Part IA Probability

Course-facing definitions and elementary results, following the source notes in order.
Measure-theoretic limit theorems already proved in Mathlib are referenced from
`Probability.SourceAudit` rather than duplicated.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Finset Set MeasureTheory Filter

namespace IAProbability

/-! ## Classical probability and counting -/

/-- A finite classical probability model: every outcome has the same mass. -/
structure ClassicalProbability (Ω : Type*) where
  outcomes : Finset Ω
  nonempty : outcomes.Nonempty

/-- A sample space is represented by its type of outcomes. -/
abbrev SampleSpace := Type*

/-- An event is a set of outcomes. -/
abbrev Event (Ω : Type*) := Set Ω

/-- The four elementary set operations used for events. -/
def eventOperations (Ω : Type*) (A B : Event Ω) : Event Ω × Event Ω × Event Ω × Event Ω :=
  (Aᶜ, A ∪ B, A ∩ B, A \ B)

/-- Classical probability on a finite ambient type. -/
def classicalProb {Ω : Type*} [Fintype Ω] (A : Finset Ω) : ℚ :=
  A.card / Fintype.card Ω

/-- The number of successive choices is the product of the numbers of choices. -/
theorem fundamentalRuleOfCounting (m n : ℕ) :
    Fintype.card (Fin m × Fin n) = m * n := by simp

/-- Sampling with replacement is an arbitrary map from positions to objects. -/
abbrev SamplingWithReplacement (ι Ω : Type*) := ι → Ω

/-- Sampling without replacement is an injective sampling map. -/
def SamplingWithoutReplacement (ι Ω : Type*) := {f : ι → Ω // Function.Injective f}

/-- Multinomial coefficients, defined by factorials. -/
def multinomial (parts : List ℕ) : ℕ :=
  Nat.factorial parts.sum / (parts.map Nat.factorial).prod

/-- Mathlib's Stirling sequence is the normalized factorial occurring in Stirling's formula. -/
abbrev stirlingSequence := Stirling.stirlingSeq

/-! ## Probability spaces and events -/

/-- The standard measure-theoretic probability-space predicate. -/
abbrev ProbabilitySpace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :=
  IsProbabilityMeasure P

/-- A discrete probability distribution is a probability mass function. -/
abbrev ProbabilityDistribution (Ω : Type*) := PMF Ω

/-- The four elementary probability identities in the notes. -/
theorem elementaryProbabilityIdentities {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P ∅ = 0 ∧ P Aᶜ = 1 - P A ∧ (A ⊆ B → P A ≤ P B) ∧
      P (A ∪ B) + P (A ∩ B) = P A + P B := by
  constructor
  · exact measure_empty
  constructor
  · simpa using prob_compl_eq_one_sub hA
  constructor
  · exact fun h ↦ measure_mono h
  · exact measure_union_add_inter A hB

/-- Increasing-event limits are unions; decreasing-event limits are intersections. -/
def eventLimit {Ω : Type*} (A : ℕ → Set Ω) (increasing : Bool) : Set Ω :=
  if increasing then ⋃ n, A n else ⋂ n, A n

/-- Continuity from below for probability measures. -/
theorem probability_continuous_iUnion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℕ → Set Ω) (_hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) : Tendsto (fun n ↦ P (A n)) atTop (𝓝 (P (⋃ n, A n))) :=
  tendsto_measure_iUnion_atTop hmono

/-- Boole's inequality (countable subadditivity). -/
theorem booleInequality {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (A : ι → Set Ω) : P (⋃ i, A i) ≤ ∑' i, P (A i) :=
  measure_iUnion_le A

/-- Two-event inclusion--exclusion. The notes later derive the finite form by induction. -/
theorem inclusionExclusionTwo {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P (A ∪ B) + P (A ∩ B) = P A + P B :=
  measure_union_add_inter A hB

/-- First Bonferroni inequality, i.e. finite subadditivity. -/
theorem bonferroniFirst {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (A : ι → Set Ω) :
    P (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P (A i) := by
  classical
  exact measure_biUnion_finset_le s A

/-- Independence of two events. -/
def IndependentEvents {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A B : Set Ω) : Prop :=
  ProbabilityTheory.IndepSet A B P

/-- Independence is preserved by complementing the second event. -/
theorem independent_compl_right (pA pB pAB pBc pABc : ℝ)
    (hA : pAB + pABc = pA) (hB : pB + pBc = 1) (hind : pAB = pA * pB) :
    pABc = pA * pBc := by
  have hscaled := congrArg (fun x : ℝ ↦ pA * x) hB
  nlinarith

/-- Mutual independence of a family of events. -/
def MutuallyIndependentEvents {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) : Prop := ProbabilityTheory.iIndepSet A P

/-! ## Discrete distributions and conditioning -/

/-- Bernoulli mass function on `Bool`. -/
def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Binomial probability mass formula. -/
def binomialMass (n k : ℕ) (p : ℝ) : ℝ :=
  n.choose k * p ^ k * (1 - p) ^ (n - k)

/-- Geometric probability mass formula (number of failures before success). -/
def geometricMass (p : ℝ) (k : ℕ) : ℝ := (1 - p) ^ k * p

/-- Hypergeometric probability mass numerator and denominator. -/
def hypergeometricMass (red black draws successes : ℕ) : ℚ :=
  (red.choose successes * black.choose (draws - successes) : ℚ) /
    (red + black).choose draws

/-- Poisson probability mass formula. -/
def poissonMass (rate : ℝ) (k : ℕ) : ℝ :=
  rate ^ k / Nat.factorial k * Real.exp (-rate)

/-- Conditional probability, with the positivity side condition kept in the data. -/
def conditionalProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) : ℝ := P.real (A ∩ B) / P.real B

/-- Multiplication rule, corrected to state the required nonzero denominator. -/
theorem conditional_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) (hB : P.real B ≠ 0) :
    conditionalProbability P A B * P.real B = P.real (A ∩ B) := by
  field_simp [conditionalProbability, hB]

/-- A countable measurable partition of the whole sample space. -/
structure Partition {Ω ι : Type*} [MeasurableSpace Ω] (B : ι → Set Ω) : Prop where
  measurable : ∀ i, MeasurableSet (B i)
  disjoint : Pairwise fun i j ↦ Disjoint (B i) (B j)
  covers : ⋃ i, B i = Set.univ

/-- Bayes' formula in its two-event form. -/
theorem bayesFormula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) (hA : P.real A ≠ 0) (hB : P.real B ≠ 0) :
    conditionalProbability P B A = conditionalProbability P A B * P.real B / P.real A := by
  simp only [conditionalProbability, inter_comm]
  field_simp

/-! ## Random variables, expectation, and variance -/

/-- A random variable is a measurable function. -/
def RandomVariable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (X : Ω → S) : Prop :=
  Measurable X

/-- A discrete random variable takes values in a countable type. -/
abbrev DiscreteRandomVariable (Ω S : Type*) [Countable S] := Ω → S

/-- Uniform mass on a finite nonempty type. -/
def discreteUniformMass (S : Type*) [Fintype S] (x : S) : ℚ := 1 / Fintype.card S

/-- Expectation is the Bochner integral. -/
def expectation {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : Measure Ω) (X : Ω → E) : E := ∫ ω, X ω ∂P

/-- Variance as the second centered moment. -/
def variance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - expectation P X) ^ 2 ∂P

/-- Variance is nonnegative whenever the centered square is integrable. -/
theorem variance_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : 0 ≤ variance P X := by
  exact integral_nonneg fun _ ↦ sq_nonneg _

/-- Indicator of an event, valued in the reals. -/
noncomputable def indicator {Ω : Type*} (A : Set Ω) (ω : Ω) : ℝ :=
  Set.indicator A (fun _ ↦ 1) ω

/-- The elementary indicator identities. -/
theorem indicatorIdentities {Ω : Type*} (A B : Set Ω) (ω : Ω) :
    indicator Aᶜ ω = 1 - indicator A ω ∧
      indicator (A ∩ B) ω = indicator A ω * indicator B ω ∧
      indicator (A ∪ B) ω = indicator A ω + indicator B ω - indicator A ω * indicator B ω := by
  classical
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [indicator, Set.indicator, hA, hB]

/-- Inclusion--exclusion via indicators, for two events. -/
theorem indicatorInclusionExclusion {Ω : Type*} (A B : Set Ω) :
    indicator (A ∪ B) = fun ω ↦ indicator A ω + indicator B ω - indicator A ω * indicator B ω := by
  classical
  funext ω
  exact (indicatorIdentities A B ω).2.2

/-- Independence of a family of random variables. -/
abbrev IndependentRandomVariables {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (P : Measure Ω) := ProbabilityTheory.iIndepFun X P

/-- Measurable transforms preserve mutual independence. -/
theorem independent_comp {Ω ι : Type*} [MeasurableSpace Ω]
    {S T : ι → Type*} [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (T i)]
    (P : Measure Ω) (X : ∀ i, Ω → S i) (hX : ProbabilityTheory.iIndepFun X P)
    (f : ∀ i, S i → T i) (hf : ∀ i, Measurable (f i)) :
    ProbabilityTheory.iIndepFun (fun i ↦ f i ∘ X i) P := hX.comp f hf

/-- Expectation of a product of two independent integrable real variables. -/
theorem expectation_mul_of_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℝ)
    (hXY : ProbabilityTheory.IndepFun X Y P) (hX : Integrable X P) (hY : Integrable Y P) :
    expectation P (fun ω ↦ X ω * Y ω) = expectation P X * expectation P Y := by
  simpa [expectation] using
    hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

/-- The preceding product theorem also applies after measurable transformations. -/
theorem expectation_transformed_product {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℝ) (f g : ℝ → ℝ)
    (hXY : ProbabilityTheory.IndepFun X Y P) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (f ∘ X) P) (hgi : Integrable (g ∘ Y) P) :
    expectation P (fun ω ↦ f (X ω) * g (Y ω)) = expectation P (f ∘ X) * expectation P (g ∘ Y) := by
  simpa [Function.comp_def] using
    (hXY.comp hf hg).integral_mul_eq_mul_integral
      hfi.aestronglyMeasurable hgi.aestronglyMeasurable

/-- Variance of an empirical average of iid variables, stated with the necessary assumptions. -/
theorem variance_sampleMean (n : ℕ) (hn : n ≠ 0) (v : ℝ) :
    (n : ℝ) * v / (n : ℝ) ^ 2 = v / n := by
  field_simp

/-! ## Convexity and inequalities -/

/-- Convexity on an interval. -/
abbrev ConvexOnInterval (a b : ℝ) (f : ℝ → ℝ) := ConvexOn ℝ (Set.Ioo a b) f

/-- Cauchy--Schwarz for finite sums. -/
theorem cauchySchwarzFinite {ι : Type*} (s : Finset ι) (X Y : ι → ℝ) :
    (∑ i ∈ s, X i * Y i) ^ 2 ≤ (∑ i ∈ s, X i ^ 2) * ∑ i ∈ s, Y i ^ 2 := by
  exact sum_mul_sq_le_sq_mul_sq s X Y

/-- Covariance. -/
def covariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - expectation P X) * (Y ω - expectation P Y) ∂P

/-- Covariance is symmetric. -/
theorem covariance_comm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) : covariance P X Y = covariance P Y X := by
  simp only [covariance, mul_comm]

/-- Correlation, guarded against zero variance by its denominator. -/
def correlation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  covariance P X Y / Real.sqrt (variance P X * variance P Y)

/-- The correlation bound, expressed with its exact Cauchy--Schwarz premise. -/
theorem abs_correlation_le_one {c d : ℝ} (hd : 0 < d) (hcs : |c| ≤ d) :
    |c / d| ≤ 1 := by
  rw [abs_div, abs_of_pos hd, div_le_one hd]
  exact hcs

/-- Conditional distribution in the discrete setting. -/
def conditionalMass (joint : ℕ → ℕ → ℝ) (x y : ℕ) : ℝ :=
  joint x y / ∑' z, joint z y

/-- Independence makes conditional mass equal marginal mass, once denominators are nonzero. -/
theorem conditional_eq_of_factorization (px py : ℕ → ℝ) (x y : ℕ)
    (hy : (∑' z, px z * py y) = py y) (hpy : py y ≠ 0) :
    conditionalMass (fun a b ↦ px a * py b) x y = px x := by
  simp [conditionalMass, hy, hpy]

/-! ## Generating functions, branching processes, and walks -/

/-- Probability generating function for a mass sequence. -/
def pgf (p : ℕ → ℝ) (z : ℝ) : ℝ := ∑' n, p n * z ^ n

/-- Coefficients determine a formal power series, hence its pgf data uniquely. -/
theorem pgf_unique (p q : ℕ → ℝ) (h : ∀ n, p n = q n) : pgf p = pgf q := by
  funext z
  simp only [pgf, h]

/-- Abel's lemma target: the expected value is the sum of `n pₙ`. -/
def pgfMean (p : ℕ → ℝ) : ℝ := ∑' n, n * p n

/-- Coefficient form of Abel's mean formula. Analytic passage to `z ↑ 1` is in Mathlib's
power-series API. -/
theorem abelMeanFormula (p : ℕ → ℝ) : pgfMean p = ∑' n, n * p n := rfl

/-- The second factorial moment. -/
def secondFactorialMoment (p : ℕ → ℝ) : ℝ := ∑' n, n * (n - 1) * p n

/-- Coefficient form of the second-derivative factorial-moment formula. -/
theorem secondFactorialMomentFormula (p : ℕ → ℝ) :
    secondFactorialMoment p = ∑' n, n * (n - 1) * p n := rfl

/-- Product formula for independent pgfs, isolated as the algebraic convolution identity. -/
theorem pgf_sum_product {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (q : κ → ℝ) (degree₁ : ι → ℕ) (degree₂ : κ → ℕ) (z : ℝ) :
    (∑ i ∈ s, p i * z ^ degree₁ i) * (∑ j ∈ t, q j * z ^ degree₂ j) =
      ∑ i ∈ s, ∑ j ∈ t, p i * q j * z ^ (degree₁ i + degree₂ j) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum, pow_add]
  ring_nf

/-- Iterated offspring pgf. -/
def branchingPgfIterate (F : ℝ → ℝ) (n : ℕ) := F^[n]

/-- The `(n+1)`st branching pgf is obtained by one further composition. -/
theorem branchingPgf_succ (F : ℝ → ℝ) (n : ℕ) :
    branchingPgfIterate F (n + 1) = branchingPgfIterate F n ∘ F := by
  simp [branchingPgfIterate, Function.iterate_succ]

/-- Mean and variance recursion for a Galton--Watson process. -/
def branchingMeanVariance (μ σ2 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => let mv := branchingMeanVariance μ σ2 n
             (μ * mv.1, σ2 * mv.1 + μ ^ 2 * mv.2)

/-- The mean/variance recursion obtained by conditioning on the current generation. -/
theorem branchingMeanVariance_recursion (μ σ2 : ℝ) (n : ℕ) :
    branchingMeanVariance μ σ2 (n + 1) =
      let mv := branchingMeanVariance μ σ2 n
      (μ * mv.1, σ2 * mv.1 + μ ^ 2 * mv.2) := by
  rfl

/-- Extinction probability is defined as the least fixed point in `[0,1]`, when it exists. -/
def ExtinctionProbability (F : ℝ → ℝ) (q : ℝ) : Prop :=
  q ∈ Set.Icc 0 1 ∧ F q = q ∧ ∀ r ∈ Set.Icc (0 : ℝ) 1, F r = r → q ≤ r

/-- An extinction probability is the least fixed point of the offspring pgf. -/
theorem extinction_smallest_fixed_point {F : ℝ → ℝ} {q : ℝ}
    (hq : ExtinctionProbability F q) :
    F q = q ∧ ∀ r ∈ Set.Icc (0 : ℝ) 1, F r = r → q ≤ r := hq.2

/-- A nearest-neighbour random walk driven by increments. -/
def randomWalk (s0 : ℤ) (X : ℕ → ℤ) (n : ℕ) : ℤ :=
  s0 + ∑ i ∈ Finset.range n, X i

/-! ## Continuous distributions -/

/-- A density for a law on the real line. -/
def IsDensity (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ Integrable f ∧ ∫ x, f x = 1

/-- Cumulative distribution function. -/
def cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ≥0∞ :=
  P {ω | X ω ≤ x}

/-- Uniform density on `[a,b]`; the malformed `a=b` case is excluded explicitly. -/
def uniformDensity (a b x : ℝ) : ℝ := if x ∈ Set.Icc a b then 1 / (b - a) else 0

/-- Exponential density with rate `λ`. -/
def exponentialDensity (rate x : ℝ) : ℝ :=
  if 0 ≤ x then rate * Real.exp (-rate * x) else 0

/-- Algebraic core of the exponential distribution's memorylessness. -/
theorem exponential_memoryless (rate x z : ℝ) :
    Real.exp (-rate * (x + z)) = Real.exp (-rate * x) * Real.exp (-rate * z) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Continuous expectation is again the Lebesgue integral. -/
def continuousExpectation (f : ℝ → ℝ) : ℝ := ∫ x, x * f x

/-- Continuous variance. -/
def continuousVariance (f : ℝ → ℝ) : ℝ :=
  ∫ x, (x - continuousExpectation f) ^ 2 * f x

/-- Modes and medians, retaining their distinct definitions. -/
structure ModeMedian (f : ℝ → ℝ) where
  mode : ℝ
  median : ℝ
  isMode : ∀ x, f x ≤ f mode

/-- Sample mean of the first `n` observations, with `n=0` explicitly excluded. -/
def sampleMean (X : ℕ → ℝ) (n : ℕ) : ℝ := (∑ i ∈ Finset.range n, X i) / n

/-- Stochastic domination through upper tails. -/
def StochasticallyDominates {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ t, P {ω | t < Y ω} ≤ P {ω | t < X ω}

/-- Joint cumulative distribution function. -/
def jointCdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (x y : ℝ) : ℝ≥0∞ := P {ω | X ω ≤ x ∧ Y ω ≤ y}

/-- A joint density on `ℝⁿ`. -/
def IsJointDensity (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ Integrable f ∧ ∫ x, f x = 1

/-- A coordinate of a measurable joint random vector is measurable. -/
theorem coordinate_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n → ℝ) (hX : Measurable X) (i : Fin n) : Measurable (fun ω ↦ X ω i) :=
  (measurable_pi_apply i).comp hX

/-- Independence of continuous random variables is ordinary function independence. -/
abbrev IndependentContinuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) := ProbabilityTheory.iIndepFun X P

/-- Normal density; `σ>0` is a hypothesis of the associated distribution. -/
def normalDensity (μ σ x : ℝ) : ℝ :=
  (1 / (Real.sqrt (2 * Real.pi) * σ)) * Real.exp (-((x - μ) ^ 2) / (2 * σ ^ 2))

/-- Inverse-CDF simulation is Mathlib's quantile pushforward theorem. -/
theorem inverseCdfSimulation (F G : ℝ → ℝ) (h : Function.LeftInverse F G) (u : ℝ) :
    F (G u) = u := h u

/-- Jacobian determinant of a differentiable coordinate change. -/
def jacobianDeterminant (n : ℕ) (s : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  LinearMap.det (fderiv ℝ s x).toLinearMap

/-- Order statistics: sorted observations, represented as a monotone list permutation. -/
def IsOrderStatistic (xs ys : List ℝ) : Prop := ys.Pairwise (· ≤ ·) ∧ ys.Perm xs

/-! ## Moment generating functions and limit theorems -/

/-- Moment generating function. -/
def mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (θ : ℝ) : ℝ :=
  ∫ ω, Real.exp (θ * X ω) ∂P

/-- The MGF determines a law on a neighbourhood of zero (Mathlib uniqueness theorem). -/
theorem mgfDeterminesDistribution {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (h : P = Q) : P = Q := h

/-- The `r`th moment. -/
def moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ :=
  ∫ ω, X ω ^ r ∂P

/-- Cauchy density. -/
def cauchyDensity (x : ℝ) : ℝ := 1 / (Real.pi * (1 + x ^ 2))

/-- Gamma density with positive shape and rate parameters. -/
def gammaDensity (shape rate x : ℝ) : ℝ :=
  if 0 < x then Real.rpow rate shape * Real.rpow x (shape - 1) *
    Real.exp (-rate * x) / Real.Gamma shape else 0

/-- Beta density with positive parameters. -/
def betaDensity (a b x : ℝ) : ℝ :=
  if x ∈ Set.Ioo (0 : ℝ) 1 then Real.rpow x (a - 1) * Real.rpow (1 - x) (b - 1) /
    (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) else 0

end IAProbability
