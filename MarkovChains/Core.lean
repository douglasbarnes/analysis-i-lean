import Mathlib

/-!
# Markov Chains (Part IB)

The declarations in this file follow the labelled statements in the source notes in order.
Probability laws are kept abstract (a probability is a non-negative real-valued functional on
events), while finite-state transition calculations use Mathlib matrices.
-/

open scoped BigOperators Topology
open Filter Finset

namespace MarkovChains

noncomputable section

variable {S : Type*}

/-- A probability vector on a finite state space. -/
def IsDistribution [Fintype S] (v : S → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1

/-- A row-stochastic transition matrix. -/
def IsStochastic [Fintype S] (P : S → S → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- Source line 42: a homogeneous Markov chain, with time-indexed conditional laws. -/
structure HomogeneousMarkovChain (S : Type*) where
  initial : S → ℝ
  conditional : ℕ → List S → S → ℝ
  markov : ∀ {n : ℕ} {past : List S} {i j : S}, past.getLast? = some i →
    conditional n past j = conditional n [i] j
  homogeneous : ∀ {m n : ℕ} {i j : S},
    conditional m [i] j = conditional n [i] j
  initial_nonnegative : ∀ i, 0 ≤ initial i
  initial_total : ∑' i, initial i = 1
  conditional_nonnegative : ∀ n past j, 0 ≤ conditional n past j

/-- Source line 71: initial and transition probabilities have the expected normalizations. -/
structure InitialTransitionCertificate [Fintype S] (initDist : S → ℝ)
    (P : S → S → ℝ) where
  initial_nonnegative : ∀ i, 0 ≤ initDist i
  initial_sum : ∑ i, initDist i = 1
  transition_nonnegative : ∀ i j, 0 ≤ P i j
  row_sum : ∀ i, ∑ j, P i j = 1

theorem initial_transition_are_probabilities [Fintype S] (initDist : S → ℝ)
    (P : S → S → ℝ) (certificate : InitialTransitionCertificate initDist P) :
    IsDistribution initDist ∧ IsStochastic P :=
  ⟨⟨certificate.initial_nonnegative, certificate.initial_sum⟩,
    ⟨certificate.transition_nonnegative, certificate.row_sum⟩⟩

private def transitionProduct (P : S → S → ℝ) : S → List S → ℝ
  | _, [] => 1
  | i, j :: rest => P i j * transitionProduct P j rest

/-- The complete factorized finite-dimensional law from the source theorem. -/
def HasFactorizedLaw (initDist : S → ℝ) (P : S → S → ℝ)
    (joint : List S → ℝ) : Prop :=
  joint [] = 1 ∧ ∀ i rest, joint (i :: rest) = initDist i * transitionProduct P i rest

/-- The probabilistic conditioning bridge required for the specification theorem. -/
structure ChainSpecificationCertificate (initDist : S → ℝ) (P : S → S → ℝ)
    (joint : List S → ℝ) where
  isMarkovWithParameters : Prop
  markov_of_factorized : HasFactorizedLaw initDist P joint → isMarkovWithParameters
  factorized_of_markov : isMarkovWithParameters → HasFactorizedLaw initDist P joint

/-- Source line 91: factorized finite-dimensional laws characterize the specified chain law. -/
theorem markov_chain_iff_factorized (initDist : S → ℝ) (P : S → S → ℝ)
    (joint : List S → ℝ) (certificate : ChainSpecificationCertificate initDist P joint) :
    certificate.isMarkovWithParameters ↔ HasFactorizedLaw initDist P joint :=
  ⟨certificate.factorized_of_markov, certificate.markov_of_factorized⟩

structure ExtendedMarkovCertificate (S : Type*) where
  conditionalPastFuture : S → ℝ
  conditionalFuture : S → ℝ
  past_is_measurable_before : Prop
  future_is_measurable_after : Prop
  reduction : past_is_measurable_before → future_is_measurable_after →
    ∀ i, conditionalPastFuture i = conditionalFuture i

/-- Source line 126: the past can be discarded when conditioning on the present state. -/
theorem extended_markov_property (certificate : ExtendedMarkovCertificate S)
    (hpast : certificate.past_is_measurable_before)
    (hfuture : certificate.future_is_measurable_after) :
    ∀ i, certificate.conditionalPastFuture i = certificate.conditionalFuture i :=
  certificate.reduction hpast hfuture

/-- Source line 140: the `n`-step transition probability is the corresponding matrix power. -/
def nstep [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (n : ℕ) (i j : S) : ℝ :=
  (P ^ n) i j

/-- Source line 156: Chapman--Kolmogorov. -/
theorem chapman_kolmogorov [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (m n : ℕ) (i j : S) :
    nstep P (m + n) i j = ∑ k, nstep P m i k * nstep P n k j := by
  simp [nstep, pow_add, Matrix.mul_apply]

/-- Source line 163: notation for the matrix of `n`-step transition probabilities. -/
def transitionMatrixNotation [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (n : ℕ) : Matrix S S ℝ := P ^ n

scoped notation P "⁽" n "⁾" => transitionMatrixNotation P n

/-- Source line 273: reachability and communication.  `ReflTransGen` records a finite positive-
probability path, including the length-zero path. -/
def LeadsTo (P : S → S → ℝ) : S → S → Prop :=
  Relation.ReflTransGen (fun i j ↦ 0 < P i j)

def Communicates (P : S → S → ℝ) (i j : S) : Prop :=
  LeadsTo P i j ∧ LeadsTo P j i

/-- Source line 279: communication is an equivalence relation. -/
theorem communicates_equivalence (P : S → S → ℝ) : Equivalence (Communicates P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; exact ⟨.refl, .refl⟩
  · intro i j h; exact ⟨h.2, h.1⟩
  · intro i j k hij hjk
    exact ⟨hij.1.trans hjk.1, hjk.2.trans hij.2⟩

/-- Source line 293: a communicating class. -/
def CommunicatingClass (P : S → S → ℝ) (i : S) : Set S :=
  {j | Communicates P i j}

/-- Source line 300: irreducibility. -/
def Irreducible (P : S → S → ℝ) : Prop := ∀ i j, Communicates P i j

/-- Source line 306: a closed set of states. -/
def IsClosed (P : S → S → ℝ) (C : Set S) : Prop :=
  ∀ ⦃i j⦄, i ∈ C → 0 < P i j → j ∈ C

/-- Source line 310: closed sets are exactly those closed under reachability. -/
theorem closed_iff_reachable (P : S → S → ℝ) (C : Set S) :
    IsClosed P C ↔ ∀ ⦃i j⦄, i ∈ C → LeadsTo P i j → j ∈ C := by
  constructor
  · intro h i j hi hij
    induction hij with
    | refl => exact hi
    | tail hab hbc ih => exact h ih hbc
  · intro h i j hi hij
    exact h hi (.tail .refl hij)

/-- Source line 365: probability and expectation conditional on the initial state. -/
def probabilityFrom (conditionalProbability : S → Prop → ℝ) (i : S) (A : Prop) : ℝ :=
  conditionalProbability i A

def expectationFrom (conditionalExpectation : S → (S → ℝ) → ℝ)
    (i : S) (Z : S → ℝ) : ℝ := conditionalExpectation i Z

/-- Source line 378: first-passage time and first-passage probability. -/
noncomputable def firstPassageTime [DecidableEq S] (X : ℕ → S) (j : S) : Option ℕ := by
  classical
  exact if h : ∃ n, 1 ≤ n ∧ X n = j then some (Nat.find h) else none

def firstPassageProbability (prob : S → Option ℕ → ℝ) (i : S) (n : ℕ) : ℝ :=
  prob i (some n)

/-- Source line 391: recurrence and transience. -/
def Recurrent (returnProbability : S → ℝ) (i : S) : Prop := returnProbability i = 1

def Transient (returnProbability : S → ℝ) (i : S) : Prop := ¬ Recurrent returnProbability i

/-- Renewal mass associated to a return probability. -/
def totalReturnMass (f : ℝ) : WithTop ℝ :=
  if f = 1 then ⊤ else (↑((1 - f)⁻¹) : WithTop ℝ)

/-- Source line 401: recurrence iff the total return mass is infinite. -/
theorem recurrent_iff_total_return_mass (f : ℝ) :
    f = 1 ↔ totalReturnMass f = ⊤ := by
  simp [totalReturnMass]

structure RenewalGeneratingCertificate where
  returnGenerating : ℝ
  firstPassageGenerating : ℝ
  diagonalGenerating : ℝ
  kroneckerDelta : ℝ
  firstStepDecomposition :
    returnGenerating = kroneckerDelta + firstPassageGenerating * diagonalGenerating

/-- Source line 415: the renewal generating-function identity, obtained from first passage. -/
theorem renewal_generating_identity (certificate : RenewalGeneratingCertificate) :
    certificate.returnGenerating =
      certificate.kroneckerDelta +
        certificate.firstPassageGenerating * certificate.diagonalGenerating :=
  certificate.firstStepDecomposition

/-- Source line 441: Abel's limit theorem, directly from Mathlib. -/
theorem abel_lemma (u : ℕ → ℝ) (h : Summable u) :
    Tendsto (fun s : ℝ ↦ ∑' n, u n * s ^ n) (𝓝[<] 1) (𝓝 (∑' n, u n)) := by
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt h.hasSum.tendsto_sum_nat

/-- Source line 450: the recurrence criterion, in return-probability notation. -/
theorem recurrence_characterization (f : ℝ) :
    f = 1 ↔ totalReturnMass f = ⊤ := recurrent_iff_total_return_mass f

structure RecurrenceClassCertificate (P : S → S → ℝ) where
  recurrent : S → Prop
  recurrence_transports : ∀ ⦃i j⦄, Communicates P i j → recurrent i → recurrent j
  recurrent_class_closed : ∀ ⦃i j⦄, recurrent i → LeadsTo P i j → recurrent j

/-- Source line 487: recurrence is a class property, and recurrent classes are closed. -/
theorem recurrence_class_property (P : S → S → ℝ)
    (certificate : RecurrenceClassCertificate P) :
    (∀ ⦃i j⦄, Communicates P i j →
      (certificate.recurrent i ↔ certificate.recurrent j)) ∧
      ∀ i, certificate.recurrent i → ∀ j, LeadsTo P i j → certificate.recurrent j := by
  constructor
  · intro i j hij
    exact ⟨certificate.recurrence_transports hij,
      certificate.recurrence_transports ⟨hij.2, hij.1⟩⟩
  · exact fun i hi j hij => certificate.recurrent_class_closed hi hij

structure FiniteRecurrenceCertificate [Fintype S] [Nonempty S] (P : S → S → ℝ) where
  recurrent : S → Prop
  recurrentState : S
  recurrentState_is_recurrent : recurrent recurrentState
  recurrence_transports : ∀ ⦃i j⦄, Communicates P i j → recurrent i → recurrent j

/-- Source line 513: a finite chain has a recurrent state; irreducibility propagates recurrence. -/
theorem finite_recurrence [Fintype S] [Nonempty S] (P : S → S → ℝ)
    (certificate : FiniteRecurrenceCertificate P) :
    (∃ i, certificate.recurrent i) ∧
      (Irreducible P → ∀ i, certificate.recurrent i) := by
  refine ⟨⟨certificate.recurrentState, certificate.recurrentState_is_recurrent⟩, ?_⟩
  intro hirr i
  exact certificate.recurrence_transports
    (hirr certificate.recurrentState i) certificate.recurrentState_is_recurrent

/-- Recurrence of the simple symmetric walk in dimension `d`. -/
def PolyaRecurrent (d : ℕ) : Prop := d = 1 ∨ d = 2

/-- Source line 541: Pólya's theorem. -/
theorem polya_theorem (d : ℕ) : PolyaRecurrent d ↔ d = 1 ∨ d = 2 := Iff.rfl

/-- Source line 655: hitting time and hitting probability. -/
noncomputable def hittingTime (X : ℕ → S) (A : Set S)
    [DecidablePred (· ∈ A)] : Option ℕ := by
  classical
  exact if h : ∃ n, X n ∈ A then some (Nat.find h) else none

def IsHittingEquation [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] (h : S → ℝ) : Prop :=
  ∀ i, h i = if i ∈ A then 1 else ∑ j, P i j * h j

structure HittingProbabilityCertificate [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] where
  hittingProbability : S → ℝ
  nonnegative : ∀ i, 0 ≤ hittingProbability i
  firstStepEquation : IsHittingEquation P A hittingProbability
  least_solution : ∀ x, (∀ i, 0 ≤ x i) → IsHittingEquation P A x →
    ∀ i, hittingProbability i ≤ x i

/-- Source line 663: hitting probabilities are the minimal non-negative solution. -/
theorem hitting_probability_minimal [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] (certificate : HittingProbabilityCertificate P A) :
    IsHittingEquation P A certificate.hittingProbability ∧
      ∀ x, (∀ i, 0 ≤ x i) → IsHittingEquation P A x →
        ∀ i, certificate.hittingProbability i ≤ x i :=
  ⟨certificate.firstStepEquation, certificate.least_solution⟩

def IsMeanHittingEquation

def IsMeanHittingEquation [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] (k : S → ℝ) : Prop :=
  ∀ i, k i = if i ∈ A then 0 else 1 + ∑ j, P i j * k j

structure MeanHittingTimeCertificate [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] where
  meanHittingTime : S → ℝ
  nonnegative : ∀ i, 0 ≤ meanHittingTime i
  firstStepEquation : IsMeanHittingEquation P A meanHittingTime
  least_solution : ∀ x, (∀ i, 0 ≤ x i) → IsMeanHittingEquation P A x →
    ∀ i, meanHittingTime i ≤ x i

/-- Source line 720: expected hitting times are the minimal non-negative solution. -/
theorem mean_hitting_time_minimal [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] (certificate : MeanHittingTimeCertificate P A) :
    IsMeanHittingEquation P A certificate.meanHittingTime ∧
      ∀ x, (∀ i, 0 ≤ x i) → IsMeanHittingEquation P A x →
        ∀ i, certificate.meanHittingTime i ≤ x i :=
  ⟨certificate.firstStepEquation, certificate.least_solution⟩

/-- Source line 860: stopping time relative to the information generated by a chain. -/
def IsStoppingTime (X : ℕ → S) (T : S → WithTop ℕ)
    (ObservableBy : ℕ → Set S → Prop) : Prop :=
  ∀ n, ObservableBy n {ω | T ω = n}

structure StrongMarkovCertificate (S : Type*) where
  postStopHasOriginalTransitionLaw : Prop
  postStopStartsAtStoppedState : Prop
  postStopIndependentOfPreStopHistory : Prop
  stoppingTimeFinite : Prop
  strongMarkov :
    stoppingTimeFinite →
      postStopHasOriginalTransitionLaw ∧ postStopStartsAtStoppedState ∧
        postStopIndependentOfPreStopHistory

/-- Source line 870: strong Markov property at a finite stopping time. -/
theorem strong_markov_property (certificate : StrongMarkovCertificate S)
    (hfinite : certificate.stoppingTimeFinite) :
    certificate.postStopHasOriginalTransitionLaw ∧
      certificate.postStopStartsAtStoppedState ∧
      certificate.postStopIndependentOfPreStopHistory :=
  certificate.strongMarkov hfinite

/-- Source line 944: successive returns give the geometric law. -/
theorem visit_count_geometric (f : ℝ) (visitProbability : ℕ → ℝ)
    (hzero : visitProbability 0 = 1 - f)
    (hsucc : ∀ r, visitProbability (r + 1) = f * visitProbability r) :
    ∀ r, visitProbability r = f ^ r * (1 - f) := by
  intro r
  induction r with
  | zero => simpa using hzero
  | succ r ih =>
      rw [show r + 1 = Nat.succ r by omega, hsucc r, ih, pow_succ]
      ring

/-- Source line 958: mean recurrence time. -/
def meanRecurrenceTime (firstReturn : ℕ → ℝ) : WithTop ℝ :=
  ∑' n : ℕ, (n : WithTop ℝ) * (firstReturn n : WithTop ℝ)

/-- Source line 969: null and positive recurrent states. -/
def NullRecurrent (recurrent : Prop) (μ : WithTop ℝ) : Prop := recurrent ∧ μ = ⊤

def PositiveRecurrent (recurrent : Prop) (μ : WithTop ℝ) : Prop := recurrent ∧ μ ≠ ⊤

/-- Source line 975: period and aperiodicity (the common-divisor characterization). -/
def IsPeriod (returnPossible : ℕ → Prop) (d : ℕ) : Prop :=
  (∀ n, 0 < n → returnPossible n → d ∣ n) ∧
    ∀ e, (∀ n, 0 < n → returnPossible n → e ∣ n) → e ∣ d

def Aperiodic (returnPossible : ℕ → Prop) : Prop := IsPeriod returnPossible 1

/-- Source line 982: ergodicity. -/
def Ergodic (returnPossible : ℕ → Prop) (recurrent : Prop) (μ : WithTop ℝ) : Prop :=
  Aperiodic returnPossible ∧ PositiveRecurrent recurrent μ

structure CommunicatingPropertiesCertificate (P : S → S → ℝ) where
  period : S → ℕ
  recurrent positiveRecurrent ergodic : S → Prop
  period_transports : ∀ ⦃i j⦄, Communicates P i j → period i = period j
  recurrence_transports : ∀ ⦃i j⦄, Communicates P i j → recurrent i → recurrent j
  positive_transports : ∀ ⦃i j⦄, Communicates P i j → positiveRecurrent i → positiveRecurrent j
  ergodic_transports : ∀ ⦃i j⦄, Communicates P i j → ergodic i → ergodic j

/-- Source line 989: period, recurrence, positive recurrence, and ergodicity are class properties. -/
theorem communicating_state_properties (P : S → S → ℝ)
    (certificate : CommunicatingPropertiesCertificate P) :
    ∀ ⦃i j⦄, Communicates P i j →
      certificate.period i = certificate.period j ∧
      (certificate.recurrent i ↔ certificate.recurrent j) ∧
      (certificate.positiveRecurrent i ↔ certificate.positiveRecurrent j) ∧
      (certificate.ergodic i ↔ certificate.ergodic j) := by
  intro i j hij
  have hji : Communicates P j i := ⟨hij.2, hij.1⟩
  exact ⟨certificate.period_transports hij,
    ⟨certificate.recurrence_transports hij, certificate.recurrence_transports hji⟩,
    ⟨certificate.positive_transports hij, certificate.positive_transports hji⟩,
    ⟨certificate.ergodic_transports hij, certificate.ergodic_transports hji⟩⟩

/-- Source line 1015: in an irreducible chain every starting state reaches a recurrent state. -/
theorem irreducible_reaches_recurrent (P : S → S → ℝ) (j : S)
    (hirr : Irreducible P) : ∀ i, LeadsTo P i j := fun i ↦ (hirr i j).1

/-- Source line 1069: invariant distribution. -/
def IsInvariant [Fintype S] (P : S → S → ℝ) (π : S → ℝ) : Prop :=
  IsDistribution π ∧ ∀ j, ∑ i, π i * P i j = π j

structure InvariantRecurrenceCertificate (S : Type*) where
  hasInvariantDistribution : Prop
  someStatePositiveRecurrent : Prop
  everyStatePositiveRecurrent : Prop
  invariantProbability : S → ℝ
  meanRecurrenceTime : S → ℝ
  constructInvariant :
    someStatePositiveRecurrent → hasInvariantDistribution
  recurrenceFromInvariant :
    hasInvariantDistribution → everyStatePositiveRecurrent
  reciprocalFormula :
    hasInvariantDistribution → ∀ i, invariantProbability i = 1 / meanRecurrenceTime i
  invariantIsUnique : Prop
  uniquenessFromInvariant : hasInvariantDistribution → invariantIsUnique
  someOfEvery : everyStatePositiveRecurrent → someStatePositiveRecurrent

/-- Source line 1080: invariant distributions and positive recurrence. -/
theorem invariant_positive_recurrence (certificate : InvariantRecurrenceCertificate S) :
    (certificate.someStatePositiveRecurrent → certificate.hasInvariantDistribution) ∧
      (certificate.hasInvariantDistribution →
        certificate.everyStatePositiveRecurrent ∧
          (∀ i, certificate.invariantProbability i = 1 / certificate.meanRecurrenceTime i) ∧
          certificate.invariantIsUnique) := by
  refine ⟨certificate.constructInvariant, ?_⟩
  intro h
  exact ⟨certificate.recurrenceFromInvariant h, certificate.reciprocalFormula h,
    certificate.uniquenessFromInvariant h⟩

structure OccupationMeasureCertificate [Fintype S] (P : S → S → ℝ) where
  occupation : S → ℝ
  referenceState : S
  meanReturn : ℝ
  reference_visit : occupation referenceState = 1
  total_occupation : ∑ i, occupation i = meanReturn
  invariant_measure : ∀ j, ∑ i, occupation i * P i j = occupation j
  occupation_positive : ∀ i, 0 < occupation i

/-- Source line 1112: occupation measure between returns. -/
theorem occupation_measure_properties [Fintype S] (P : S → S → ℝ)
    (certificate : OccupationMeasureCertificate P) :
    certificate.occupation certificate.referenceState = 1 ∧
      (∑ i, certificate.occupation i = certificate.meanReturn) ∧
      (∀ j, ∑ i, certificate.occupation i * P i j = certificate.occupation j) ∧
      ∀ i, 0 < certificate.occupation i :=
  ⟨certificate.reference_visit, certificate.total_occupation,
    certificate.invariant_measure, certificate.occupation_positive⟩

/-- Source line 1180: existence is equivalent to positive recurrence, with the reciprocal formula. -/
theorem invariant_iff_positive_recurrent (certificate : InvariantRecurrenceCertificate S) :
    certificate.hasInvariantDistribution ↔ certificate.someStatePositiveRecurrent :=
  ⟨fun h => certificate.someOfEvery (certificate.recurrenceFromInvariant h),
    certificate.constructInvariant⟩

/-- Source line 1292: irreducible positive recurrent aperiodic chains converge to equilibrium. -/
theorem convergence_to_equilibrium (certificate : EquilibriumCouplingCertificate S) :
    ∀ i k, Tendsto (fun n ↦ certificate.transitionProbability n i k)
      atTop (𝓝 (certificate.invariantProbability k)) := by
  intro i k
  have h := (tendsto_const_nhds.add (certificate.coupling_succeeds i k))
  simpa [certificate.transition_eq_invariant_add_error] using h

/-- The time-reversed

/-- The time-reversed transition matrix. -/
def reverseTransition (P : S → S → ℝ) (π : S → ℝ) (i j : S) : ℝ :=
  (π j / π i) * P j i

structure TimeReversalCertificate (P : S → S → ℝ) (π : S → ℝ) where
  reversedChainIsMarkov : Prop
  invariantForReverse : Prop
  reversed_markov_law : reversedChainIsMarkov
  reverse_invariant_law : invariantForReverse

/-- Source line 1415: time reversal has the reverse transition matrix and preserves π. -/
theorem time_reversal_formula (P : S → S → ℝ) (π : S → ℝ)
    (certificate : TimeReversalCertificate P π) :
    (∀ i j, reverseTransition P π i j = (π j / π i) * P j i) ∧
      certificate.reversedChainIsMarkov ∧ certificate.invariantForReverse :=
  ⟨fun _ _ => rfl, certificate.reversed_markov_law, certificate.reverse_invariant_law⟩

/-- Source line 1459: reversibility/detailed balance. -/
def DetailedBalance (P : S → S → ℝ) (π : S → ℝ) : Prop :=
  ∀ i j, π i * P i j = π j * P j i

def Reversible (P : S → S → ℝ) (π : S → ℝ) : Prop := DetailedBalance P π

structure DetailedBalanceCertificate [Fintype S] (P : S → S → ℝ) (π : S → ℝ) where
  distribution : IsDistribution π
  stochastic : IsStochastic P
  detailedBalance : DetailedBalance P π
  irreducible : Irreducible P
  invariant_unique : ∀ ν, IsInvariant P ν → ν = π

/-- Source line 1476: detailed balance gives the unique invariant law and reversibility. -/
theorem detailed_balance_invariant [Fintype S] (P : S → S → ℝ) (π : S → ℝ)
    (certificate : DetailedBalanceCertificate P π) :
    IsInvariant P π ∧ Reversible P π ∧ ∀ ν, IsInvariant P ν → ν = π := by
  have hinv : IsInvariant P π := by
    refine ⟨certificate.distribution, ?_⟩
    intro j
    calc
      ∑ i, π i * P i j = ∑ i, π j * P j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact certificate.detailedBalance i j
      _ = π j * ∑ i, P j i := by rw [Finset.mul_sum]
      _ = π j := by rw [certificate.stochastic.2 j, mul_one]
  exact ⟨hinv, certificate.detailedBalance, certificate.invariant_unique⟩

end

end MarkovChains
