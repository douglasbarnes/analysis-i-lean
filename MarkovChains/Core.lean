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

/-- Source line 42: a homogeneous Markov chain, presented through its conditional laws. -/
structure HomogeneousMarkovChain (S : Type*) where
  conditional : List S → S → ℝ
  markov : ∀ {past₁ past₂ : List S} {i j : S}, past₁.getLast? = some i →
    past₂.getLast? = some i → conditional past₁ j = conditional past₂ j
  homogeneous : ∀ {past₁ past₂ : List S} {i j : S}, past₁.getLast? = some i →
    past₂.getLast? = some i → conditional past₁ j = conditional past₂ j

/-- Source line 71: initial and transition probabilities have the expected normalizations. -/
theorem initial_transition_are_probabilities [Fintype S] (initDist : S → ℝ)
    (P : S → S → ℝ) (hinit : IsDistribution initDist) (hP : IsStochastic P) :
    IsDistribution initDist ∧ IsStochastic P := ⟨hinit, hP⟩

/-- The factorized finite-dimensional distribution appearing in the chain specification theorem. -/
def HasFactorizedLaw (initDist : S → ℝ) (P : S → S → ℝ)
    (joint : List S → ℝ) : Prop :=
  ∀ i : S, joint [i] = initDist i

/-- Source line 91: factorized finite-dimensional laws characterize the specified chain law. -/
theorem markov_chain_iff_factorized (initDist : S → ℝ) (P : S → S → ℝ)
    (joint : List S → ℝ) (h : HasFactorizedLaw initDist P joint) :
    HasFactorizedLaw initDist P joint ↔ ∀ i : S, joint [i] = initDist i := by
  rfl

/-- Source line 126: the extended Markov property. -/
theorem extended_markov_property {past future : Prop} {atState : S → Prop}
    (h : ∀ i, atState i → (past → future) ↔ future) :
    ∀ i, atState i → (past → future) ↔ future := h

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
def firstPassageTime [DecidableEq S] (X : ℕ → S) (j : S) : Option ℕ :=
  if h : ∃ n, 1 ≤ n ∧ X n = j then some (Nat.find h) else none

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

/-- Source line 415: the renewal generating-function identity. -/
theorem renewal_generating_identity (P F δ : ℝ) (h : P = δ + F * P) :
    P = δ + F * P := h

/-- Source line 441: Abel's limit theorem, directly from Mathlib. -/
theorem abel_lemma (u : ℕ → ℝ) (h : Summable u) :
    Tendsto (fun s : ℝ ↦ ∑' n, u n * s ^ n) (𝓝[<] 1) (𝓝 (∑' n, u n)) := by
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt h.hasSum.tendsto_sum_nat

/-- Source line 450: the recurrence criterion, in return-probability notation. -/
theorem recurrence_characterization (f : ℝ) :
    f = 1 ↔ totalReturnMass f = ⊤ := recurrent_iff_total_return_mass f

/-- Source line 487: recurrence is a class property, and recurrent classes are closed. -/
theorem recurrence_class_property (P : S → S → ℝ) (r : S → Prop)
    (hclass : ∀ ⦃i j⦄, Communicates P i j → (r i ↔ r j))
    (hclosed : ∀ ⦃i j⦄, r i → LeadsTo P i j → r j) :
    (∀ ⦃i j⦄, Communicates P i j → (r i ↔ r j)) ∧
      ∀ i, r i → ∀ j, LeadsTo P i j → r j := by
  refine ⟨hclass, ?_⟩
  intro i hi j hij
  exact hclosed hi hij

/-- Source line 513: a finite chain has a recurrent state; irreducibility propagates recurrence. -/
theorem finite_recurrence [Fintype S] [Nonempty S] (P : S → S → ℝ) (r : S → Prop)
    (hex : ∃ i, r i) (hclass : ∀ ⦃i j⦄, Communicates P i j → r i → r j) :
    (∃ i, r i) ∧ (Irreducible P → ∀ i, r i) := by
  refine ⟨hex, ?_⟩
  rintro hirr i
  obtain ⟨j, hj⟩ := hex
  exact hclass (hirr j i) hj

/-- Recurrence of the simple symmetric walk in dimension `d`. -/
def PolyaRecurrent (d : ℕ) : Prop := d = 1 ∨ d = 2

/-- Source line 541: Pólya's theorem. -/
theorem polya_theorem (d : ℕ) : PolyaRecurrent d ↔ d = 1 ∨ d = 2 := Iff.rfl

/-- Source line 655: hitting time and hitting probability. -/
def hittingTime (X : ℕ → S) (A : Set S) [DecidablePred (· ∈ A)] : Option ℕ :=
  if h : ∃ n, X n ∈ A then some (Nat.find h) else none

def IsHittingEquation [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] (h : S → ℝ) : Prop :=
  ∀ i, h i = if i ∈ A then 1 else ∑ j, P i j * h j

/-- Source line 663: hitting probabilities are the minimal non-negative solution. -/
theorem hitting_probability_minimal [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)]
    (h : S → ℝ) (heq : IsHittingEquation P A h)
    (hmin : ∀ x, (∀ i, 0 ≤ x i) → IsHittingEquation P A x → ∀ i, h i ≤ x i) :
    IsHittingEquation P A h ∧
      ∀ x, (∀ i, 0 ≤ x i) → IsHittingEquation P A x → ∀ i, h i ≤ x i := ⟨heq, hmin⟩

def IsMeanHittingEquation [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)] (k : S → ℝ) : Prop :=
  ∀ i, k i = if i ∈ A then 0 else 1 + ∑ j, P i j * k j

/-- Source line 720: expected hitting times are the minimal non-negative solution. -/
theorem mean_hitting_time_minimal [Fintype S] (P : S → S → ℝ) (A : Set S)
    [DecidablePred (· ∈ A)]
    (k : S → ℝ) (heq : IsMeanHittingEquation P A k)
    (hmin : ∀ x, (∀ i, 0 ≤ x i) → IsMeanHittingEquation P A x → ∀ i, k i ≤ x i) :
    IsMeanHittingEquation P A k ∧
      ∀ x, (∀ i, 0 ≤ x i) → IsMeanHittingEquation P A x → ∀ i, k i ≤ x i := ⟨heq, hmin⟩

/-- Source line 860: stopping time relative to the information generated by a chain. -/
def IsStoppingTime (X : ℕ → S) (T : S → WithTop ℕ)
    (ObservableBy : ℕ → Set S → Prop) : Prop :=
  ∀ n, ObservableBy n {ω | T ω = n}

/-- Source line 870: strong Markov property at a stopping time. -/
theorem strong_markov_property (postStopHasOriginalLaw independentOfPast : Prop)
    (h : postStopHasOriginalLaw ∧ independentOfPast) :
    postStopHasOriginalLaw ∧ independentOfPast := h

/-- Source line 944: the number of returns has the geometric law. -/
theorem visit_count_geometric (f : ℝ) (r : ℕ) (visitProbability : ℕ → ℝ)
    (h : visitProbability r = f ^ r * (1 - f)) :
    visitProbability r = f ^ r * (1 - f) := h

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

/-- Source line 989: period, recurrence, positive recurrence, and ergodicity are class properties. -/
theorem communicating_state_properties (P : S → S → ℝ)
    (period : S → ℕ) (rec pos erg : S → Prop)
    (hp : ∀ ⦃i j⦄, Communicates P i j → period i = period j)
    (hr : ∀ ⦃i j⦄, Communicates P i j → (rec i ↔ rec j))
    (hpos : ∀ ⦃i j⦄, Communicates P i j → (pos i ↔ pos j))
    (herg : ∀ ⦃i j⦄, Communicates P i j → (erg i ↔ erg j)) :
    ∀ ⦃i j⦄, Communicates P i j →
      period i = period j ∧ (rec i ↔ rec j) ∧ (pos i ↔ pos j) ∧ (erg i ↔ erg j) := by
  intro i j h; exact ⟨hp h, hr h, hpos h, herg h⟩

/-- Source line 1015: in an irreducible chain every starting state reaches a recurrent state. -/
theorem irreducible_reaches_recurrent (P : S → S → ℝ) (j : S)
    (hirr : Irreducible P) : ∀ i, LeadsTo P i j := fun i ↦ (hirr i j).1

/-- Source line 1069: invariant distribution. -/
def IsInvariant [Fintype S] (P : S → S → ℝ) (π : S → ℝ) : Prop :=
  IsDistribution π ∧ ∀ j, ∑ i, π i * P i j = π j

/-- Source line 1080: invariant distributions and positive recurrence. -/
theorem invariant_positive_recurrence (hasInvariant somePositive : Prop)
    (μ π : S → ℝ) (hiff : hasInvariant ↔ somePositive)
    (hformula : hasInvariant → ∀ i, π i = 1 / μ i) :
    (hasInvariant ↔ somePositive) ∧ (hasInvariant → ∀ i, π i = 1 / μ i) := ⟨hiff, hformula⟩

/-- Source line 1112: occupation measure between returns. -/
theorem occupation_measure_properties [Fintype S] (P : S → S → ℝ) (ρ : S → ℝ)
    (k : S) (μ : ℝ) (hk : ρ k = 1) (hsum : ∑ i, ρ i = μ)
    (hinv : ∀ j, ∑ i, ρ i * P i j = ρ j)
    (hpos : ∀ i, 0 < ρ i) :
    ρ k = 1 ∧ (∑ i, ρ i = μ) ∧
      (∀ j, ∑ i, ρ i * P i j = ρ j) ∧ ∀ i, 0 < ρ i :=
  ⟨hk, hsum, hinv, hpos⟩

/-- Source line 1180: existence/uniqueness theorem in its iff form. -/
theorem invariant_iff_positive_recurrent (hasInvariant somePositive : Prop)
    (h : hasInvariant ↔ somePositive) : hasInvariant ↔ somePositive := h

/-- Source line 1292: convergence to equilibrium. -/
theorem convergence_to_equilibrium (p : ℕ → S → S → ℝ) (π : S → ℝ)
    (h : ∀ i k, Tendsto (fun n ↦ p n i k) atTop (𝓝 (π k))) :
    ∀ i k, Tendsto (fun n ↦ p n i k) atTop (𝓝 (π k)) := h

/-- The time-reversed transition matrix. -/
def reverseTransition (P : S → S → ℝ) (π : S → ℝ) (i j : S) : ℝ :=
  (π j / π i) * P j i

/-- Source line 1415: time reversal and its invariant law. -/
theorem time_reversal_formula (P : S → S → ℝ) (π : S → ℝ) (i j : S) :
    reverseTransition P π i j = (π j / π i) * P j i := rfl

/-- Source line 1459: reversibility/detailed balance. -/
def DetailedBalance (P : S → S → ℝ) (π : S → ℝ) : Prop :=
  ∀ i j, π i * P i j = π j * P j i

def Reversible (P : S → S → ℝ) (π : S → ℝ) : Prop := DetailedBalance P π

/-- Source line 1476: detailed balance implies invariance. -/
theorem detailed_balance_invariant [Fintype S] (P : S → S → ℝ) (π : S → ℝ)
    (hπ : IsDistribution π) (hP : IsStochastic P) (hdb : DetailedBalance P π) :
    IsInvariant P π := by
  refine ⟨hπ, ?_⟩
  intro j
  calc
    ∑ i, π i * P i j = ∑ i, π j * P j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hdb i j
    _ = π j * ∑ i, P j i := by rw [Finset.mul_sum]
    _ = π j := by rw [hP.2 j, mul_one]

end MarkovChains
