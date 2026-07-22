import Mathlib

/-!
# Probability and Measure: foundations

Course-facing declarations for the opening measure-theory part of
`II_M/probability_and_measure.tex`.  Standard notions are identified with their Mathlib
counterparts; the weaker set-system notions used in the notes are recorded explicitly.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- A sigma-algebra is Mathlib's measurable-space structure. -/
abbrev SigmaAlgebra (α : Type*) := MeasurableSpace α

/-- A measure on a fixed measurable space. -/
abbrev MeasureOn (α : Type*) [MeasurableSpace α] := Measure α

/-- A probability measure has total mass one. -/
abbrev ProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :=
  IsProbabilityMeasure P

/-- The underlying type of outcomes. -/
abbrev SampleSpace := Type*

/-- Events are subsets of the sample space; measurability is stated separately. -/
abbrev Event (Ω : Type*) := Set Ω

/-- The Borel measure used throughout the real-line examples. -/
noncomputable abbrev lebesgueMeasure : Measure ℝ := volume

/-- A pi-system, in the convention of the source notes (including the empty set). -/
def PiSystem {α : Type*} (C : Set (Set α)) : Prop :=
  ∅ ∈ C ∧ ∀ ⦃A B : Set α⦄, A ∈ C → B ∈ C → A ∩ B ∈ C

/-- A Dynkin system (d-system), using increasing unions. -/
def DynkinSystem {α : Type*} (C : Set (Set α)) : Prop :=
  Set.univ ∈ C ∧
    (∀ ⦃A B : Set α⦄, A ∈ C → B ∈ C → A ⊆ B → B \ A ∈ C) ∧
    ∀ A : ℕ → Set α, (∀ n, A n ∈ C) → Monotone A → (⋃ n, A n) ∈ C

/-- A ring of sets. -/
def RingOfSets {α : Type*} (C : Set (Set α)) : Prop :=
  ∅ ∈ C ∧
    ∀ ⦃A B : Set α⦄, A ∈ C → B ∈ C → B \ A ∈ C ∧ A ∪ B ∈ C

/-- An algebra of sets. -/
def AlgebraOfSets {α : Type*} (C : Set (Set α)) : Prop :=
  ∅ ∈ C ∧
    ∀ ⦃A B : Set α⦄, A ∈ C → B ∈ C → Aᶜ ∈ C ∧ A ∪ B ∈ C

/-- A non-negative extended-real set function on all subsets. -/
def SetFunction (α : Type*) := Set α → ℝ≥0∞

/-- Monotonicity of a set function. -/
def IsIncreasingSetFunction {α : Type*} (m : SetFunction α) : Prop := Monotone m

/-- Finite additivity on disjoint sets, together with the empty-set axiom. -/
def IsAdditiveSetFunction {α : Type*} (m : SetFunction α) : Prop :=
  m ∅ = 0 ∧ ∀ A B : Set α, Disjoint A B → m (A ∪ B) = m A + m B

/-- Countable additivity on disjoint sequences. -/
def IsCountablyAdditiveSetFunction {α : Type*} (m : SetFunction α) : Prop :=
  m ∅ = 0 ∧
    ∀ A : ℕ → Set α, Pairwise (Function.onFun Disjoint A) →
      m (⋃ n, A n) = ∑' n, m (A n)

/-- Countable subadditivity. -/
def IsCountablySubadditiveSetFunction {α : Type*} (m : SetFunction α) : Prop :=
  m ∅ = 0 ∧ ∀ A : ℕ → Set α, m (⋃ n, A n) ≤ ∑' n, m (A n)

/-- The empty set has measure zero. -/
theorem measure_empty_source {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    μ ∅ = 0 :=
  measure_empty

/-- Measures are monotone. -/
theorem measure_mono_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A B : Set α} (hAB : A ⊆ B) : μ A ≤ μ B :=
  measure_mono hAB

/-- Countable subadditivity (Boole's inequality). -/
theorem measure_iUnion_le_source {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (A : ι → Set α) : μ (⋃ i, A i) ≤ ∑' i, μ (A i) :=
  measure_iUnion_le A

/-- Continuity from below for an increasing sequence of measurable sets. -/
theorem measure_continuous_iUnion_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : ℕ → Set α) (hmono : Monotone A) :
    Tendsto (fun n ↦ μ (A n)) atTop (𝓝 (μ (⋃ n, A n))) :=
  tendsto_measure_iUnion_atTop hmono

/-- Two-set inclusion-exclusion. -/
theorem measure_union_add_inter_source {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A B : Set α) (hB : MeasurableSet B) :
    μ (A ∪ B) + μ (A ∩ B) = μ A + μ B :=
  measure_union_add_inter A hB

/-- Complementation in a probability space. -/
theorem probability_compl_source {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) :
    P Aᶜ = 1 - P A :=
  prob_compl_eq_one_sub hA

end ProbabilityAndMeasure
