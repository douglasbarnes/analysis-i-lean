import AdvancedProbability.DiscreteResults

noncomputable section

open scoped BigOperators ENNReal NNReal Topology MeasureTheory ProbabilityTheory Function
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- Countable pointwise suprema of discrete stopping times are stopping times. -/
theorem isStoppingTime_iSup {Ω ι : Type*} [Countable ι] [m₀ : MeasurableSpace Ω]
    {ℱ : Filtration ℕ m₀} {T : ι → Ω → ℕ∞}
    (hT : ∀ i, IsStoppingTime ℱ (T i)) :
    IsStoppingTime ℱ (fun ω ↦ ⨆ i, T i ω) := by
  intro n
  change MeasurableSet[ℱ n] {ω | (⨆ i, T i ω) ≤ n}
  have hEq : {ω | (⨆ i, T i ω) ≤ n} = ⋂ i, {ω | T i ω ≤ n} := by
    ext ω
    simp
  rw [hEq]
  exact MeasurableSet.iInter fun i ↦ hT i n

/-- Nonempty countable pointwise infima of `ℕ∞`-valued stopping times are stopping times. -/
theorem isStoppingTime_iInf {Ω ι : Type*} [Countable ι] [Nonempty ι]
    [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {T : ι → Ω → ℕ∞}
    (hT : ∀ i, IsStoppingTime ℱ (T i)) :
    IsStoppingTime ℱ (fun ω ↦ ⨅ i, T i ω) := by
  intro n
  change MeasurableSet[ℱ n] {ω | (⨅ i, T i ω) ≤ n}
  have hEq : {ω | (⨅ i, T i ω) ≤ n} = ⋃ i, {ω | T i ω ≤ n} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨i, hi⟩ := ENat.exists_eq_iInf (fun i ↦ T i ω)
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      simpa [hi] using hω
    · intro hω
      rw [Set.mem_iUnion] at hω
      obtain ⟨i, hi⟩ := hω
      exact (iInf_le (fun i ↦ T i ω) i).trans hi
  rw [hEq]
  exact MeasurableSet.iUnion fun i ↦ hT i n

/-- Pointwise limsups of sequences of discrete stopping times are stopping times. -/
theorem isStoppingTime_limsup {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {ℱ : Filtration ℕ m₀} {T : ℕ → Ω → ℕ∞}
    (hT : ∀ i, IsStoppingTime ℱ (T i)) :
    IsStoppingTime ℱ (fun ω ↦ limsup (fun i ↦ T i ω) atTop) := by
  have hEq :
      (fun ω ↦ limsup (fun i ↦ T i ω) atTop) =
        fun ω ↦ ⨅ n : ℕ, ⨆ i : {i : ℕ // n ≤ i}, T i.1 ω := by
    funext ω
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    congr with n
    apply le_antisymm
    · exact iSup_le fun i ↦ iSup_le fun hi ↦
        le_iSup_of_le (⟨i, hi⟩ : {i : ℕ // n ≤ i}) le_rfl
    · exact iSup_le fun i ↦
        le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
  have hRhs : IsStoppingTime ℱ
      (fun ω ↦ ⨅ n : ℕ, ⨆ i : {i : ℕ // n ≤ i}, T i.1 ω) := by
    apply isStoppingTime_iInf
    intro n
    apply isStoppingTime_iSup
    intro i
    exact hT i.1
  exact hEq.symm ▸ hRhs

/-- Pointwise liminfs of sequences of discrete stopping times are stopping times. -/
theorem isStoppingTime_liminf {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {ℱ : Filtration ℕ m₀} {T : ℕ → Ω → ℕ∞}
    (hT : ∀ i, IsStoppingTime ℱ (T i)) :
    IsStoppingTime ℱ (fun ω ↦ liminf (fun i ↦ T i ω) atTop) := by
  have hEq :
      (fun ω ↦ liminf (fun i ↦ T i ω) atTop) =
        fun ω ↦ ⨆ n : ℕ, ⨅ i : {i : ℕ // n ≤ i}, T i.1 ω := by
    funext ω
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    congr with n
    apply le_antisymm
    · refine le_iInf fun i : {i : ℕ // n ≤ i} ↦ ?_
      exact iInf_le_of_le i.1 (iInf_le_of_le i.2 le_rfl)
    · refine le_iInf fun i : ℕ ↦ le_iInf fun hi : n ≤ i ↦ ?_
      exact iInf_le (fun j : {j : ℕ // n ≤ j} ↦ T j.1 ω) ⟨i, hi⟩
  have hRhs : IsStoppingTime ℱ
      (fun ω ↦ ⨆ n : ℕ, ⨅ i : {i : ℕ // n ≤ i}, T i.1 ω) := by
    apply isStoppingTime_iSup
    intro n
    letI : Nonempty {i : ℕ // n ≤ i} := ⟨⟨n, le_rfl⟩⟩
    apply isStoppingTime_iInf
    intro i
    exact hT i.1
  exact hEq.symm ▸ hRhs

/-- Source 32: the complete discrete stopping-time calculus from the notes. -/
theorem DiscreteStoppingCalculusTheorem {Ω : Type u} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} {ℱ : Filtration ℕ m₀} {X : ℕ → Ω → ℝ}
    (hX_adapted : StronglyAdapted ℱ X) (hX_integrable : ∀ n, Integrable (X n) μ) :
    (∀ S T : Ω → ℕ∞, IsStoppingTime ℱ S → IsStoppingTime ℱ T →
      IsStoppingTime ℱ (fun ω ↦ max (S ω) (T ω))) ∧
    (∀ S T : Ω → ℕ∞, IsStoppingTime ℱ S → IsStoppingTime ℱ T →
      IsStoppingTime ℱ (fun ω ↦ min (S ω) (T ω))) ∧
    (∀ T : ℕ → Ω → ℕ∞, (∀ n, IsStoppingTime ℱ (T n)) →
      IsStoppingTime ℱ (fun ω ↦ ⨆ n, T n ω)) ∧
    (∀ T : ℕ → Ω → ℕ∞, (∀ n, IsStoppingTime ℱ (T n)) →
      IsStoppingTime ℱ (fun ω ↦ ⨅ n, T n ω)) ∧
    (∀ T : ℕ → Ω → ℕ∞, (∀ n, IsStoppingTime ℱ (T n)) →
      IsStoppingTime ℱ (fun ω ↦ limsup (fun n ↦ T n ω) atTop)) ∧
    (∀ T : ℕ → Ω → ℕ∞, (∀ n, IsStoppingTime ℱ (T n)) →
      IsStoppingTime ℱ (fun ω ↦ liminf (fun n ↦ T n ω) atTop)) ∧
    (∀ S T : Ω → ℕ∞, (hS : IsStoppingTime ℱ S) → (hT : IsStoppingTime ℱ T) →
      S ≤ T → hS.measurableSpace ≤ hT.measurableSpace) ∧
    (∀ T : Ω → ℕ∞, (hT : IsStoppingTime ℱ T) →
      Measurable[hT.measurableSpace]
        ({ω | T ω ≠ ⊤}.indicator (MeasureTheory.stoppedValue X T))) ∧
    (∀ T : Ω → ℕ∞, IsStoppingTime ℱ T →
      StronglyAdapted ℱ (MeasureTheory.stoppedProcess X T)) ∧
    (∀ T : Ω → ℕ∞, IsStoppingTime ℱ T → ∀ n,
      Integrable (MeasureTheory.stoppedProcess X T n) μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S T hS hT
    exact hS.max hT
  · intro S T hS hT
    exact hS.min hT
  · intro T hT
    exact isStoppingTime_iSup hT
  · intro T hT
    exact isStoppingTime_iInf hT
  · intro T hT
    exact isStoppingTime_limsup hT
  · intro T hT
    exact isStoppingTime_liminf hT
  · intro S T hS hT hST
    exact hS.measurableSpace_mono hT hST
  · intro T hT
    have hStopped : Measurable[hT.measurableSpace] (MeasureTheory.stoppedValue X T) :=
      MeasureTheory.measurable_stoppedValue
        hX_adapted.isStronglyProgressive_of_discrete hT
    have hFiniteEq : {ω | T ω ≠ ⊤} = ⋃ n : ℕ, {ω | T ω = (n : ℕ∞)} := by
      ext ω
      cases h : T ω with
      | top => simp [h]
      | coe n => simp [h]
    have hFinite : MeasurableSet[hT.measurableSpace] {ω | T ω ≠ ⊤} := by
      rw [hFiniteEq]
      exact MeasurableSet.iUnion fun n ↦ hT.measurableSet_eq_of_countable' n
    exact hStopped.indicator hFinite
  · intro T hT
    exact hX_adapted.stoppedProcess_of_discrete hT
  · intro T hT n
    exact integrable_stoppedProcess hT hX_integrable n

end AdvancedProbability
