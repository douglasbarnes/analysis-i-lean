import AdvancedProbability.ContinuousTime

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

namespace SigmaField

/-- The whole space belongs to every sigma-field. -/
theorem univ_mem {Ω : Type u} (𝒢 : SigmaField Ω) : (Set.univ : Set Ω) ∈ 𝒢.sets := by
  simpa using 𝒢.compl_mem (∅ : Set Ω) 𝒢.empty_mem

/-- Sigma-fields are closed under binary unions. -/
theorem union_mem {Ω : Type u} (𝒢 : SigmaField Ω) {A B : Set Ω}
    (hA : A ∈ 𝒢.sets) (hB : B ∈ 𝒢.sets) : A ∪ B ∈ 𝒢.sets := by
  let C : ℕ → Set Ω := fun n ↦ if n = 0 then A else B
  have hC : ∀ n, C n ∈ 𝒢.sets := by
    intro n
    by_cases hn : n = 0
    · simpa [C, hn] using hA
    · simpa [C, hn] using hB
  have hUnion := 𝒢.iUnion_mem C hC
  have hEq : (⋃ n, C n) = A ∪ B := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      by_cases h0 : n = 0
      · exact Or.inl (by simpa [C, h0] using hn)
      · exact Or.inr (by simpa [C, h0] using hn)
    · intro hx
      rw [Set.mem_iUnion]
      rcases hx with hx | hx
      · exact ⟨0, by simpa [C] using hx⟩
      · exact ⟨1, by simpa [C] using hx⟩
  rw [hEq] at hUnion
  exact hUnion

/-- Sigma-fields are closed under binary intersections. -/
theorem inter_mem {Ω : Type u} (𝒢 : SigmaField Ω) {A B : Set Ω}
    (hA : A ∈ 𝒢.sets) (hB : B ∈ 𝒢.sets) : A ∩ B ∈ 𝒢.sets := by
  have hAc : Aᶜ ∈ 𝒢.sets := 𝒢.compl_mem A hA
  have hBc : Bᶜ ∈ 𝒢.sets := 𝒢.compl_mem B hB
  have hUnion : Aᶜ ∪ Bᶜ ∈ 𝒢.sets := 𝒢.union_mem hAc hBc
  have hCompl : (Aᶜ ∪ Bᶜ)ᶜ ∈ 𝒢.sets := 𝒢.compl_mem (Aᶜ ∪ Bᶜ) hUnion
  simpa only [compl_union, compl_compl] using hCompl

end SigmaField

/-- Source 62: pointwise maxima and minima of extended-valued continuous-time stopping times are
stopping times. -/
theorem ContinuousStoppingCalculusTheorem {Ω : Type u} (ℱ : ContinuousFiltration Ω) :
    (∀ S T : Ω → WithTop ℝ≥0, IsContinuousStoppingTime ℱ S → IsContinuousStoppingTime ℱ T →
      IsContinuousStoppingTime ℱ (fun ω ↦ max (S ω) (T ω))) ∧
    (∀ S T : Ω → WithTop ℝ≥0, IsContinuousStoppingTime ℱ S → IsContinuousStoppingTime ℱ T →
      IsContinuousStoppingTime ℱ (fun ω ↦ min (S ω) (T ω))) := by
  constructor
  · intro S T hS hT t
    have hInter := (ℱ.sigma t).inter_mem (hS t) (hT t)
    have hEq : {ω | max (S ω) (T ω) ≤ t} = {ω | S ω ≤ t} ∩ {ω | T ω ≤ t} := by
      ext ω
      simp
    rw [hEq]
    exact hInter
  · intro S T hS hT t
    have hUnion := (ℱ.sigma t).union_mem (hS t) (hT t)
    have hEq : {ω | min (S ω) (T ω) ≤ t} = {ω | S ω ≤ t} ∪ {ω | T ω ≤ t} := by
      ext ω
      simp
    rw [hEq]
    exact hUnion

/-- The sigma-field of events observable at a continuous stopping time. -/
def continuousStoppingSigmaField {Ω : Type u} (ℱ : ContinuousFiltration Ω)
    (T : Ω → WithTop ℝ≥0) (hT : IsContinuousStoppingTime ℱ T) : SigmaField Ω where
  sets := {A | ∀ t, A ∩ {ω | T ω ≤ t} ∈ (ℱ.sigma t).sets}
  empty_mem := by
    intro t
    simpa using (ℱ.sigma t).empty_mem
  compl_mem := by
    intro A hA t
    have hComp : (A ∩ {ω | T ω ≤ t})ᶜ ∈ (ℱ.sigma t).sets :=
      (ℱ.sigma t).compl_mem _ (hA t)
    have hInter := (ℱ.sigma t).inter_mem hComp (hT t)
    have hEq : (A ∩ {ω | T ω ≤ t})ᶜ ∩ {ω | T ω ≤ t} =
        Aᶜ ∩ {ω | T ω ≤ t} := by
      ext ω
      constructor
      · rintro ⟨hNot, hLe⟩
        refine ⟨?_, hLe⟩
        intro hAω
        exact hNot ⟨hAω, hLe⟩
      · rintro ⟨hNotA, hLe⟩
        refine ⟨?_, hLe⟩
        rintro ⟨hAω, -⟩
        exact hNotA hAω
    rw [hEq] at hInter
    exact hInter
  iUnion_mem := by
    intro A hA t
    have hUnion := (ℱ.sigma t).iUnion_mem
      (fun n ↦ A n ∩ {ω | T ω ≤ t}) (fun n ↦ hA n t)
    simpa only [Set.iUnion_inter] using hUnion

/-- Source 62(2): if `S ≤ T`, then every event observable at `S` is observable at `T`. -/
theorem continuousStoppingSigmaField_mono {Ω : Type u} (ℱ : ContinuousFiltration Ω)
    {S T : Ω → WithTop ℝ≥0} (hS : IsContinuousStoppingTime ℱ S)
    (hT : IsContinuousStoppingTime ℱ T) (hST : S ≤ T) :
    (continuousStoppingSigmaField ℱ S hS).Subfield
      (continuousStoppingSigmaField ℱ T hT) := by
  intro A hA t
  have hAS : A ∩ {ω | S ω ≤ t} ∈ (ℱ.sigma t).sets := hA t
  have hTt : {ω | T ω ≤ t} ∈ (ℱ.sigma t).sets := hT t
  have hInter := (ℱ.sigma t).inter_mem hAS hTt
  have hEq : (A ∩ {ω | S ω ≤ t}) ∩ {ω | T ω ≤ t} =
      A ∩ {ω | T ω ≤ t} := by
    ext ω
    constructor
    · rintro ⟨⟨hAω, -⟩, hTω⟩
      exact ⟨hAω, hTω⟩
    · rintro ⟨hAω, hTω⟩
      exact ⟨⟨hAω, (hST ω).trans hTω⟩, hTω⟩
  rw [hEq] at hInter
  exact hInter

/-- Source 63: a real random variable is measurable at a stopping time iff each localization
`Z 1_{T ≤ t}` is measurable at deterministic time `t`. -/
theorem StoppingSigmaMeasurabilityTheorem {Ω : Type u} (ℱ : ContinuousFiltration Ω)
    (T : Ω → WithTop ℝ≥0) (hT : IsContinuousStoppingTime ℱ T) (Z : Ω → ℝ) :
    Observable (continuousStoppingSigmaField ℱ T hT) Z ↔
      ∀ t, Observable (ℱ.sigma t) ({ω | T ω ≤ t}.indicator Z) := by
  constructor
  · intro hZ t B hB
    let E : Set Ω := {ω | T ω ≤ t}
    have hE : E ∈ (ℱ.sigma t).sets := hT t
    have hZE : Z ⁻¹' B ∩ E ∈ (ℱ.sigma t).sets := by
      exact hZ B hB t
    by_cases h0 : (0 : ℝ) ∈ B
    · have hUnion := (ℱ.sigma t).union_mem hZE ((ℱ.sigma t).compl_mem E hE)
      have hEq : E.indicator Z ⁻¹' B = (Z ⁻¹' B ∩ E) ∪ Eᶜ := by
        ext ω
        by_cases hω : ω ∈ E <;> simp [Set.indicator, hω, h0]
      rw [hEq]
      exact hUnion
    · have hEq : E.indicator Z ⁻¹' B = Z ⁻¹' B ∩ E := by
        ext ω
        by_cases hω : ω ∈ E <;> simp [Set.indicator, hω, h0]
      rw [hEq]
      exact hZE
  · intro hLocal B hB t
    let E : Set Ω := {ω | T ω ≤ t}
    have hInd : E.indicator Z ⁻¹' B ∈ (ℱ.sigma t).sets := hLocal t B hB
    have hInter := (ℱ.sigma t).inter_mem hInd (hT t)
    have hEq : (E.indicator Z ⁻¹' B) ∩ E = Z ⁻¹' B ∩ E := by
      ext ω
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
    rw [hEq] at hInter
    exact hInter

end AdvancedProbability