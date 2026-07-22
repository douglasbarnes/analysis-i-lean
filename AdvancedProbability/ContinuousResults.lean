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

/-- Source 62: pointwise maxima and minima of continuous-time stopping times are stopping times. -/
theorem ContinuousStoppingCalculusTheorem {Ω : Type u} (ℱ : ContinuousFiltration Ω) :
    (∀ S T : Ω → ℝ≥0, IsContinuousStoppingTime ℱ S → IsContinuousStoppingTime ℱ T →
      IsContinuousStoppingTime ℱ (fun ω ↦ max (S ω) (T ω))) ∧
    (∀ S T : Ω → ℝ≥0, IsContinuousStoppingTime ℱ S → IsContinuousStoppingTime ℱ T →
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

end AdvancedProbability
