/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.LorentzLemmas

/-!
# Chapter 3: VC trace and function-class structure

Exact set identities and monotonicity statements for traces, set classes,
subgraphs, thresholds, indicators, envelopes and VC-subgraph classes.  These do
not use the source-sensitive quantitative bounds in Proposition 3.6.7 or
Theorem 3.6.9.
-/

noncomputable section

open Set
open scoped ENNReal

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Traces

variable {α : Type*}

/-- The trace operation is monotone in the set class. -/
theorem setClassTrace_mono
    {𝓒 𝓓 : Set (Set α)} (h𝓒𝓓 : 𝓒 ⊆ 𝓓) (A : Finset α) :
    setClassTrace 𝓒 A ⊆ setClassTrace 𝓓 A := by
  rintro B ⟨C, hC, rfl⟩
  exact ⟨C, h𝓒𝓓 hC, rfl⟩

/-- Tracing a union of set classes gives the union of the traces. -/
theorem setClassTrace_union
    (𝓒 𝓓 : Set (Set α)) (A : Finset α) :
    setClassTrace (𝓒 ∪ 𝓓) A =
      setClassTrace 𝓒 A ∪ setClassTrace 𝓓 A := by
  ext B
  constructor
  · rintro ⟨C, hC | hC, rfl⟩
    · exact Or.inl ⟨C, hC, rfl⟩
    · exact Or.inr ⟨C, hC, rfl⟩
  · rintro (⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩)
    · exact ⟨C, Or.inl hC, rfl⟩
    · exact ⟨C, Or.inr hC, rfl⟩

/-- The empty set class has empty trace. -/
@[simp] theorem setClassTrace_empty (A : Finset α) :
    setClassTrace (∅ : Set (Set α)) A = ∅ := by
  ext B
  simp [setClassTrace]

/-- A singleton set class has the corresponding singleton trace. -/
@[simp] theorem setClassTrace_singleton
    (C : Set α) (A : Finset α) :
    setClassTrace ({C} : Set (Set α)) A = {C ∩ (A : Set α)} := by
  ext B
  simp [setClassTrace]

/-- A subclass of a VC class is a VC class. -/
theorem IsVCClass.mono
    {𝓒 𝓓 : Set (Set α)} (h𝓓 : IsVCClass 𝓓) (h𝓒𝓓 : 𝓒 ⊆ 𝓓) :
    IsVCClass 𝓒 := by
  unfold IsVCClass at h𝓓 ⊢
  exact (vcDimension_mono h𝓒𝓓).trans_lt h𝓓

end Traces

section FunctionClassMaps

variable {α : Type*}

/-- Subgraph classes are monotone in the underlying function class. -/
theorem subgraphClass_mono
    {𝓕 𝓖 : Set (α → ℝ)} (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    subgraphClass 𝓕 ⊆ subgraphClass 𝓖 := by
  rintro A ⟨f, hf, rfl⟩
  exact ⟨f, h𝓕𝓖 hf, rfl⟩

/-- Threshold classes are monotone in the underlying function class. -/
theorem thresholdClass_mono
    {𝓕 𝓖 : Set (α → ℝ)} (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    thresholdClass 𝓕 ⊆ thresholdClass 𝓖 := by
  rintro A ⟨f, hf, t, rfl⟩
  exact ⟨f, h𝓕𝓖 hf, t, rfl⟩

/-- Indicator classes are monotone in the underlying set class. -/
theorem indicatorClass_mono
    {𝓒 𝓓 : Set (Set α)} (h𝓒𝓓 : 𝓒 ⊆ 𝓓) :
    indicatorClass 𝓒 ⊆ indicatorClass 𝓓 := by
  rintro f ⟨C, hC, rfl⟩
  exact ⟨C, h𝓒𝓓 hC, rfl⟩

/-- A subclass of a VC-subgraph class is VC-subgraph. -/
theorem IsVCSubgraphClass.mono
    {𝓕 𝓖 : Set (α → ℝ)}
    (h𝓖 : IsVCSubgraphClass 𝓖) (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    IsVCSubgraphClass 𝓕 := by
  unfold IsVCSubgraphClass at h𝓖 ⊢
  exact h𝓖.mono (subgraphClass_mono h𝓕𝓖)

end FunctionClassMaps

section Envelopes

variable {α : Type*}

/-- Restricting the function class preserves an envelope. -/
theorem IsEnvelope.mono_class
    {𝓕 𝓖 : Set (α → ℝ)} {F : α → ℝ}
    (hF : IsEnvelope 𝓖 F) (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    IsEnvelope 𝓕 F := by
  intro f hf x
  exact hF f (h𝓕𝓖 hf) x

/-- Increasing an envelope pointwise preserves the envelope property. -/
theorem IsEnvelope.mono_function
    {𝓕 : Set (α → ℝ)} {F G : α → ℝ}
    (hF : IsEnvelope 𝓕 F) (hFG : F ≤ G) :
    IsEnvelope 𝓕 G := by
  intro f hf x
  exact (hF f hf x).trans (hFG x)

/-- Restricting a uniformly bounded class preserves the same bound. -/
theorem IsUniformlyBounded.mono_class
    {𝓕 𝓖 : Set (α → ℝ)} {M : ℝ}
    (hM : IsUniformlyBounded 𝓖 M) (h𝓕𝓖 : 𝓕 ⊆ 𝓖) :
    IsUniformlyBounded 𝓕 M := by
  intro f hf x
  exact hM f (h𝓕𝓖 hf) x

/-- Increasing the uniform bound preserves uniform boundedness. -/
theorem IsUniformlyBounded.mono_bound
    {𝓕 : Set (α → ℝ)} {M N : ℝ}
    (hM : IsUniformlyBounded 𝓕 M) (hMN : M ≤ N) :
    IsUniformlyBounded 𝓕 N := by
  intro f hf x
  exact (hM f hf x).trans hMN

/-- Indicator classes are uniformly bounded by one. -/
theorem indicatorClass_uniformlyBounded_one (𝓒 : Set (Set α)) :
    IsUniformlyBounded (indicatorClass 𝓒) 1 := by
  intro f hf x
  rcases hf with ⟨C, hC, rfl⟩
  by_cases hx : x ∈ C <;> simp [hx]

end Envelopes

end Chapter03
end InfiniteDimensionalStatistics
