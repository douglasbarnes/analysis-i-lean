/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.LocalClasses

/-!
# Chapter 3: Interface lemmas

Elementary consequences of the source-order interfaces.  Every declaration in
this file has a proof term; no analytical concentration theorem is assumed.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set Filter

namespace InfiniteDimensionalStatistics
namespace Chapter03

section CoordinateReplacement

variable {S : Type*} {n : ℕ}

@[simp] theorem replaceCoordinate_same (x : Fin n → S) (k : Fin n) :
    replaceCoordinate x k (x k) = x := by
  funext i
  by_cases h : i = k
  · subst h
    simp [replaceCoordinate]
  · simp [replaceCoordinate, Function.update_noteq h]

@[simp] theorem replaceCoordinate_apply_same
    (x : Fin n → S) (k : Fin n) (y : S) :
    replaceCoordinate x k y k = y := by
  simp [replaceCoordinate]

@[simp] theorem replaceCoordinate_apply_ne
    (x : Fin n → S) {i k : Fin n} (h : i ≠ k) (y : S) :
    replaceCoordinate x k y i = x i := by
  simp [replaceCoordinate, Function.update_noteq h]

@[refl] theorem agreeOff_refl (k : Fin n) (x : Fin n → S) :
    AgreeOff k x x := by
  intro i _
  rfl

@[symm] theorem agreeOff_symm {k : Fin n} {x y : Fin n → S}
    (h : AgreeOff k x y) : AgreeOff k y x := by
  intro i hi
  exact (h i hi).symm

@[trans] theorem agreeOff_trans {k : Fin n} {x y z : Fin n → S}
    (hxy : AgreeOff k x y) (hyz : AgreeOff k y z) : AgreeOff k x z := by
  intro i hi
  exact (hxy i hi).trans (hyz i hi)

/-- Replacing coordinate `k` leaves all other coordinates unchanged. -/
theorem agreeOff_replaceCoordinate
    (x : Fin n → S) (k : Fin n) (y : S) :
    AgreeOff k x (replaceCoordinate x k y) := by
  intro i hi
  exact (replaceCoordinate_apply_ne x hi y).symm

end CoordinateReplacement

section EntropyFunctions

@[simp] theorem entropyPhi_zero : entropyPhi 0 = 0 := by
  simp [entropyPhi]

@[simp] theorem bennettFunction_zero' : bennettFunction 0 = 0 := by
  simp [bennettFunction]

end EntropyFunctions

section EmpiricalMetrics

variable {S : Type*} [MeasurableSpace S]

@[simp] theorem empiricalL2PseudoMetric_self {n : ℕ}
    (X : Fin n → S) (f : S → ℝ) :
    empiricalL2PseudoMetric X f f = 0 := by
  simp [empiricalL2PseudoMetric, empiricalMean]

@[simp] theorem empiricalL1PseudoMetric_self {n : ℕ}
    (X : Fin n → S) (f : S → ℝ) :
    empiricalL1PseudoMetric X f f = 0 := by
  simp [empiricalL1PseudoMetric, empiricalMean]

@[simp] theorem measureL2PseudoMetric_self
    (P : Measure S) (f : S → ℝ) :
    measureL2PseudoMetric P f f = 0 := by
  simp [measureL2PseudoMetric, measureL2Seminorm]

@[simp] theorem brownianMotionMetric_self
    (P : Measure S) (f : S → ℝ) :
    brownianMotionMetric P f f = 0 := by
  exact measureL2PseudoMetric_self P f

@[simp] theorem populationSquaredL2_zero (P : Measure S) :
    populationSquaredL2 P (fun _ ↦ 0) = 0 := by
  simp [populationSquaredL2]

/-- The zero function belongs to the difference class of any nonempty class. -/
theorem zero_mem_differenceClass {𝓕 : Set (S → ℝ)}
    (h𝓕 : 𝓕.Nonempty) : (fun _ ↦ 0) ∈ differenceClass 𝓕 := by
  rcases h𝓕 with ⟨f, hf⟩
  exact ⟨f, hf, f, hf, by funext x; simp⟩

/-- A nonempty class has zero in every nonnegative population localisation. -/
theorem zero_mem_populationLocalDifferenceClass
    (P : Measure S) {𝓕 : Set (S → ℝ)} (h𝓕 : 𝓕.Nonempty)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (fun _ ↦ 0) ∈ populationLocalDifferenceClass P 𝓕 δ := by
  exact ⟨zero_mem_differenceClass h𝓕, by simp [populationSquaredL2, hδ]⟩

end EmpiricalMetrics

section BridgeMetrics

variable {S : Type*} [MeasurableSpace S]

@[simp] theorem brownianBridgeCovariance_zero_left
    (P : Measure S) (f : S → ℝ) :
    brownianBridgeCovariance P (fun _ ↦ 0) f = 0 := by
  simp [brownianBridgeCovariance]

@[simp] theorem brownianBridgeCovariance_zero_right
    (P : Measure S) (f : S → ℝ) :
    brownianBridgeCovariance P f (fun _ ↦ 0) = 0 := by
  simp [brownianBridgeCovariance]

@[simp] theorem brownianBridgeMetric_self
    (P : Measure S) (f : S → ℝ) :
    brownianBridgeMetric P f f = 0 := by
  simp [brownianBridgeMetric, brownianBridgeCovariance]

end BridgeMetrics

section Shattering

variable {α : Type*}

/-- Enlarging a set class preserves shattering. -/
theorem Shatters.mono_class {𝓒 𝓓 : Set (Set α)} {A : Finset α}
    (h𝓒𝓓 : 𝓒 ⊆ 𝓓) (hA : Shatters 𝓒 A) : Shatters 𝓓 A := by
  unfold Shatters at hA ⊢
  ext B
  constructor
  · exact setClassTrace_subset_powerset 𝓓 A
  · intro hB
    rw [← hA] at hB
    rcases hB with ⟨C, hC, rfl⟩
    exact ⟨C, h𝓒𝓓 hC, rfl⟩

/-- Every subset of a shattered finite set is shattered. -/
theorem Shatters.mono_finset {𝓒 : Set (Set α)} {A B : Finset α}
    (hBA : B ⊆ A) (hA : Shatters 𝓒 A) : Shatters 𝓒 B := by
  unfold Shatters at hA ⊢
  ext U
  constructor
  · exact setClassTrace_subset_powerset 𝓒 B
  · intro hUB
    have hUA : U ⊆ (A : Set α) :=
      hUB.trans fun x hx ↦ hBA hx
    have hUtrace : U ∈ setClassTrace 𝓒 A := by
      rw [hA]
      exact hUA
    rcases hUtrace with ⟨C, hC, hCU⟩
    refine ⟨C, hC, ?_⟩
    ext x
    constructor
    · rintro ⟨hxC, hxB⟩
      have hxA : x ∈ (A : Set α) := hBA hxB
      have hxU : x ∈ U := by
        rw [← hCU]
        exact ⟨hxC, hxA⟩
      exact hxU
    · intro hxU
      have hxA : x ∈ (A : Set α) := hUA hxU
      have hxC : x ∈ C := by
        have : x ∈ C ∩ (A : Set α) := by
          rw [hCU]
          exact hxU
        exact this.1
      exact ⟨hxC, hUB hxU⟩

end Shattering

section FunctionClasses

variable {S : Type*}

/-- Every class is contained in its symmetric convex hull. -/
theorem subset_symmetricConvexHull (𝓕 : Set (S → ℝ)) :
    𝓕 ⊆ symmetricConvexHull 𝓕 := by
  intro f hf
  exact subset_convexHull ℝ (subset_symmetricHull 𝓕 hf)

/-- Difference classes are symmetric. -/
theorem neg_mem_differenceClass {𝓕 : Set (S → ℝ)} {h : S → ℝ}
    (hh : h ∈ differenceClass 𝓕) :
    (fun x ↦ -h x) ∈ differenceClass 𝓕 := by
  rcases hh with ⟨f, hf, g, hg, rfl⟩
  exact ⟨g, hg, f, hf, by funext x; ring⟩

end FunctionClasses

end Chapter03
end InfiniteDimensionalStatistics
