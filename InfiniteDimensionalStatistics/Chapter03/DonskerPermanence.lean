/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.McDiarmidReduction
import InfiniteDimensionalStatistics.Chapter03.GaussianPermanence
import InfiniteDimensionalStatistics.Chapter03.BoundedLipschitzLemmas

/-!
# Chapter 3: Donsker permanence under restriction

One-Lipschitz measurable maps contract the bounded-Lipschitz discrepancy and
therefore preserve the repository's measurable weak-convergence predicate.
Applying this to a coordinate-restriction map proves that Donsker processes and
concrete `P`-Donsker realisations restrict to subclasses, provided the chosen
function-space metrics make restriction one-Lipschitz.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace InfiniteDimensionalStatistics
namespace Chapter03

section BoundedLipschitzMapping

variable {E F : Type*}
  [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]

/-- One-Lipschitz push-forward contracts the bounded-Lipschitz discrepancy. -/
theorem boundedLipschitzDistance_map_le
    (P Q : Measure E) {f : E → F} (hf : LipschitzWith 1 f) :
    boundedLipschitzDistance (Measure.map f P) (Measure.map f Q) ≤
      boundedLipschitzDistance P Q := by
  unfold boundedLipschitzDistance
  refine iSup_le fun h => ?_
  let g : boundedLipschitzClass (E := E) :=
    ⟨fun x => h.1 (f x), by
      constructor
      · simpa using h.2.1.comp hf
      · intro x
        exact h.2.2 (f x)⟩
  have hfmeas : Measurable f := hf.continuous.measurable
  have hhmeas : AEStronglyMeasurable h.1 (Measure.map f P) := by
    exact h.2.1.continuous.measurable.aestronglyMeasurable
  have hhmeasQ : AEStronglyMeasurable h.1 (Measure.map f Q) := by
    exact h.2.1.continuous.measurable.aestronglyMeasurable
  calc
    ENNReal.ofReal
        |(∫ y, h.1 y ∂Measure.map f P) -
          ∫ y, h.1 y ∂Measure.map f Q| =
      ENNReal.ofReal
        |(∫ x, g.1 x ∂P) - ∫ x, g.1 x ∂Q| := by
      rw [integral_map hfmeas.aemeasurable hhmeas,
        integral_map hfmeas.aemeasurable hhmeasQ]
    _ ≤ ⨆ k : boundedLipschitzClass (E := E),
        ENNReal.ofReal
          |(∫ x, k.1 x ∂P) - ∫ x, k.1 x ∂Q| :=
      le_iSup (fun k : boundedLipschitzClass (E := E) =>
        ENNReal.ofReal
          |(∫ x, k.1 x ∂P) - ∫ x, k.1 x ∂Q|) g

/-- One-Lipschitz push-forward preserves bounded-Lipschitz weak convergence. -/
theorem WeaklyConverges.map_of_lipschitz
    {P : ℕ → Measure E} {Q : Measure E}
    (hP : WeaklyConverges P Q)
    {f : E → F} (hf : LipschitzWith 1 f) :
    WeaklyConverges (fun n => Measure.map f (P n)) (Measure.map f Q) := by
  unfold WeaklyConverges at hP ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hP
    (fun _ => bot_le)
    (fun n => boundedLipschitzDistance_map_le (P n) Q hf)

end BoundedLipschitzMapping

section ProcessRestriction

variable {S T U Ω Ω' : Type*}
  [MeasurableSpace S]
  [PseudoMetricSpace (T → ℝ)] [MeasurableSpace (T → ℝ)]
  [OpensMeasurableSpace (T → ℝ)]
  [PseudoMetricSpace (U → ℝ)] [MeasurableSpace (U → ℝ)]
  [BorelSpace (U → ℝ)]
  [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Coordinate restriction on process paths. -/
def restrictProcessPath (ι : U → T) : (T → ℝ) → (U → ℝ) :=
  fun x u => x (ι u)

/-- A Donsker process remains Donsker after one-Lipschitz reindexing. -/
theorem IsDonskerProcess.reindex
    (P : Measure S) (index : T → S → ℝ)
    (sampleLaw : ℕ → Measure Ω) (X : ℕ → T → Ω → ℝ)
    (limitLaw : Measure Ω') (G : T → Ω' → ℝ)
    (hX : IsDonskerProcess P index sampleLaw X limitLaw G)
    (ι : U → T)
    (hι : LipschitzWith 1 (restrictProcessPath ι)) :
    IsDonskerProcess P (fun u => index (ι u)) sampleLaw
      (fun n u ω => X n (ι u) ω) limitLaw
      (fun u ω => G (ι u) ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact hι.continuous.measurable.comp (hX.1 n)
  · exact hι.continuous.measurable.comp hX.2.1
  · intro s t
    exact hX.2.2.1 (ι s) (ι t)
  · let r := restrictProcessPath ι
    have hw := hX.2.2.2.map_of_lipschitz hι
    have hmapX (n : ℕ) :
        Measure.map r
            (Measure.map (fun ω t => X n t ω) (sampleLaw n)) =
          Measure.map (fun ω u => X n (ι u) ω) (sampleLaw n) := by
      rw [Measure.map_map hι.continuous.measurable (hX.1 n)]
      rfl
    have hmapG :
        Measure.map r
            (Measure.map (fun ω t => G t ω) limitLaw) =
          Measure.map (fun ω u => G (ι u) ω) limitLaw := by
      rw [Measure.map_map hι.continuous.measurable hX.2.1]
      rfl
    simpa only [hmapX, hmapG] using hw

end ProcessRestriction

section ClassRestriction

variable {S Ω Ω' : Type*}
  [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {𝓕 𝓖 : Set (S → ℝ)}
  [PseudoMetricSpace (𝓕 → ℝ)] [MeasurableSpace (𝓕 → ℝ)]
  [OpensMeasurableSpace (𝓕 → ℝ)]
  [PseudoMetricSpace (𝓖 → ℝ)] [MeasurableSpace (𝓖 → ℝ)]
  [BorelSpace (𝓖 → ℝ)]

/-- A concrete `P`-Donsker realisation restricts to a subclass. -/
theorem RealisesPDonskerClass.restrict
    (P : Measure S) (sampleLaw : ℕ → Measure Ω)
    (ν : ℕ → 𝓕 → Ω → ℝ)
    (limitLaw : Measure Ω') (G : 𝓕 → Ω' → ℝ)
    (hD : RealisesPDonskerClass P 𝓕 sampleLaw ν limitLaw G)
    (h𝓖𝓕 : 𝓖 ⊆ 𝓕)
    (hres : LipschitzWith 1
      (restrictProcessPath
        (fun g : 𝓖 => (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕)))) :
    RealisesPDonskerClass P 𝓖 sampleLaw
      (fun n => restrictIndexedProcess h𝓖𝓕 (ν n))
      limitLaw (restrictIndexedProcess h𝓖𝓕 G) := by
  refine ⟨hD.1.restrict h𝓖𝓕, ?_⟩
  simpa [restrictIndexedProcess, restrictProcessPath, Function.comp_def] using
    hD.2.reindex
      (fun g : 𝓖 => (⟨g.1, h𝓖𝓕 g.2⟩ : 𝓕)) hres

end ClassRestriction

end Chapter03
end InfiniteDimensionalStatistics
