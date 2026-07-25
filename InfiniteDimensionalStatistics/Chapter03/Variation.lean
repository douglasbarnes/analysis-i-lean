/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.EntropyGrowth

/-!
# Chapter 3: Bounded p-variation

The variation functional and translate/dilate classes from Section 3.6.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

/-- A finite strictly increasing real partition. -/
structure IncreasingPartition where
  length : ℕ
  point : Fin (length + 1) → ℝ
  strictMono : StrictMono point

/-- Sum of `p`-powers of increments of `f` along a partition. -/
def partitionVariationPower (f : ℝ → ℝ) (p : ℝ)
    (π : IncreasingPartition) : ℝ :=
  ∑ i : Fin π.length,
    |f (π.point i.succ) - f (π.point i.castSucc)| ^ p

/--
Extended `p`-variation of a real function.

Source: unnumbered definition on pp. 220–221; specification id `p_variation`.
-/
def pVariation (f : ℝ → ℝ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ π : IncreasingPartition,
    ENNReal.ofReal ((partitionVariationPower f p π) ^ (1 / p))

/-- A function has finite `p`-variation. -/
def HasBoundedPVariation (f : ℝ → ℝ) (p : ℝ) : Prop :=
  pVariation f p < ∞

/-- Translation of a function. -/
def translateFunction (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun x ↦ f (x - a)

/-- Dilation and translation with amplitude. -/
def affineTransformFunction (f : ℝ → ℝ)
    (amplitude scale shift : ℝ) : ℝ → ℝ :=
  fun x ↦ amplitude * f (scale * x - shift)

/-- Full translate class of a fixed function. -/
def translateClass (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  Set.range (translateFunction f)

/-- Translate/dilate/amplitude class of a fixed function. -/
def affineTransformClass (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {g | ∃ amplitude scale shift : ℝ,
    g = affineTransformFunction f amplitude scale shift}

end Chapter03
end InfiniteDimensionalStatistics
