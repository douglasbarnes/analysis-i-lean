/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.Symmetrisation

/-!
# Chapter 3: Metric entropy and bracketing

Reusable definitions for covering, packing, bracketing and entropy integrals.
They support the chaining and empirical-process bounds in Sections 3.2–3.7.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section CoveringAndPacking

variable {α : Type*}

/-- A finite `ε`-net for `A` with respect to a nonnegative distance function. -/
def IsEpsilonNet (d : α → α → ℝ) (A C : Set α) (ε : ℝ) : Prop :=
  C.Finite ∧ C ⊆ A ∧ ∀ x ∈ A, ∃ y ∈ C, d x y ≤ ε

/-- A finite `ε`-separated subset of `A`. -/
def IsEpsilonSeparated (d : α → α → ℝ) (A C : Set α) (ε : ℝ) : Prop :=
  C.Finite ∧ C ⊆ A ∧ C.Pairwise fun x y ↦ ε < d x y

/-- The extended covering number. -/
def coveringNumber (d : α → α → ℝ) (A : Set α) (ε : ℝ) : WithTop ℕ :=
  sInf {k : WithTop ℕ |
    ∃ C : Set α, IsEpsilonNet d A C ε ∧ k = (C.ncard : WithTop ℕ)}

/-- The extended packing number. -/
def packingNumber (d : α → α → ℝ) (A : Set α) (ε : ℝ) : WithTop ℕ :=
  sSup {k : WithTop ℕ |
    ∃ C : Set α, IsEpsilonSeparated d A C ε ∧ k = (C.ncard : WithTop ℕ)}

/-- Extended diameter of a set. -/
def extendedDiameter (d : α → α → ℝ) (A : Set α) : ℝ≥0∞ :=
  ⨆ x : A, ⨆ y : A, ENNReal.ofReal (d x.1 y.1)

end CoveringAndPacking

section Bracketing

variable {α : Type*}

/-- A lower and upper function forming a bracket. -/
structure FunctionBracket where
  lower : α → ℝ
  upper : α → ℝ

/-- Pointwise membership of a function in a bracket. -/
def FunctionBracket.Contains (b : FunctionBracket (α := α)) (f : α → ℝ) : Prop :=
  ∀ x, b.lower x ≤ f x ∧ f x ≤ b.upper x

/-- Width of a bracket with respect to a supplied seminorm or pseudonorm. -/
def FunctionBracket.width (ρ : (α → ℝ) → ℝ)
    (b : FunctionBracket (α := α)) : ℝ :=
  ρ (b.upper - b.lower)

/-- A finite family of brackets covering a function class. -/
def IsBracketingCover (ρ : (α → ℝ) → ℝ) (𝓕 : Set (α → ℝ))
    (B : Set (FunctionBracket (α := α))) (ε : ℝ) : Prop :=
  B.Finite ∧
    (∀ b ∈ B, b.width ρ ≤ ε) ∧
    ∀ f ∈ 𝓕, ∃ b ∈ B, b.Contains f

/-- Extended bracketing number. -/
def bracketingNumber (ρ : (α → ℝ) → ℝ) (𝓕 : Set (α → ℝ))
    (ε : ℝ) : WithTop ℕ :=
  sInf {k : WithTop ℕ |
    ∃ B : Set (FunctionBracket (α := α)),
      IsBracketingCover ρ 𝓕 B ε ∧ k = (B.ncard : WithTop ℕ)}

end Bracketing

section EntropyIntegrals

/-- A truncated entropy integral `∫₀^δ sqrt(max(H(ε),0)) dε`. -/
def entropyIntegral (H : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∫ ε, Set.indicator (Set.Ioc (0 : ℝ) δ)
    (fun r ↦ Real.sqrt (max (H r) 0)) ε

/-- A weighted entropy integral used in moment and maximal inequalities. -/
def weightedEntropyIntegral (H w : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∫ ε, Set.indicator (Set.Ioc (0 : ℝ) δ)
    (fun r ↦ w r * Real.sqrt (max (H r) 0)) ε

end EntropyIntegrals

end Chapter03
end InfiniteDimensionalStatistics
