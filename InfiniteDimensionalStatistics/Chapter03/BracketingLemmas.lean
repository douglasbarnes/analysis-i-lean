/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.MetricEntropyLemmas

/-!
# Chapter 3: Elementary bracketing lemmas

Diagonal brackets and finite bracketing-cover facts used before the bracketing
entropy inequalities.
-/

noncomputable section

open Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

variable {α : Type*}

/-- The degenerate bracket with identical lower and upper functions. -/
def diagonalBracket (f : α → ℝ) : FunctionBracket (α := α) where
  lower := f
  upper := f

@[simp] theorem diagonalBracket_contains (f : α → ℝ) :
    (diagonalBracket f).Contains f := by
  intro x
  exact ⟨le_rfl, le_rfl⟩

@[simp] theorem diagonalBracket_width
    (ρ : (α → ℝ) → ℝ) (f : α → ℝ) :
    (diagonalBracket f).width ρ = ρ 0 := by
  congr 1
  funext x
  simp [FunctionBracket.width, diagonalBracket]

/-- A bracketing cover remains valid when the allowed width is enlarged. -/
theorem IsBracketingCover.mono_radius
    {ρ : (α → ℝ) → ℝ} {𝓕 : Set (α → ℝ)}
    {B : Set (FunctionBracket (α := α))} {ε δ : ℝ}
    (h : IsBracketingCover ρ 𝓕 B ε) (hεδ : ε ≤ δ) :
    IsBracketingCover ρ 𝓕 B δ := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro b hb
  exact (h.2.1 b hb).trans hεδ

/-- The diagonal bracket gives a singleton bracketing cover at nonnegative radius. -/
theorem singleton_isBracketingCover
    (ρ : (α → ℝ) → ℝ) (hρ0 : ρ 0 = 0)
    (f : α → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsBracketingCover ρ {f} {diagonalBracket f} ε := by
  refine ⟨Set.finite_singleton _, ?_, ?_⟩
  · intro b hb
    have : b = diagonalBracket f := by simpa using hb
    subst this
    simp [hρ0, hε]
  · intro g hg
    have hgf : g = f := by simpa using hg
    subst hgf
    exact ⟨diagonalBracket f, Set.mem_singleton _, diagonalBracket_contains f⟩

/-- A singleton class has bracketing number at most one. -/
theorem bracketingNumber_singleton_le_one
    (ρ : (α → ℝ) → ℝ) (hρ0 : ρ 0 = 0)
    (f : α → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    bracketingNumber ρ {f} ε ≤ 1 := by
  unfold bracketingNumber
  apply sInf_le
  exact ⟨{diagonalBracket f},
    singleton_isBracketingCover ρ hρ0 f hε, by simp⟩

/-- Every finite bracketing-cover witness bounds the bracketing number. -/
theorem bracketingNumber_le_ncard
    (ρ : (α → ℝ) → ℝ) (𝓕 : Set (α → ℝ))
    (B : Set (FunctionBracket (α := α))) {ε : ℝ}
    (hB : IsBracketingCover ρ 𝓕 B ε) :
    bracketingNumber ρ 𝓕 ε ≤ (B.ncard : WithTop ℕ) := by
  unfold bracketingNumber
  apply sInf_le
  exact ⟨B, hB, rfl⟩

end Chapter03
end InfiniteDimensionalStatistics
