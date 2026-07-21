import Mathlib

namespace AnalysisI

/-- Course-level definition: a real sequence is bounded by one nonnegative radius. -/
def SequenceBounded (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |a n| ≤ C

/-- Course-level definition: a real sequence is bounded from some index onwards. -/
def SequenceEventuallyBounded (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ n ≥ N, |a n| ≤ C

/-- Source theorem 4 (lines 175–177): every eventually bounded real sequence is bounded. -/
theorem eventuallyBounded_bounded {a : ℕ → ℝ}
    (h : SequenceEventuallyBounded a) : SequenceBounded a := by
  rcases h with ⟨C, N, hC, htail⟩
  let B : ℝ := ∑ i ∈ Finset.range N, |a i|
  refine ⟨max C B, hC.trans (le_max_left _ _), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (htail n hn).trans (le_max_left _ _)
  · have hn' : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hB : |a n| ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun i _ => abs_nonneg (a i)) hn'
    exact hB.trans (le_max_right _ _)

end AnalysisI
