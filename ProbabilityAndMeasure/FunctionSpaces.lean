import ProbabilityAndMeasure.Integration

/-!
# Probability and Measure: inequalities and `Lᵖ` spaces

The course's functional-analytic language is connected to Mathlib's `Lp` construction.
The deep inequalities and completeness results are checked in `LibraryCoverage.lean`.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set Filter MeasureTheory

namespace ProbabilityAndMeasure

/-- Mathlib's quotient space of almost-everywhere equal `p`-integrable functions. -/
abbrev LpSpace (α E : Type*) [MeasurableSpace α] [NormedAddCommGroup E]
    (p : ℝ≥0∞) (μ : Measure α) :=
  MeasureTheory.Lp E p μ

/-- Membership in `Lᵖ`, before passage to almost-everywhere equivalence classes. -/
abbrev IsLp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  MemLp f p μ

/-- Convexity of a real function on an interval. -/
def ConvexOnInterval (I : Set ℝ) (c : ℝ → ℝ) : Prop :=
  ConvexOn ℝ I c

/-- Conjugate finite exponents. -/
def AreConjugateExponents (p q : ℝ) : Prop :=
  1 < p ∧ 1 < q ∧ 1 / p + 1 / q = 1

/-- A family is uniformly bounded in `Lᵖ`. -/
def LpBounded {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : ℝ≥0∞) (X : ι → Ω → ℝ) : Prop :=
  ∃ C : ℝ≥0∞, ∀ i, eLpNorm (X i) p P ≤ C

/-- Banach-space completeness is represented by Mathlib's `CompleteSpace` class. -/
abbrev IsBanachSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Nonempty (CompleteSpace E)

/-- A Hilbert space is an inner-product space carrying a compatible complete metric. -/
abbrev IsHilbertSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  Nonempty (CompleteSpace E)

/-- Orthogonality in a real inner-product space. -/
def Orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : Prop :=
  inner ℝ x y = 0

/-- Cauchy--Schwarz for finite real sums. -/
theorem cauchySchwarzFinite {ι : Type*} (s : Finset ι) (X Y : ι → ℝ) :
    (∑ i ∈ s, X i * Y i) ^ 2 ≤
      (∑ i ∈ s, X i ^ 2) * ∑ i ∈ s, Y i ^ 2 := by
  exact Finset.sum_mul_sq_le_sq_mul_sq s X Y

/-- The triangle inequality in any normed additive commutative group. -/
theorem minkowski_abstract {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

end ProbabilityAndMeasure
