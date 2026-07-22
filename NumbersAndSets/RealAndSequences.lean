import Mathlib

/-! # Numbers and Sets: real numbers and sequences -/

namespace NumbersAndSets

abbrev Sequence := ℕ → ℝ
abbrev TendsTo (a : Sequence) (l : ℝ) := Filter.Tendsto a Filter.atTop (nhds l)
abbrev Converges (a : Sequence) := ∃ l, TendsTo a l
abbrev Subsequence (a : Sequence) (g : ℕ → ℕ) := a ∘ g

theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := _root_.irrational_sqrt_two

theorem archimedean (r : ℝ) : ∃ n : ℕ, r < n := by
  exact exists_nat_gt r

theorem rationals_dense (r s : ℝ) (h : r < s) :
    ∃ q : ℚ, r < q ∧ (q : ℝ) < s := by
  exact exists_rat_btwn h

theorem exists_sq_eq_two : ∃ x : ℝ, x ^ 2 = 2 := by
  refine ⟨Real.sqrt 2, ?_⟩
  norm_num

theorem monotone_bounded_converges (a : Sequence) (hmono : Monotone a)
    (hbounded : BddAbove (Set.range a)) : Converges a := by
  exact ⟨sSup (Set.range a), tendsto_atTop_ciSup hmono hbounded⟩

theorem limit_unique {a : Sequence} {x y : ℝ} (hx : TendsTo a x) (hy : TendsTo a y) : x = y :=
  tendsto_nhds_unique hx hy

theorem eventually_equal_same_limit {a b : Sequence} {x : ℝ} (h : TendsTo a x)
    (hab : a =ᶠ[Filter.atTop] b) : TendsTo b x := Filter.Tendsto.congr' hab h

theorem constant_limit (x : ℝ) : TendsTo (fun _ : ℕ => x) x := tendsto_const_nhds

theorem add_limits {a b : Sequence} {x y : ℝ} (ha : TendsTo a x) (hb : TendsTo b y) :
    TendsTo (fun n => a n + b n) (x + y) := ha.add hb

theorem mul_limits {a b : Sequence} {x y : ℝ} (ha : TendsTo a x) (hb : TendsTo b y) :
    TendsTo (fun n => a n * b n) (x * y) := ha.mul hb

theorem inv_limit {a : Sequence} {x : ℝ} (ha : TendsTo a x) (hx : x ≠ 0) :
    TendsTo (fun n => (a n)⁻¹) x⁻¹ := ha.inv₀ hx

theorem squeeze {a b c : Sequence} {x : ℝ} (ha : TendsTo a x) (hb : TendsTo b x)
    (h : ∀ n, a n ≤ c n ∧ c n ≤ b n) : TendsTo c x := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb
  · exact fun n => (h n).1
  · exact fun n => (h n).2

end NumbersAndSets
