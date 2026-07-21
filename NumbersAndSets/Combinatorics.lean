import Mathlib

/-! # Numbers and Sets: finite sets and combinatorics -/

namespace NumbersAndSets

noncomputable def Indicator {α : Type*} (A : Set α) (x : α) : ℕ :=
  by
    classical
    exact if x ∈ A then 1 else 0

theorem indicator_eq_iff {α : Type*} (A B : Set α) :
    Indicator A = Indicator B ↔ A = B := by
  classical
  constructor
  · intro h
    ext x
    have hx := congrFun h x
    simp only [Indicator] at hx
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb] at hx ⊢
  · rintro rfl
    rfl

theorem indicator_inter {α : Type*} (A B : Set α) (x : α) :
    Indicator (A ∩ B) x = Indicator A x * Indicator B x := by
  classical
  simp only [Indicator, Set.mem_inter_iff]
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]

theorem card_union_add_card_inter {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card + (A ∩ B).card = A.card + B.card := Finset.card_union_add_card_inter A B

theorem sum_choose (n : ℕ) : ∑ r ∈ Finset.range (n + 1), n.choose r = 2 ^ n := by
  simpa using Nat.sum_range_choose n

theorem choose_symm (n r : ℕ) (h : r ≤ n) : n.choose r = n.choose (n - r) :=
  (Nat.choose_symm h).symm

theorem pascal (n r : ℕ) (hr : 0 < r) : n.choose (r - 1) + n.choose r = (n + 1).choose r := by
  cases r with
  | zero => simp at hr
  | succ r => simpa [Nat.add_comm] using (Nat.choose_succ_succ n r).symm

theorem weak_induction (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => simpa using hs n ih

theorem strong_induction (P : ℕ → Prop) (h : ∀ n, (∀ k < n, P k) → P n) :
    ∀ n, P n := by
  intro n
  exact Nat.strong_induction_on n (fun n ih => h n ih)

end NumbersAndSets
