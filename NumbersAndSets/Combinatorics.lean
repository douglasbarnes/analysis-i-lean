import Mathlib

/-! # Numbers and Sets: finite sets and combinatorics -/

namespace NumbersAndSets

abbrev Indicator {α : Type*} (A : Set α) (x : α) : ℕ := if x ∈ A then 1 else 0

theorem indicator_eq_iff {α : Type*} (A B : Set α) :
    Indicator A = Indicator B ↔ A = B := by
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
  simp only [Indicator, Set.mem_inter_iff]
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]

theorem card_union_add_card_inter {α : Type*} [DecidableEq α] (A B : Finset α) :
    #(A ∪ B) + #(A ∩ B) = #A + #B := Finset.card_union_add_card_inter A B

theorem pigeonhole {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    {m : ℕ} (h : m * Fintype.card β < Fintype.card α) :
    ∃ y : β, m < Fintype.card {x : α // f x = y} := by
  by_contra hn
  push_neg at hn
  have := Fintype.card_le_mul_card_fiberwise hn
  omega

theorem sum_choose (n : ℕ) : ∑ r ∈ Finset.range (n + 1), n.choose r = 2 ^ n := by
  simpa using Nat.sum_range_choose n

theorem choose_symm (n r : ℕ) : n.choose r = n.choose (n - r) := Nat.choose_symm r n

theorem pascal (n r : ℕ) : n.choose (r - 1) + n.choose r = (n + 1).choose r := by
  cases r with
  | zero => simp
  | succ r => simpa [Nat.add_comm] using (Nat.choose_succ_succ n r).symm

theorem choose_mul_choose (n k r : ℕ) :
    n.choose k * k.choose r = n.choose r * (n - r).choose (k - r) := by
  simpa [Nat.mul_comm] using Nat.choose_mul_choose n k r

theorem choose_eq_factorial_div (n r : ℕ) :
    n.choose r = n ! / ((n - r)! * r !) := by
  rw [Nat.choose_eq_factorial_div_factorial]
  rw [Nat.mul_comm]

theorem weak_induction (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => simpa using hs n ih

theorem strong_induction (P : ℕ → Prop) (h : ∀ n, (∀ k < n, P k) → P n) :
    ∀ n, P n := Nat.strong_induction_on (p := P) (fun n ih => h n ih)

end NumbersAndSets
