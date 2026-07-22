import Mathlib

/-! # Numbers and Sets: finite and countable sets -/

namespace NumbersAndSets

abbrev IsFiniteSet (α : Type*) := Finite α
abbrev IsCountableSet (α : Type*) := Countable α

theorem injective_finite_self_is_surjective {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Injective f) : Function.Surjective f := by
  exact Finite.injective_iff_surjective.mp hf

theorem finite_card_unique {α : Type*} [Fintype α] {m n : ℕ}
    (f : α ≃ Fin m) (g : α ≃ Fin n) : m = n := by
  simpa using Fintype.card_congr (f.symm.trans g)

theorem countable_iff_injective_nat (α : Type*) :
    Countable α ↔ Nonempty (α ↪ ℕ) := by
  exact countable_iff_nonempty_embedding

theorem integers_countable : Countable ℤ := inferInstance
theorem nat_product_countable : Countable (ℕ × ℕ) := inferInstance
theorem integer_power_countable (k : ℕ) : Countable (Fin k → ℤ) := inferInstance
theorem rationals_countable : Countable ℚ := inferInstance

theorem subtype_of_countable {α : Type*} [Countable α] (S : Set α) : Countable S := inferInstance

theorem countable_union {ι α : Type*} [Countable ι] {s : ι → Set α}
    (hs : ∀ i, (s i).Countable) : (⋃ i, s i).Countable := Set.countable_iUnion hs

theorem reals_uncountable : ¬ Countable ℝ := by
  intro h
  letI : Countable ℝ := h
  exact Cardinal.not_countable_real Set.countable_univ

theorem cantor_no_surjection {α : Type*} (f : α → Set α) : ¬ Function.Surjective f := by
  intro hf
  let D : Set α := {x | x ∉ f x}
  obtain ⟨d, hd⟩ := hf D
  have hiff : d ∈ D ↔ d ∉ D := by
    change (d ∉ f d) ↔ d ∉ D
    rw [hd]
  tauto

theorem cantor_schroeder_bernstein {α β : Type*} (f : α ↪ β) (g : β ↪ α) :
    Nonempty (α ≃ β) := Function.Embedding.antisymm f g

end NumbersAndSets
