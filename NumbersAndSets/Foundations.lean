import Mathlib

/-!
# Numbers and Sets: logic, sets, functions and relations

Declaration-level formalisation of the first two chapters of Dexter Chua's
Part IA *Numbers and Sets* notes.  Definitions already supplied by Lean or
Mathlib are recorded as abbreviations; named results are restated as proved
wrappers so downstream files need not depend on library theorem names.
-/

namespace NumbersAndSets

abbrev Statement := Prop
abbrev Proof (P : Statement) := P

theorem set_eq_iff_mutual_subset {α : Type*} (A B : Set α) :
    A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    subst h
    exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  · rintro ⟨hAB, hBA⟩
    exact Set.Subset.antisymm hAB hBA

theorem inter_assoc {α : Type*} (A B C : Set α) :
    (A ∩ B) ∩ C = A ∩ (B ∩ C) := by ext; simp [and_assoc]

theorem union_assoc {α : Type*} (A B C : Set α) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) := by ext; simp [or_assoc]

theorem inter_union_distrib {α : Type*} (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by ext; aesop

abbrev CartesianProduct (α β : Type*) := α × β
abbrev IsInjective {α β : Type*} (f : α → β) := Function.Injective f
abbrev IsSurjective {α β : Type*} (f : α → β) := Function.Surjective f
abbrev IsBijective {α β : Type*} (f : α → β) := Function.Bijective f
abbrev Permutation (α : Type*) := Equiv.Perm α
abbrev Image {α β : Type*} (f : α → β) (A : Set α) := f '' A
abbrev Preimage {α β : Type*} (f : α → β) (B : Set β) := f ⁻¹' B
abbrev LeftInverse {α β : Type*} (g : β → α) (f : α → β) := Function.LeftInverse g f
abbrev RightInverse {α β : Type*} (g : β → α) (f : α → β) := Function.RightInverse g f

theorem leftInverse_implies_injective {α β : Type*} {f : α → β} {g : β → α}
    (h : LeftInverse g f) : IsInjective f := by
  intro x y hxy
  simpa [h x, h y] using congrArg g hxy

theorem injective_iff_has_leftInverse {α β : Type*} [Nonempty α] (f : α → β) :
    IsInjective f ↔ ∃ g : β → α, LeftInverse g f := by
  constructor
  · intro hf
    classical
    exact ⟨Function.invFun f, Function.leftInverse_invFun hf⟩
  · rintro ⟨g, hg⟩
    exact leftInverse_implies_injective hg

theorem rightInverse_implies_surjective {α β : Type*} {f : α → β} {g : β → α}
    (h : RightInverse g f) : IsSurjective f := by
  intro y
  exact ⟨g y, h y⟩

theorem surjective_iff_has_rightInverse {α β : Type*} [Nonempty α] (f : α → β) :
    IsSurjective f ↔ ∃ g : β → α, RightInverse g f := by
  constructor
  · intro hf
    classical
    exact ⟨Function.invFun f, Function.rightInverse_invFun hf⟩
  · rintro ⟨g, hg⟩
    exact rightInverse_implies_surjective hg

theorem inverse_unique {α β : Type*} {f : α → β} {g h : β → α}
    (gl : LeftInverse g f) (gr : RightInverse g f)
    (hl : LeftInverse h f) (hr : RightInverse h f) : g = h := by
  funext y
  rw [← hr y, gl]

abbrev Relation (α : Type*) := α → α → Prop
abbrev Reflexive {α : Type*} (r : Relation α) := IsRefl α r
abbrev Symmetric {α : Type*} (r : Relation α) := Symmetric r
abbrev Transitive {α : Type*} (r : Relation α) := Transitive r
abbrev EquivalenceRelation {α : Type*} (r : Relation α) := Equivalence r
abbrev EquivalenceClass {α : Type*} (r : Relation α) (x : α) := {y | r y x}

theorem equivalence_classes_cover {α : Type*} {r : Relation α} (h : Equivalence r) (x : α) :
    x ∈ EquivalenceClass r x := h.1 x

theorem equivalence_classes_eq_or_disjoint {α : Type*} {r : Relation α}
    (h : Equivalence r) (x y : α) :
    EquivalenceClass r x = EquivalenceClass r y ∨
      Disjoint (EquivalenceClass r x) (EquivalenceClass r y) := by
  classical
  by_cases hxy : r x y
  · left
    ext z
    constructor
    · intro hzx
      exact h.2.2 hzx hxy
    · intro hzy
      exact h.2.2 hzy (h.2.1 hxy)
  · right
    rw [Set.disjoint_left]
    intro z hzx hzy
    exact hxy (h.2.2 (h.2.1 hzx) hzy)

abbrev PartialOrderRelation {α : Type*} (r : Relation α) :=
  IsRefl α r ∧ Antisymm r ∧ Transitive r

abbrev TotalOrderRelation {α : Type*} (r : Relation α) :=
  PartialOrderRelation r ∧ ∀ x y, r x y ∨ r y x

abbrev WellOrderedRelation {α : Type*} (r : Relation α) := IsWellOrder α r

theorem nat_well_ordering (S : Set ℕ) (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  let P : ℕ → Prop := fun n => n ∈ S
  have hex : ∃ n, P n := hne
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro n hn
  exact Nat.find_min' hex hn

end NumbersAndSets
