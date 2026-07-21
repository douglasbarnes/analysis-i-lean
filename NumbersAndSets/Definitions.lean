import NumbersAndSets.Foundations

/-! Every definition environment in the source has a course-facing Lean name here. -/

namespace NumbersAndSets.Definitions

abbrev Proof (P : Prop) := P
abbrev Statement := Prop
abbrev SetOf (α : Type*) := Set α
abbrev SetEquality {α : Type*} (A B : Set α) := ∀ x, x ∈ A ↔ x ∈ B
abbrev Subset {α : Type*} (A B : Set α) := A ⊆ B
abbrev Intersection {α : Type*} (A B : Set α) := A ∩ B
abbrev Union {α : Type*} (A B : Set α) := A ∪ B
abbrev Difference {α : Type*} (A B : Set α) := A \ B
abbrev SymmetricDifference {α : Type*} (A B : Set α) := (A \ B) ∪ (B \ A)
abbrev PowerSet {α : Type*} (A : Set α) := Set.powerset A
abbrev OrderedPair (α β : Type*) := α × β
abbrev CartesianProduct (α β : Type*) := α × β
abbrev Function (α β : Type*) := α → β
abbrev Injective {α β : Type*} (f : α → β) := _root_.Function.Injective f
abbrev Surjective {α β : Type*} (f : α → β) := _root_.Function.Surjective f
abbrev Bijective {α β : Type*} (f : α → β) := _root_.Function.Bijective f
abbrev Permutation (α : Type*) := Equiv.Perm α
abbrev Composition {α β γ : Type*} (g : β → γ) (f : α → β) := g ∘ f
abbrev Image {α β : Type*} (f : α → β) (A : Set α) := f '' A
abbrev Preimage {α β : Type*} (f : α → β) (B : Set β) := f ⁻¹' B
abbrev Identity (α : Type*) := (id : α → α)
abbrev LeftInverse {α β : Type*} (g : β → α) (f : α → β) := _root_.Function.LeftInverse g f
abbrev RightInverse {α β : Type*} (g : β → α) (f : α → β) := _root_.Function.RightInverse g f
abbrev Inverse (α β : Type*) := α ≃ β
abbrev Relation (α : Type*) := α → α → Prop
abbrev Reflexive {α : Type*} (r : Relation α) := IsRefl α r
abbrev Symmetric {α : Type*} (r : Relation α) := _root_.Symmetric r
abbrev Transitive {α : Type*} (r : Relation α) := _root_.Transitive r
abbrev EquivalenceRelation {α : Type*} (r : Relation α) := Equivalence r
abbrev EquivalenceClass {α : Type*} (r : Relation α) (x : α) := {y | r y x}
abbrev Partition (α ι : Type*) :=
  {p : ι → Set α // (∀ x, ∃! i, x ∈ p i)}
abbrev QuotientMap {α : Type*} (s : Setoid α) := Quotient.mk s
abbrev IntegerFactor (a b : ℤ) := a ∣ b
abbrev CommonFactor (a b c : ℤ) := c ∣ a ∧ c ∣ b
abbrev GreatestCommonDivisor (a b : ℕ) := Nat.gcd a b
abbrev Prime (p : ℕ) := Nat.Prime p
abbrev Coprime (a b : ℕ) := Nat.Coprime a b
noncomputable def Indicator {α : Type*} (A : Set α) (x : α) : ℕ := by
  classical
  exact if x ∈ A then 1 else 0
abbrev Combination (n r : ℕ) := n.choose r
abbrev PartialOrderRelation {α : Type*} (r : Relation α) :=
  IsRefl α r ∧ Std.Antisymm r ∧ _root_.Transitive r
abbrev TotalOrderRelation {α : Type*} (r : Relation α) := PartialOrderRelation r ∧ ∀ x y, r x y ∨ r y x
abbrev WellOrderRelation {α : Type*} (r : Relation α) := IsWellOrder α r
abbrev CongruentModulo (m a b : ℕ) := Nat.ModEq m a b
abbrev ModularUnit (m : ℕ) (u : ZMod m) := IsUnit u
abbrev EulerTotient (m : ℕ) := Nat.totient m
abbrev QuadraticResidue (p : ℕ) (a : ZMod p) := IsSquare a
abbrev NaturalNumbers := ℕ
abbrev Integers := ℤ
abbrev Rationals := ℚ
class TotallyOrderedField (F : Type*) extends Field F, LinearOrder F, IsStrictOrderedRing F
abbrev IsLeastUpperBound {α : Type*} [LE α] (S : Set α) (x : α) := IsLUB S x
abbrev IsGreatestLowerBound {α : Type*} [LE α] (S : Set α) (x : α) := IsGLB S x
abbrev RealNumbers := ℝ
abbrev ClosedInterval (a b : ℝ) := Set.Icc a b
abbrev OpenInterval (a b : ℝ) := Set.Ioo a b
abbrev DedekindCut := {L : Set ℚ // L.Nonempty ∧ L ≠ Set.univ ∧ ∀ a ∈ L, ∀ b < a, b ∈ L}
abbrev Sequence := ℕ → ℝ
abbrev Limit (a : Sequence) (l : ℝ) := Filter.Tendsto a Filter.atTop (nhds l)
abbrev Convergent (a : Sequence) := ∃ l, Limit a l
abbrev Subsequence (a : Sequence) (g : ℕ → ℕ) := a ∘ g
abbrev PartialSums (a : Sequence) (n : ℕ) := ∑ i ∈ Finset.Icc 1 n, a i
abbrev DecimalDigits := ℕ → Fin 10
abbrev IrrationalReal (x : ℝ) := Irrational x
abbrev PeriodicSequence {α : Type*} (f : ℕ → α) := ∃ p > 0, _root_.Function.Periodic f p
noncomputable def EulerNumber := Real.exp 1
abbrev AlgebraicNumber (x : ℂ) := IsIntegral ℚ x
abbrev TranscendentalNumber (x : ℂ) := Transcendental ℚ x
abbrev FiniteSet (α : Type*) := Finite α
abbrev CountableSet (α : Type*) := Countable α

end NumbersAndSets.Definitions
