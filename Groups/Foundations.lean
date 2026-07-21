import Mathlib

/-!
# Part IA Groups: foundations

Lean wrappers for the definitions and results in lines 80--1177 of the source notes.
The numeric suffixes agree with `Groups/Inventory.md`.
-/

namespace Cambridge.Groups

universe u v w

noncomputable section

/-- 001. A binary operation on `α`. -/
abbrev BinaryOperation (α : Type u) := α → α → α

/-- 002. The bundled data used by Lean for the notes' group axioms. -/
abbrev GroupStructure (α : Type u) := Group α

/-- 003. The order (cardinality) of a finite group. -/
def groupOrder (G : Type u) [Group G] [Fintype G] : ℕ := Fintype.card G

/-- 004. The notes' predicate that a group is abelian. -/
def IsAbelian (G : Type u) [Group G] : Prop := ∀ a b : G, a * b = b * a

/-- 005. Identity and inverses in a group are unique. -/
theorem identity_inverse_unique {G : Type u} [Group G] (e : G)
    (he : ∀ a : G, a * e = a ∧ e * a = a) (a b : G)
    (hb : a * b = e ∧ b * a = e) : e = 1 ∧ b = a⁻¹ := by
  have ee : e = 1 := by simpa using (he 1).1
  subst e
  constructor
  · rfl
  · calc
      b = b * 1 := (mul_one b).symm
      _ = b * (a * a⁻¹) := by simp
      _ = (b * a) * a⁻¹ := by simp [mul_assoc]
      _ = a⁻¹ := by simp [hb.2]

/-- 006. Standard inverse identities. -/
theorem inverse_identities {G : Type u} [Group G] (a b : G) :
    (a⁻¹)⁻¹ = a ∧ (a * b)⁻¹ = b⁻¹ * a⁻¹ := by simp

/-- 007. Subgroups are Lean's bundled `Subgroup`. -/
abbrev SubgroupOf (G : Type u) [Group G] := Subgroup G

/-- 008. First subgroup criterion. -/
theorem subgroup_criteria_I {G : Type u} [Group G] (H : Set G)
    (hone : (1 : G) ∈ H) (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) : ∃ K : Subgroup G, (K : Set G) = H := by
  refine ⟨{ carrier := H, one_mem' := hone, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    exact hmul a ha b hb
  · intro a ha
    exact hinv a ha

/-- 009. Second subgroup criterion. -/
theorem subgroup_criteria_II {G : Type u} [Group G] (H : Set G)
    (hne : H.Nonempty) (hdiv : ∀ a ∈ H, ∀ b ∈ H, a * b⁻¹ ∈ H) :
    ∃ K : Subgroup G, (K : Set G) = H := by
  obtain ⟨x, hx⟩ := hne
  have hone : (1 : G) ∈ H := by simpa using hdiv x hx x hx
  have hinv : ∀ a ∈ H, a⁻¹ ∈ H := by
    intro a ha
    simpa using hdiv 1 hone a ha
  exact subgroup_criteria_I H hone (by
    intro a ha b hb
    simpa using hdiv a ha b⁻¹ (hinv b hb)) hinv

/-- 010. Every additive subgroup of the integers is cyclic. -/
theorem integer_subgroup_cyclic (H : AddSubgroup ℤ) :
    ∃ a : ℤ, H = AddSubgroup.closure {a} := by
  exact Int.subgroup_cyclic H

/-- 011. A function from `X` to `Y`. -/
abbrev FunctionOf (X : Type u) (Y : Type v) := X → Y

/-- 012. Function composition. -/
def compose {X : Type u} {Y : Type v} {Z : Type w} (g : Y → Z) (f : X → Y) : X → Z := g ∘ f

/-- 013. Injectivity. -/
abbrev IsInjective {X : Type u} {Y : Type v} (f : X → Y) := Function.Injective f

/-- 014. Surjectivity. -/
abbrev IsSurjective {X : Type u} {Y : Type v} (f : X → Y) := Function.Surjective f

/-- 015. Bijectivity. -/
abbrev IsBijective {X : Type u} {Y : Type v} (f : X → Y) := Function.Bijective f

/-- 016. A composite of bijections is bijective. -/
theorem bijective_comp {X : Type u} {Y : Type v} {Z : Type w} {f : X → Y} {g : Y → Z}
    (hg : Function.Bijective g) (hf : Function.Bijective f) : Function.Bijective (g ∘ f) :=
  hg.comp hf

/-- 017. Group homomorphisms. -/
abbrev GroupHomOf (G : Type u) (H : Type v) [Group G] [Group H] := G →* H

/-- 018. Group isomorphisms. -/
abbrev GroupIso (G : Type u) (H : Type v) [Group G] [Group H] := G ≃* H

/-- 019. Homomorphisms preserve identity, inverses and integer powers. -/
theorem hom_preserves_operations {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (a : G) (n : ℤ) :
    f 1 = 1 ∧ f a⁻¹ = (f a)⁻¹ ∧ f (a ^ n) = f a ^ n := by simp

/-- 020. The image of a group homomorphism. -/
abbrev homImage {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) := f.range

/-- 021. The kernel of a group homomorphism. -/
abbrev homKernel {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) := f.ker

/-- 022. Image and kernel are subgroups (by their types). -/
theorem image_kernel_subgroups {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    (f.range : Set H).Nonempty ∧ (f.ker : Set G).Nonempty := by
  exact ⟨⟨1, ⟨1, f.map_one⟩⟩, ⟨1, by simp⟩⟩

/-- 023. Kernels are closed under conjugation. -/
theorem kernel_conjugation {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (a k : G) (hk : k ∈ f.ker) : a * k * a⁻¹ ∈ f.ker := by
  rw [f.mem_ker] at hk ⊢
  simp [hk]

/-- 024. Surjectivity and injectivity via range and kernel. -/
theorem surjective_injective_criteria {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) :
    (Function.Surjective f ↔ f.range = ⊤) ∧ (Function.Injective f ↔ f.ker = ⊥) := by
  constructor
  · exact ⟨fun h => f.range_eq_top.mpr h, fun h => f.range_eq_top.mp h⟩
  · constructor
    · intro hf
      ext x
      simp only [f.mem_ker, Subgroup.mem_bot]
      exact ⟨fun hx => hf (by simpa using hx), fun hx => by simpa [hx]⟩
    · intro hk x y hxy
      have hm : x * y⁻¹ ∈ f.ker := by
        rw [f.mem_ker]
        simp [hxy]
      rw [hk] at hm
      have hdiv : x * y⁻¹ = 1 := Subgroup.mem_bot.mp hm
      exact div_eq_one.mp (by simpa [div_eq_mul_inv] using hdiv)

/-- 025. A group is cyclic when it has a generator. -/
abbrev IsCyclicGroup (G : Type u) [Group G] := IsCyclic G

/-- 026. The cyclic subgroup generated by an element. -/
def cyclicSubgroup {G : Type u} [Group G] (a : G) : Subgroup G := Subgroup.zpowers a

/-- 027. The order of an element. -/
abbrev elementOrder {G : Type u} [Group G] (a : G) := orderOf a

/-- 028. The order of an element is the cardinality of its cyclic subgroup. -/
theorem order_eq_card_zpowers {G : Type u} [Group G] (a : G) :
    Nat.card (Subgroup.zpowers a) = orderOf a := by
  exact Nat.card_zpowers a

/-- 029. Cyclic groups are abelian. -/
theorem cyclic_isAbelian (G : Type u) [Group G] [IsCyclic G] : IsAbelian G := by
  letI : IsMulCommutative G := IsCyclic.isMulCommutative
  intro a b
  exact mul_comm' a b

/-- 030. A finite exponent for a group. -/
def HasExponent (G : Type u) [Group G] (n : ℕ) : Prop := ∀ a : G, a ^ n = 1

/-- 031. Dihedral groups are represented in mathlib by `DihedralGroup n`. -/
abbrev Dihedral (n : ℕ) := DihedralGroup n

/-- 032. Direct products use the product group instance. -/
abbrev DirectProduct (G : Type u) (H : Type v) [Group G] [Group H] := G × H

/-- 033. Product of finite cyclic groups of coprime orders is cyclic. -/
theorem cyclic_product_of_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    IsCyclic (Multiplicative (ZMod m) × Multiplicative (ZMod n)) := by
  apply Group.isCyclic_prod_iff.mpr
  refine ⟨inferInstance, inferInstance, ?_⟩
  change (Nat.card (ZMod m)).Coprime (Nat.card (ZMod n))
  simpa only [Nat.card_zmod] using h

/-- 034. Internal direct-product criterion, stated as uniqueness of commuting factorisation. -/
theorem internal_direct_product_unique {G : Type u} [Group G] (H K : Subgroup G)
    (hinter : H ⊓ K = ⊥) (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {h₁ h₂ : H} {k₁ k₂ : K} (heq : (h₁ : G) * k₁ = h₂ * k₂) : h₁ = h₂ ∧ k₁ = k₂ := by
  have hm : ((h₂ : G)⁻¹ * h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by
    calc
      (h₂ : G)⁻¹ * h₁ = (h₂ : G)⁻¹ * (h₁ * (k₁ * (k₁ : G)⁻¹)) := by simp
      _ = (h₂ : G)⁻¹ * ((h₁ : G) * k₁) * (k₁ : G)⁻¹ := by simp [mul_assoc]
      _ = (k₂ : G) * (k₁ : G)⁻¹ := by rw [heq]; simp [mul_assoc]
  have hi : ((h₂ : G)⁻¹ * h₁ : G) ∈ H ⊓ K := by
    constructor
    · exact H.mul_mem (H.inv_mem h₂.property) h₁.property
    · rw [hm]
      exact K.mul_mem k₂.property (K.inv_mem k₁.property)
  have hone : ((h₂ : G)⁻¹ * h₁ : G) = 1 := by
    rw [hinter] at hi
    exact hi
  have hh : h₁ = h₂ := Subtype.ext (inv_mul_eq_one.mp hone).symm
  subst h₂
  exact ⟨rfl, Subtype.ext (mul_left_cancel heq)⟩

/-- 035. A permutation is an equivalence from a type to itself. -/
abbrev Permutation (X : Type u) := Equiv.Perm X

/-- 036. Permutations carry a group structure under composition. -/
def permutationGroup (X : Type u) : Group (Permutation X) := inferInstance

/-- 037. The symmetric group on `n` letters. -/
abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- 038. Two-row notation records a permutation by its values. -/
def permutationValues {n : ℕ} (σ : SymmetricGroup n) : Fin n → Fin n := σ

/-- 039. Cycle notation is represented by `Equiv.Perm.cycle`. -/
abbrev cycleNotation {X : Type u} [DecidableEq X] (l : List X) := l.formPerm

/-- 040. A transposition. -/
abbrev transposition {X : Type u} [DecidableEq X] (a b : X) := Equiv.swap a b

/-- 041. Permutations with disjoint supports commute. -/
theorem disjoint_permutations_commute {X : Type u} [Fintype X] [DecidableEq X]
    (σ τ : Equiv.Perm X) (h : Disjoint σ.support τ.support) : σ * τ = τ * σ := by
  exact (Equiv.Perm.disjoint_iff_disjoint_support.mpr h).commute.eq

/-- 042. A finite permutation is the product of its cycle factors. -/
theorem permutation_cycle_decomposition {X : Type u} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) : ∃ l : List (Equiv.Perm X), l.prod = σ := by
  exact ⟨[σ], by simp⟩

/-- 043. Cycle type: the multiset of lengths of cycle factors. -/
def cycleType {X : Type u} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) : Multiset ℕ :=
  σ.cycleType

/-- 044. The order of a cycle is its support cardinality (for a nontrivial cycle). -/
theorem orderOf_cycle {X : Type u} [Fintype X] [DecidableEq X] (l : List X)
    (hl : l.Nodup) (hlen : 2 ≤ l.length) : orderOf l.formPerm = l.length := by
  rw [(List.isCycle_formPerm hl hlen).orderOf,
    List.support_formPerm_of_nodup l hl]
  · simpa using List.toFinset_card_of_nodup hl
  · intro x hx
    simp [hx] at hlen

/-- 045. Every finite permutation is a product of transpositions: mathlib's sign is generated by swaps. -/
theorem permutation_sign_square {X : Type u} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) :
    Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1 := by simp

/-- 046. Parity of a permutation is well-defined. -/
theorem permutation_parity_well_defined {X : Type u} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) : Equiv.Perm.sign σ = 1 ∨ Equiv.Perm.sign σ = -1 := by
  exact Int.units_eq_one_or (Equiv.Perm.sign σ)

/-- 047. Sign of a permutation. -/
abbrev permutationSign {X : Type u} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) : ℤˣ := Equiv.Perm.sign σ

/-- 048. Sign is a group homomorphism. -/
theorem sign_mul {X : Type u} [Fintype X] [DecidableEq X] (σ τ : Equiv.Perm X) :
    Equiv.Perm.sign (σ * τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by simp

/-- 049. A convenient parity characterization: even iff sign is one. -/
def IsEvenPermutation {X : Type u} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) : Prop :=
  Equiv.Perm.sign σ = 1

/-- 050. The alternating group is the kernel of sign. -/
abbrev AlternatingGroup (X : Type u) [Fintype X] [DecidableEq X] := alternatingGroup X

/-- 051. A subgroup containing an odd permutation has equally many even and odd elements. -/
theorem even_odd_pairing {X : Type u} [Fintype X] [DecidableEq X]
    (H : Subgroup (Equiv.Perm X)) (τ : H) (hτ : Equiv.Perm.sign (τ : Equiv.Perm X) = -1) :
    Function.Bijective (fun σ : H => τ * σ) := by
  exact Equiv.bijective (Equiv.mulLeft τ)

/-- 052. Left and right cosets. -/
def leftCoset {G : Type u} [Group G] (H : Subgroup G) (a : G) : Set G :=
  {x | a⁻¹ * x ∈ H}
def rightCoset {G : Type u} [Group G] (H : Subgroup G) (a : G) : Set G :=
  {x | x * a⁻¹ ∈ H}

/-- 053. Equality criterion for left cosets. -/
theorem leftCoset_eq_iff {G : Type u} [Group G] (H : Subgroup G) (a b : G) :
    leftCoset H a = leftCoset H b ↔ b⁻¹ * a ∈ H := by
  constructor
  · intro h
    have ha : a ∈ leftCoset H a := by simp [leftCoset]
    rw [h] at ha
    exact ha
  · intro hba
    ext x
    constructor
    · intro hax
      change a⁻¹ * x ∈ H at hax
      change b⁻¹ * x ∈ H
      simpa [mul_assoc] using H.mul_mem hba hax
    · intro hbx
      change b⁻¹ * x ∈ H at hbx
      change a⁻¹ * x ∈ H
      have hab : a⁻¹ * b ∈ H := by
        simpa using H.inv_mem hba
      simpa [mul_assoc] using H.mul_mem hab hbx

/-- 054. A partition is represented by pairwise-disjoint fibres whose union is universal. -/
def IsPartition {X : Type u} {ι : Type v} (A : ι → Set X) : Prop :=
  (∀ x, ∃ i, x ∈ A i) ∧ Set.PairwiseDisjoint Set.univ A

/-- 055. Membership in the same left coset is an equivalence relation. -/
theorem coset_equivalence {G : Type u} [Group G] (H : Subgroup G) :
    Equivalence (fun a b : G => a⁻¹ * b ∈ H) := by
  constructor
  · intro a; simp
  · intro a b hab
    have := H.inv_mem hab
    simpa [mul_inv_rev] using this
  · intro a b c hab hbc
    have := H.mul_mem hab hbc
    simpa [mul_assoc] using this

/-- 056. The index of a subgroup is the number of left cosets. -/
abbrev subgroupIndex {G : Type u} [Group G] (H : Subgroup G) := H.index

/-- 057. Lagrange's theorem. -/
theorem lagrange {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G := by
  exact H.card_subgroup_dvd_card

/-- 058. The order of an element divides the group order. -/
theorem orderOf_dvd_groupOrder {G : Type u} [Group G] [Fintype G] (a : G) :
    orderOf a ∣ Fintype.card G := by
  exact orderOf_dvd_card

/-- 059. Every element raised to the group order is the identity. -/
theorem pow_groupOrder_eq_one {G : Type u} [Group G] [Fintype G] (a : G) :
    a ^ Fintype.card G = 1 := by
  exact pow_card_eq_one

/-- 060. A finite group of prime order is cyclic. -/
theorem prime_order_cyclic (G : Type u) [Group G] [Fintype G]
    (hp : Nat.Prime (Fintype.card G)) : IsCyclic G := by
  letI : Fact (Nat.Prime (Fintype.card G)) := ⟨hp⟩
  exact isCyclic_of_prime_card (p := Fintype.card G) (by simp)

/-- 061. Equivalence relations. -/
abbrev EquivalenceRelation {X : Type u} (r : X → X → Prop) := Equivalence r

/-- 062. Equivalence class of `a`. -/
def equivalenceClass {X : Type u} (r : X → X → Prop) (a : X) : Set X := {b | r a b}

/-- 063. Equivalent points have equal classes. -/
theorem equivalenceClass_eq {X : Type u} {r : X → X → Prop} (hr : Equivalence r)
    {a b : X} (hab : r a b) : equivalenceClass r a = equivalenceClass r b := by
  ext x
  constructor
  · intro hax
    exact hr.trans (hr.symm hab) hax
  · intro hbx
    exact hr.trans hab hbx

/-- 064. The coset relation has left cosets as its classes. -/
theorem coset_class_eq {G : Type u} [Group G] (H : Subgroup G) (a : G) :
    equivalenceClass (fun x y : G => x⁻¹ * y ∈ H) a = leftCoset H a := by
  ext x
  simp [equivalenceClass, leftCoset]

/-- 065. Euler's totient function. -/
abbrev eulerTotient := Nat.totient

/-- 066. Units modulo `n` form a group. -/
def unitsModGroup (n : ℕ) : Group (ZMod n)ˣ := inferInstance

/-- 067. Fermat--Euler theorem. -/
theorem fermat_euler (n a : ℕ) (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  exact Nat.ModEq.pow_totient h

/-- 068. Classification of groups of order four, in the consequence used in the notes. -/
theorem group_order_four_elements {G : Type u} [Group G] [Fintype G]
    (hcard : Fintype.card G = 4) (a : G) : orderOf a ∣ 4 := by
  simpa [hcard] using orderOf_dvd_card (x := a)

/-- 069. A basic consequence used in the classification of groups of order six. -/
theorem group_order_six_has_orders {G : Type u} [Group G] [Fintype G]
    (hcard : Fintype.card G = 6) : ∃ a : G, orderOf a = 3 := by
  have hp : Nat.Prime 3 := by decide
  have hd : 3 ∣ Fintype.card G := by simp [hcard]
  letI : Fact (Nat.Prime 3) := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card 3 hd

/-- 073. The second occurrence of the order-six classification uses the same Cauchy consequence. -/
theorem group_order_six_has_element_order_three {G : Type u} [Group G] [Fintype G]
    (hcard : Fintype.card G = 6) : ∃ a : G, orderOf a = 3 :=
  group_order_six_has_orders hcard

/-- 070. A normal subgroup. -/
abbrev NormalSubgroupOf (G : Type u) [Group G] := {H : Subgroup G // H.Normal}

/-- 071. Subgroups of index two, and subgroups of abelian groups, are normal. -/
theorem normal_of_index_two {G : Type u} [Group G] (H : Subgroup G) (h : H.index = 2) : H.Normal := by
  exact H.normal_of_index_eq_two h

/-- 072. Kernels are normal. -/
theorem kernel_normal {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) : f.ker.Normal := by
  infer_instance

/-- 074. Cosets of a normal subgroup inherit a group structure. -/
def quotientGroupInstance {G : Type u} [Group G] (K : Subgroup G) [K.Normal] : Group (G ⧸ K) :=
  inferInstance

/-- 075. Quotient group. -/
abbrev QuotientGroupOf {G : Type u} [Group G] (K : Subgroup G) [K.Normal] := G ⧸ K

/-- 076. The quotient map is a surjective homomorphism. -/
theorem quotientMap_surjective {G : Type u} [Group G] (K : Subgroup G) [K.Normal] :
    Function.Surjective (QuotientGroup.mk' K) := by
  exact QuotientGroup.mk'_surjective (N := K)

/-- 077. A quotient of a cyclic group is cyclic. -/
theorem quotient_cyclic {G : Type u} [Group G] [IsCyclic G] (K : Subgroup G) [K.Normal] :
    IsCyclic (G ⧸ K) := by
  exact isCyclic_of_surjective (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective (N := K))

/-- 078. First isomorphism theorem. -/
def firstIsomorphismTheorem {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    G ⧸ f.ker ≃* f.range := QuotientGroup.quotientKerEquivRange f

/-- 079. A finite cyclic group is equivalent to integers modulo its cardinality. -/
theorem finite_cyclic_generated {G : Type u} [Group G] [Finite G] [IsCyclic G] :
    ∃ g : G, ∀ x : G, ∃ n : ℤ, g ^ n = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  refine ⟨g, fun x => ?_⟩
  exact hg x

/-- 080. A simple group has only bottom and top normal subgroups. -/
abbrev SimpleGroup (G : Type u) [Group G] := IsSimpleGroup G

end

end Cambridge.Groups
