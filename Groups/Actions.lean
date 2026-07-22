import Groups.Foundations

/-! Part IA Groups: group actions, conjugacy, and small groups (source 081--112). -/

namespace Cambridge.Groups

universe u v

/-- 081. A group action is Lean's `MulAction` typeclass. -/
abbrev GroupAction (G : Type u) (X : Type v) [Group G] := MulAction G X

/-- 082. The two action axioms. -/
theorem action_axioms (G : Type u) (X : Type v) [Group G] [MulAction G X] (g h : G) (x : X) :
    (1 : G) • x = x ∧ (g * h) • x = g • h • x := by
  exact ⟨one_smul G x, mul_smul g h x⟩

/-- 083. Kernel of an action. -/
def actionKernel (G : Type u) (X : Type v) [Group G] [MulAction G X] : Subgroup G :=
  (MulAction.toPermHom G X).ker

/-- 084. Faithful action. -/
abbrev FaithfulAction (G : Type u) (X : Type v) [Group G] [MulAction G X] := FaithfulSMul G X

/-- 085. Orbit of a point. -/
abbrev orbitOf (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) := MulAction.orbit G x

/-- 086. Stabilizer of a point. -/
abbrev stabilizerOf (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) := MulAction.stabilizer G x

/-- 087. A stabilizer is a subgroup (by its type). -/
theorem stabilizer_contains_one (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) :
    (1 : G) ∈ MulAction.stabilizer G x := by simp

/-- 088. Transitive action. -/
abbrev TransitiveAction (G : Type u) (X : Type v) [Group G] [MulAction G X] := MulAction.IsPretransitive G X

/-- 089. Orbit membership is an equivalence relation. -/
theorem orbit_relation_equivalence (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    Equivalence (fun x y : X => y ∈ MulAction.orbit G x) := by
  constructor
  · intro x; exact ⟨1, by simp⟩
  · intro x y
    rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp⟩
  · intro x y z
    rintro ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨h * g, by simp [mul_smul]⟩

/-- 090. Orbit--stabilizer theorem for finite groups. -/
theorem orbit_stabilizer_card (G : Type u) {X : Type v} [Group G] [Fintype G]
    [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

/-- 091. Left multiplication gives a faithful and transitive action of a group on itself. -/
theorem left_regular_action (G : Type u) [Group G] :
    Function.Injective (fun g : G => Equiv.mulLeft g) := by
  intro a b h
  have := DFunLike.congr_fun h 1
  simpa using this

/-- 092. Cayley's theorem. -/
noncomputable def cayleyEmbedding (G : Type u) [Group G] :
    G ≃* (MulAction.toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

/-- 093. Left multiplication on cosets is transitive. -/
theorem left_coset_action_transitive {G : Type u} [Group G] (H : Subgroup G) :
    ∀ a b : G, ∃ g : G, leftCoset H (g * a) = leftCoset H b := by
  intro a b
  refine ⟨b * a⁻¹, ?_⟩
  simp [mul_assoc]

/-- 094. Conjugation of an element. -/
def conjugate {G : Type u} [Group G] (b a : G) : G := b * a * b⁻¹

/-- 095. Conjugation satisfies the action law. -/
theorem conjugation_action_law {G : Type u} [Group G] (g h x : G) :
    conjugate (g * h) x = conjugate g (conjugate h x) := by
  simp [conjugate, mul_assoc]

/-- 096. Conjugacy class and centralizer. -/
def conjugacyClass {G : Type u} [Group G] (a : G) : Set G := {b | ∃ g, conjugate g a = b}
abbrev centralizerOf {G : Type u} [Group G] (a : G) := Subgroup.centralizer ({a} : Set G)

/-- 097. Center of a group. -/
abbrev centerOf (G : Type u) [Group G] := Subgroup.center G

/-- 098. A normal subgroup is closed under conjugation. -/
theorem normal_conjugate_mem {G : Type u} [Group G] (K : Subgroup G) [K.Normal]
    (g : G) {k : G} (hk : k ∈ K) : conjugate g k ∈ K := by
  simpa [conjugate] using Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk g

/-- 099. A subgroup is normal iff it contains every conjugacy class meeting it. -/
theorem normal_iff_conjugacy_closed {G : Type u} [Group G] (K : Subgroup G) :
    K.Normal ↔ ∀ g : G, ∀ k ∈ K, conjugate g k ∈ K := by
  constructor
  · intro h g k hk
    simpa [conjugate] using Subgroup.Normal.conj_mem h k hk g
  · intro h
    exact ⟨fun k hk g => by simpa [conjugate] using h g k hk⟩

/-- 100. Conjugation sends a subgroup to a subgroup. -/
def conjugateSubgroup {G : Type u} [Group G] (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

/-- 101. Normalizer of a subgroup. -/
abbrev normalizerOf {G : Type u} [Group G] (H : Subgroup G) :=
  Subgroup.normalizer (H : Set G)

/-- 102. Stabilizers of points in the same orbit are conjugate. -/
theorem stabilizer_smul {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = conjugateSubgroup g (MulAction.stabilizer G x) := by
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g x

/-- 103. Cauchy's theorem. -/
theorem cauchy {G : Type u} [Group G] [Fintype G] {p : ℕ}
    (hp : Nat.Prime p) (hd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card p hd

/-- 104. Conjugating a permutation transports its cycle. -/
theorem conjugate_cycle {X : Type u} (ρ σ : Equiv.Perm X) (hσ : σ.IsCycle) :
    (ρ * σ * ρ⁻¹).IsCycle := by
  exact hσ.conj

/-- 105. Conjugation preserves cycle type. -/
theorem cycleType_conjugate {X : Type u} [Fintype X] [DecidableEq X]
    (ρ σ : Equiv.Perm X) : cycleType (ρ * σ * ρ⁻¹) = cycleType σ := by
  exact Equiv.Perm.cycleType_conj

/-- 106. Predicate saying an alternating-group conjugacy class splits. -/
def ConjugacyClassSplits {X : Type u} [Fintype X] [DecidableEq X]
    (σ : alternatingGroup X) : Prop :=
  Nat.card (MulAction.orbit (ConjAct (alternatingGroup X)) σ) * 2 =
    Nat.card (MulAction.orbit (ConjAct (Equiv.Perm X)) (σ : Equiv.Perm X))

/-- 107. Abstract index-two splitting criterion used in the notes. -/
theorem index_two_class_splitting_criterion {G : Type u} [Group G] (H : Subgroup G)
    (hindex : H.index = 2) (x : H) :
    (∀ g : G, g * x * g⁻¹ = x → g ∈ H) ↔
      Subgroup.centralizer ({(x : G)} : Set G) ≤ H := by
  constructor
  · intro h g hg
    apply h g
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  · intro h g hg
    apply h
    rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul]
    exact hg

/-- 108. A 5-cycle generates a cyclic subgroup of order five. -/
theorem five_cycle_order {X : Type u} [Fintype X] [DecidableEq X] (l : List X)
    (hl : l.Nodup) (hlen : l.length = 5) : orderOf l.formPerm = 5 := by
  rw [orderOf_cycle l hl (by omega), hlen]

/-- 109. Mathlib's theorem that `A₅` is simple. -/
theorem alternatingGroupFive_simple : IsSimpleGroup (alternatingGroup (Fin 5)) := by
  infer_instance

/-- 110. Quaternion group. -/
abbrev QuaternionEight := QuaternionGroup 2

/-- 111. The quaternion relations, represented by the bundled quaternion group. -/
theorem quaternion_order : Nat.card QuaternionEight = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- 112. For a group of order eight, every element has order dividing eight. -/
theorem order_eight_element_orders {G : Type u} [Group G] [Fintype G]
    (hcard : Fintype.card G = 8) (g : G) : orderOf g ∣ 8 := by
  simpa [hcard] using orderOf_dvd_card (x := g)

end Cambridge.Groups
