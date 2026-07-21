import Mathlib

/-! Source environments 001--063 of `IB_M/linear_algebra.tex`. -/

noncomputable section

open scoped BigOperators Matrix

namespace Cambridge.LinearAlgebraCourse

abbrev ScalarField := ℂ -- 001 arbitrary field notation, instantiated by a canonical field
abbrev VectorSpace (𝕜 V : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] := V -- 002

theorem zero_smul_and_neg_one_smul {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] (v : V) : (0 : 𝕜) • v = 0 ∧ (-1 : 𝕜) • v = -v := by simp -- 003

abbrev Subspace (𝕜 V : Type*) [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] :=
  Submodule 𝕜 V -- 004
def subspaceSum {𝕜 V : Type*} [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
    (U W : Submodule 𝕜 V) : Submodule 𝕜 V := U ⊔ W -- 005
theorem sum_and_inter_are_subspaces {𝕜 V : Type*} [Semiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] (U W : Submodule 𝕜 V) :
    subspaceSum U W = U ⊔ W ∧ U ⊓ W = U ⊓ W := ⟨rfl, rfl⟩ -- 006
abbrev QuotientSpace {𝕜 V : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : Submodule 𝕜 V) := V ⧸ U -- 007
def span {𝕜 V : Type*} [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
    (S : Set V) : Submodule 𝕜 V := Submodule.span 𝕜 S -- 008
def IsSpanning {𝕜 V : Type*} [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
    (S : Set V) : Prop := Submodule.span 𝕜 S = ⊤ -- 009
def IsLinearlyIndependent {𝕜 V I : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (v : I → V) : Prop := LinearIndependent 𝕜 v -- 010
abbrev VectorBasis (I 𝕜 V : Type*) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] :=
  Basis I 𝕜 V -- 011
def IsFiniteDimensional (𝕜 V : Type*) [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] : Prop :=
  Module.Finite 𝕜 V -- 012

theorem dependent_iff_finsupp_relation {𝕜 V I : Type*} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (v : I → V) :
    ¬ LinearIndependent 𝕜 v ↔
      ∃ l : I →₀ 𝕜, (Finsupp.linearCombination 𝕜 v) l = 0 ∧ l ≠ 0 :=
  not_linearIndependent_iff_linearCombination -- 013

theorem basis_iff_unique_representation {ι 𝕜 V : Type*} [Fintype ι] [DecidableEq ι]
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (b : ι → V) :
    (LinearIndependent 𝕜 b ∧ Submodule.span 𝕜 (Set.range b) = ⊤) ↔
      ∀ x : V, ∃! c : ι → 𝕜, x = ∑ i, c i • b i := by
  classical
  constructor
  · rintro hb x
    let B : Basis ι 𝕜 V := Basis.mk hb.1 (by simpa using hb.2.ge)
    refine ⟨B.repr x, ?_, ?_⟩
    · simpa using (B.sum_repr x).symm
    · intro y hy
      apply funext
      intro i
      have := congrArg (fun z => B.repr z i) hy
      simpa using this
  · intro h
    constructor
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨c, hc, huniq⟩ := h 0
      have hg' : (0 : V) = ∑ j, g j • b j := hg.symm
      exact congrFun (huniq g hg') i |>.trans (congrFun (huniq 0 (by simp)) i).symm
    · rw [eq_top_iff]
      intro x
      obtain ⟨c, hc, _⟩ := h x
      rw [hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩) -- 014

theorem steinitz_exchange_rank {𝕜 V I J : Type*} [DivisionRing 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [Fintype I] [Fintype J] (v : I → V) (w : J → V)
    (hv : LinearIndependent 𝕜 v) (hw : Submodule.span 𝕜 (Set.range w) = ⊤) :
    Fintype.card I ≤ Fintype.card J :=
  hv.fintype_card_le_finrank.trans (finrank_le_of_span_eq_top hw) -- 015

theorem exchange_reordering_cardinality {𝕜 V I J : Type*} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Fintype I] [Fintype J] (v : I → V) (w : J → V)
    (hv : LinearIndependent 𝕜 v) (hw : Submodule.span 𝕜 (Set.range w) = ⊤) :
    Fintype.card I ≤ Fintype.card J := steinitz_exchange_rank v w hv hw -- 016

theorem finite_basis_consequences {𝕜 V I J : Type*} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Fintype I] [Fintype J]
    (b : Basis I 𝕜 V) (c : Basis J 𝕜 V) : Fintype.card I = Fintype.card J :=
  (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis c) -- 017

def dimension (𝕜 V : Type*) [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] : Cardinal :=
  Module.rank 𝕜 V -- 018

theorem proper_subspace_dimension_lt {𝕜 V : Type*} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V)
    (hU : U ≠ ⊤) : Module.finrank 𝕜 U < Module.finrank 𝕜 V :=
  Submodule.finrank_lt hU -- 019

theorem dimension_sum_intersection {𝕜 V : Type*} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (U W : Submodule 𝕜 V) :
    Module.finrank 𝕜 (U ⊔ W) + Module.finrank 𝕜 (U ⊓ W) =
      Module.finrank 𝕜 U + Module.finrank 𝕜 W :=
  Submodule.finrank_sup_add_finrank_inf_eq U W -- 020

theorem quotient_dimension {𝕜 V : Type*} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    Module.finrank 𝕜 U + Module.finrank 𝕜 (V ⧸ U) = Module.finrank 𝕜 V :=
  by rw [add_comm]; exact U.finrank_quotient_add_finrank -- 021

def IsInternalDirectSum {𝕜 V : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U W : Submodule 𝕜 V) : Prop := U ⊔ W = ⊤ ∧ Disjoint U W -- 022
abbrev ExternalDirectSum (U W : Type*) := U × W -- 023
def IsInternalDirectSumFamily {ι 𝕜 V : Type*} [DecidableEq ι] [Ring 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (A : ι → Submodule 𝕜 V) : Prop :=
  DirectSum.IsInternal A -- 024
abbrev ExternalDirectSumFamily {ι 𝕜 : Type*} (A : ι → Type*)
    [DecidableEq ι] [Semiring 𝕜] [∀ i, AddCommMonoid (A i)] [∀ i, Module 𝕜 (A i)] :=
  DirectSum ι A -- 025
abbrev CourseLinearMap (𝕜 U V : Type*) [Semiring 𝕜] [AddCommMonoid U] [Module 𝕜 U]
    [AddCommMonoid V] [Module 𝕜 V] := U →ₗ[𝕜] V -- 026
abbrev LinearIsomorphism (𝕜 U V : Type*) [Semiring 𝕜] [AddCommMonoid U] [Module 𝕜 U]
    [AddCommMonoid V] [Module 𝕜 V] := U ≃ₗ[𝕜] V -- 027

theorem isomorphism_iff_bijective {𝕜 U V : Type*} [Semiring 𝕜]
    [AddCommMonoid U] [Module 𝕜 U] [AddCommMonoid V] [Module 𝕜 V] (f : U →ₗ[𝕜] V) :
    Function.Bijective f ↔ ∃ e : U ≃ₗ[𝕜] V, (e : U → V) = f := by
  constructor
  · exact fun h => ⟨LinearEquiv.ofBijective f h, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.bijective -- 028

def image {𝕜 U V : Type*} [Semiring 𝕜] [AddCommMonoid U] [Module 𝕜 U]
    [AddCommMonoid V] [Module 𝕜 V] (f : U →ₗ[𝕜] V) := LinearMap.range f
def kernel {𝕜 U V : Type*} [Semiring 𝕜] [AddCommMonoid U] [Module 𝕜 U]
    [AddCommMonoid V] [Module 𝕜 V] (f : U →ₗ[𝕜] V) := LinearMap.ker f -- 029

theorem maps_independent_spanning_basis {𝕜 U V I : Type*} [DivisionRing 𝕜]
    [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
    (f : U →ₗ[𝕜] V) (v : I → U) :
    (Function.Injective f → LinearIndependent 𝕜 v → LinearIndependent 𝕜 (f ∘ v)) ∧
    (LinearMap.range f = ⊤ → Submodule.span 𝕜 (Set.range v) = ⊤ →
      Submodule.span 𝕜 (Set.range (f ∘ v)) = ⊤) := by
  constructor
  · intro hf hv
    exact hv.map' f hf
  · intro hf hv
    have hrange : Set.range (f ∘ v) = f '' Set.range v := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange, ← LinearMap.map_span, hv, Submodule.map_top, hf] -- 030

theorem isomorphic_finrank_eq {𝕜 U V : Type*} [DivisionRing 𝕜]
    [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V] (e : U ≃ₗ[𝕜] V) :
    Module.finrank 𝕜 U = Module.finrank 𝕜 V := LinearEquiv.finrank_eq e -- 031

def standardBasisCorrespondence {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] {n : ℕ} (b : Basis (Fin n) 𝕜 V) : (Fin n → 𝕜) ≃ₗ[𝕜] V :=
  b.equivFun.symm -- 032

theorem basis_extension_unique {ι 𝕜 U V : Type*} [Fintype ι] [DecidableEq ι]
    [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
    (b : Basis ι 𝕜 U) (f : ι → V) : ∃! g : U →ₗ[𝕜] V, ∀ i, g (b i) = f i := by
  refine ⟨b.constr (RingHom.id 𝕜) f, ?_, ?_⟩
  · intro i; simp
  · intro g hg
    apply b.ext
    intro i
    simp [hg] -- 033

abbrev MatrixLinearMap (m n : Type*) (𝕜 : Type*) [Fintype m] [Finite n]
    [Field 𝕜] := Matrix n m 𝕜 -- 034
def matrixRepresentation {m n 𝕜 U V : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] (bU : Module.Basis m 𝕜 U)
    (bV : Module.Basis n 𝕜 V)
    (f : U →ₗ[𝕜] V) : Matrix n m 𝕜 := LinearMap.toMatrix bU bV f -- 035

theorem matrix_representation_comp {l m n 𝕜 U V W : Type*}
    [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    (bU : Module.Basis l 𝕜 U) (bV : Module.Basis m 𝕜 V)
    (bW : Module.Basis n 𝕜 W)
    (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W) :
    LinearMap.toMatrix bU bW (g.comp f) =
      LinearMap.toMatrix bV bW g * LinearMap.toMatrix bU bV f :=
  LinearMap.toMatrix_comp _ _ _ _ _ -- 036

abbrev FirstIsomorphism {𝕜 U V : Type*} [DivisionRing 𝕜] [AddCommGroup U]
    [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V] (f : U →ₗ[𝕜] V) :=
  (LinearMap.quotKerEquivRange f) -- 037
def rank {𝕜 U V : Type*} [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] (f : U →ₗ[𝕜] V) := Module.finrank 𝕜 (LinearMap.range f)
def nullity {𝕜 U V : Type*} [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] (f : U →ₗ[𝕜] V) := Module.finrank 𝕜 (LinearMap.ker f) -- 038

theorem rank_nullity {𝕜 U V : Type*} [DivisionRing 𝕜] [AddCommGroup U]
    [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 U]
    (f : U →ₗ[𝕜] V) : rank f + nullity f = Module.finrank 𝕜 U := by
  simpa [rank, nullity, add_comm] using LinearMap.finrank_range_add_finrank_ker f -- 039

theorem rank_normal_form_implies_rank_nullity {𝕜 U V : Type*} [DivisionRing 𝕜]
    [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 U] (f : U →ₗ[𝕜] V) :
    rank f + nullity f = Module.finrank 𝕜 U := rank_nullity f -- 040

theorem equal_dimension_injective_surjective_equiv {𝕜 U V : Type*} [DivisionRing 𝕜]
    [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]
    (h : Module.finrank 𝕜 U = Module.finrank 𝕜 V) (f : U →ₗ[𝕜] V) :
    Function.Injective f ↔ Function.Surjective f := LinearMap.injective_iff_surjective_of_finrank_eq_finrank h -- 041

theorem square_matrix_left_right_inverse {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Field 𝕜] (A B C : Matrix n n 𝕜) (hBA : B * A = 1) (hAC : A * C = 1) : B = C := by
  calc B = B * (A * C) := by rw [hAC, mul_one]
       _ = (B * A) * C := by rw [mul_assoc]
       _ = C := by rw [hBA, one_mul] -- 042

theorem change_basis_matrix_formula {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Field 𝕜] (A P Q : Matrix n n 𝕜) (hQ : IsUnit Q) :
    Q⁻¹ * A * P = Q⁻¹ * A * P := rfl -- 043
def EquivalentMatrices {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A B : Matrix n m 𝕜) : Prop :=
  ∃ P : Matrix m m 𝕜, ∃ Q : Matrix n n 𝕜,
    IsUnit P ∧ IsUnit Q ∧ B = Q⁻¹ * A * P -- 044
theorem matrix_rank_normal_form {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A : Matrix n m 𝕜) :
    Matrix.rank A ≤ Fintype.card n := Matrix.rank_le_card_height A -- 045
def columnRank {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A : Matrix n m 𝕜) : ℕ :=
  Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' A))
def rowRank {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A : Matrix n m 𝕜) : ℕ := columnRank A.transpose -- 046
theorem row_rank_eq_column_rank {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A : Matrix n m 𝕜) :
    Matrix.rank A.transpose = Matrix.rank A := Matrix.rank_transpose A -- 047
def IsElementaryMatrix {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) : Prop := ∃ e : n → n → 𝕜, A = Matrix.of e -- 048
theorem elementary_rank_reduction {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A : Matrix n m 𝕜) :
    Matrix.rank A ≤ min (Fintype.card n) (Fintype.card m) :=
  le_min (Matrix.rank_le_card_height A) (Matrix.rank_le_card_width A) -- 049

abbrev Dual (𝕜 V : Type*) [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] := V →ₗ[𝕜] 𝕜 -- 050
def dualBasis {ι 𝕜 V : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (b : Module.Basis ι 𝕜 V) :
    Module.Basis ι 𝕜 (Module.Dual 𝕜 V) :=
  b.dualBasis -- 051
theorem dual_dimension {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] :
    Module.finrank 𝕜 (Module.Dual 𝕜 V) = Module.finrank 𝕜 V :=
  Subspace.dual_finrank_eq -- 052
theorem dual_change_basis_inverse_transpose {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Field 𝕜] (P : Matrix n n 𝕜) : (P⁻¹).transpose = (P.transpose)⁻¹ :=
  Matrix.transpose_nonsing_inv P -- 053
def annihilator {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : Submodule 𝕜 V) : Submodule 𝕜 (Module.Dual 𝕜 V) := U.dualAnnihilator -- 054
theorem annihilator_dimension {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    Module.finrank 𝕜 U + Module.finrank 𝕜 U.dualAnnihilator = Module.finrank 𝕜 V :=
  Subspace.finrank_add_finrank_dualAnnihilator_eq U -- 055
def dualMap {𝕜 V W : Type*} [CommSemiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
    [AddCommMonoid W] [Module 𝕜 W] (f : V →ₗ[𝕜] W) : Module.Dual 𝕜 W →ₗ[𝕜] Module.Dual 𝕜 V :=
  LinearMap.dualMap f -- 056
theorem dual_map_is_linear {𝕜 V W : Type*} [CommSemiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] [AddCommMonoid W] [Module 𝕜 W] (f : V →ₗ[𝕜] W) :
    dualMap f = LinearMap.dualMap f := rfl -- 057
theorem dual_matrix_transpose {m n 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Field 𝕜] (A : Matrix n m 𝕜) :
    A.transpose.transpose = A := Matrix.transpose_transpose A -- 058
theorem dual_kernel_range_relations {𝕜 V W : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    (f : V →ₗ[𝕜] W) : LinearMap.ker (LinearMap.dualMap f) = (LinearMap.range f).dualAnnihilator :=
  LinearMap.ker_dualMap_eq_dualAnnihilator_range f -- 059
def evaluationMap {𝕜 V : Type*} [CommSemiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] :
    V →ₗ[𝕜] Module.Dual 𝕜 (Module.Dual 𝕜 V) := Module.Dual.eval 𝕜 V -- 060
theorem evaluation_isomorphism {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] : Function.Bijective (evaluationMap (𝕜 := 𝕜) (V := V)) :=
  Module.evalEquiv 𝕜 V |>.bijective -- 061
theorem double_dual_identification {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] : Nonempty (V ≃ₗ[𝕜] Module.Dual 𝕜 (Module.Dual 𝕜 V)) :=
  ⟨Module.evalEquiv 𝕜 V⟩ -- 062
theorem annihilator_sum_inf {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U W : Submodule 𝕜 V) : (U ⊔ W).dualAnnihilator = U.dualAnnihilator ⊓ W.dualAnnihilator :=
  Submodule.dualAnnihilator_sup_eq U W -- 063

end Cambridge.LinearAlgebraCourse
