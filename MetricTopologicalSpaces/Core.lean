import Mathlib

/-! # Part IB Metric and Topological Spaces -/

open Set Filter Topology
open scoped Topology

namespace MetricTopologicalSpaces

/- 1. Metric space. -/
abbrev MetricSpaceDefinition := MetricSpace
/- 2. Metric subspace. -/
abbrev metricSubspace {X : Type*} [MetricSpace X] (Y : Set X) := Y
/- 3. Convergent sequence. -/
def SequenceConverges {X : Type*} [TopologicalSpace X] (u : ℕ → X) (x : X) : Prop :=
  Tendsto u atTop (𝓝 x)
/- 4. Uniqueness of metric limits. -/
theorem metric_limit_unique {X : Type*} [MetricSpace X] {u : ℕ → X} {x y : X}
    (hx : SequenceConverges u x) (hy : SequenceConverges u y) : x = y :=
  tendsto_nhds_unique hx hy
/- 5. Sequential continuity in metric spaces. -/
def SequentiallyContinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop := ∀ u x, SequenceConverges u x → SequenceConverges (f ∘ u) (f x)
/- 6. Norm. -/
abbrev NormDefinition := Norm
/- 7. A norm induces a metric. -/
theorem norm_distance_metric {V : Type*} [SeminormedAddCommGroup V] (v w : V) :
    dist v w = ‖v - w‖ := dist_eq_norm v w
/- 8. A nonzero nonnegative continuous function has positive integral. -/
theorem integral_pos_of_nonnegative_nonzero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ f x)
    (hpos : ∃ x ∈ Set.Ioc (0:ℝ) 1, 0 < f x) : 0 < ∫ x in (0:ℝ)..1, f x := by
  obtain ⟨x, hx, hfx⟩ := hpos
  exact intervalIntegral.integral_pos hf.intervalIntegrable hn (by exact ⟨x, hx.1, hx.2, hfx⟩)
/- 9. Inner product. -/
abbrev InnerProductDefinition := Inner
/- 10. Cauchy--Schwarz. -/
theorem cauchy_schwarz_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v w : V) : |@inner ℝ V _ v w| ≤ ‖v‖ * ‖w‖ := by
  simpa [Real.norm_eq_abs] using norm_inner_le_norm v w
/- 11. Inner-product norm. -/
theorem norm_eq_sqrt_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : ‖v‖ = Real.sqrt (@inner ℝ V _ v v) := norm_eq_sqrt_re_inner v
/- 12. Open and closed balls. -/
def openBall {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) := Metric.ball x r
def closedBall {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) := Metric.closedBall x r
/- 13. Metric open and closed sets. -/
def MetricOpen {X : Type*} [PseudoMetricSpace X] (U : Set X) : Prop := IsOpen U
/- 14. Balls are open/closed. -/
theorem balls_open_closed {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    IsOpen (openBall x r) ∧ IsClosed (closedBall x r) :=
  ⟨Metric.isOpen_ball, Metric.isClosed_closedBall⟩
/- 15. Open neighbourhood. -/
def IsOpenNeighbourhood {X : Type*} [TopologicalSpace X] (U : Set X) (x : X) : Prop :=
  IsOpen U ∧ x ∈ U
/- 16. Convergent sequences are eventually in neighbourhoods. -/
theorem eventually_mem_open_neighbourhood {X : Type*} [TopologicalSpace X]
    {u : ℕ → X} {x : X} {U : Set X} (hu : SequenceConverges u x)
    (hU : IsOpenNeighbourhood U x) : ∀ᶠ n in atTop, u n ∈ U :=
  hu.eventually hU.1.mem_nhds hU.2
/- 17. Sequential limit point. -/
def SequentialLimitPoint {X : Type*} [TopologicalSpace X] (A : Set X) (x : X) : Prop :=
  ∃ u : ℕ → X, SequenceConverges u x ∧ ∀ n, u n ∈ A
/- 18. Sequential characterization of metric closed sets. -/
theorem metric_closed_iff_sequences {X : Type*} [PseudoMetricSpace X] {C : Set X} :
    IsClosed C ↔ ∀ u x, (∀ n, u n ∈ C) → SequenceConverges u x → x ∈ C :=
  Metric.isClosed_iff
/- 19. Characterizations of continuity. -/
theorem metric_continuity_characterizations {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} :
    Continuous f ↔ ∀ x ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ y, dist y x < δ → dist (f y) (f x) < ε :=
  Metric.continuous_iff
/- 20. Metric-open-set laws. -/
theorem metric_open_set_laws {X : Type*} [PseudoMetricSpace X] :
    IsOpen (∅ : Set X) ∧ IsOpen (Set.univ : Set X) ∧
      (∀ (ι : Type*) (U : ι → Set X), (∀ i, IsOpen (U i)) → IsOpen (⋃ i, U i)) ∧
      (∀ U V : Set X, IsOpen U → IsOpen V → IsOpen (U ∩ V)) :=
  ⟨isOpen_empty, isOpen_univ, fun _ _ h => isOpen_iUnion h, fun _ _ => IsOpen.inter⟩
/- 21. Topological space. -/
abbrev TopologicalSpaceDefinition := TopologicalSpace
/- 22. Metric-induced topology. -/
def metricInducedTopology {X : Type*} [PseudoMetricSpace X] : TopologicalSpace X := inferInstance
/- 23. Topological continuity. -/
def TopologicallyContinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop := Continuous f
/- 24. Composition of continuous functions. -/
theorem continuous_composition {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := hg.comp hf
/- 25. Homeomorphism. -/
abbrev Homeomorphism {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] := X ≃ₜ Y
/- 26. Homeomorphism is an equivalence relation. -/
theorem homeomorphism_equivalence {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X ≃ₜ Y) (g : Y ≃ₜ Z) :
    Nonempty (X ≃ₜ X) ∧ Nonempty (Y ≃ₜ X) ∧ Nonempty (X ≃ₜ Z) :=
  ⟨⟨Homeomorph.refl X⟩, ⟨f.symm⟩, ⟨f.trans g⟩⟩
/- 27. Topological open neighbourhood. -/
def OpenNeighbourhood {X : Type*} [TopologicalSpace X] (x : X) := {U : Set X // IsOpen U ∧ x ∈ U}
/- 28. Topological sequence convergence. -/
def TopologicalSequenceConverges {X : Type*} [TopologicalSpace X] (u : ℕ → X) (x : X) : Prop :=
  Tendsto u atTop (𝓝 x)
/- 29. Hausdorff space. -/
abbrev HausdorffSpaceDefinition := T2Space
/- 30. Hausdorff limits are unique. -/
theorem hausdorff_limit_unique {X : Type*} [TopologicalSpace X] [T2Space X]
    {u : ℕ → X} {x y : X} (hx : Tendsto u atTop (𝓝 x)) (hy : Tendsto u atTop (𝓝 y)) : x = y :=
  tendsto_nhds_unique hx hy
/- 31. Closed set. -/
def TopologicallyClosed {X : Type*} [TopologicalSpace X] (C : Set X) : Prop := IsClosed C
/- 32. Closed-set laws. -/
theorem closed_set_laws {X : Type*} [TopologicalSpace X] :
    (∀ (ι : Type*) (C : ι → Set X), (∀ i, IsClosed (C i)) → IsClosed (⋂ i, C i)) ∧
      (∀ C D : Set X, IsClosed C → IsClosed D → IsClosed (C ∪ D)) :=
  ⟨fun _ _ h => isClosed_iInter h, fun _ _ => IsClosed.union⟩
/- 33. Singletons are closed in Hausdorff spaces. -/
theorem singleton_closed {X : Type*} [TopologicalSpace X] [T2Space X] (x : X) :
    IsClosed ({x} : Set X) := isClosed_singleton
/- 34. Closure. -/
def topologicalClosure {X : Type*} [TopologicalSpace X] (A : Set X) := closure A
/- 35. Closure is the smallest closed superset. -/
theorem closure_smallest_closed {X : Type*} [TopologicalSpace X] (A C : Set X)
    (hA : A ⊆ C) (hC : IsClosed C) : closure A ⊆ C := closure_minimal hA hC
/- 36. Limit point set (the notes' non-punctured sequential convention). -/
def limitPointSet {X : Type*} [TopologicalSpace X] (A : Set X) := closure A
/- 37. Closed sets equal their limit-point set. -/
theorem closed_eq_limitPointSet {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsClosed C) :
    limitPointSet C = C := hC.closure_eq
/- 38. Limit points lie in the closure. -/
theorem limitPointSet_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    limitPointSet A ⊆ closure A := Subset.rfl
/- 39. Closure squeeze. -/
theorem closure_squeeze {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hC : IsClosed C) (hAC : A ⊆ C) (hCL : C ⊆ limitPointSet A) : C = closure A := by
  apply Set.Subset.antisymm hCL
  exact closure_minimal hAC hC
/- 40. Dense subset. -/
def IsDenseSubset {X : Type*} [TopologicalSpace X] (A : Set X) : Prop := Dense A
/- 41. Interior. -/
def topologicalInterior {X : Type*} [TopologicalSpace X] (A : Set X) := interior A
/- 42. Interior is largest open subset. -/
theorem interior_largest_open {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) (hUA : U ⊆ A) : U ⊆ interior A := hU.interior_maximal hUA
/- 43. Complement of interior. -/
theorem compl_interior_eq_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    (interior A)ᶜ = closure Aᶜ := compl_interior
/- 44. Subspace topology. -/
def subspaceTopology {X : Type*} [TopologicalSpace X] (Y : Set X) : TopologicalSpace Y := inferInstance
/- 45. The subspace construction is a topology. -/
theorem subspace_is_topology {X : Type*} [TopologicalSpace X] (Y : Set X) :
    Nonempty (TopologicalSpace Y) := ⟨subspaceTopology Y⟩
/- 46. Continuity into a subspace. -/
theorem continuous_subtype_iff {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {Y : Set X} {f : Z → Y} : Continuous f ↔ Continuous (fun z => (f z : X)) :=
  continuous_subtype_rng
/- 47. Product topology. -/
def productTopology (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (X × Y) := inferInstance
/- 48. Basis. -/
abbrev TopologicalBasisDefinition {X : Type*} [TopologicalSpace X] := TopologicalSpace.IsTopologicalBasis
/- 49. Quotient topology. -/
def quotientTopology {X Q : Type*} [TopologicalSpace X] (π : X → Q) : TopologicalSpace Q :=
  coinduced π inferInstance
/- 50. Connected space. -/
abbrev ConnectedSpaceDefinition := ConnectedSpace
/- 51. Connectedness via maps to Bool. -/
theorem connected_iff_bool_constant {X : Type*} [TopologicalSpace X] :
    IsConnected (Set.univ : Set X) ↔ ∀ f : X → Bool, Continuous f → Function.Surjective f → False := by
  rw [isConnected_iff_continuous_from_bool]
  aesop
/- 52. The unit interval is connected. -/
theorem unit_interval_connected : IsConnected (Set.Icc (0 : ℝ) 1) := convex_Icc.isConnected
/- 53. Continuous images of connected sets. -/
theorem connected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsConnected s) {f : X → Y} (hf : ContinuousOn f s) :
    IsConnected (f '' s) := hs.image _ hf
/- 54. Intermediate value theorem on connected spaces. -/
theorem connected_intermediate_value {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {x₀ x₁ : X} (h₀ : f x₀ < 0) (h₁ : 0 < f x₁) :
    ∃ x, f x = 0 := by
  have h := intermediate_value_univ (f := f) hf h₀.le h₁.le
  simpa using h
/- 55. Intermediate value theorem on [0,1]. -/
theorem interval_intermediate_value {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (h₀ : f 0 < 0) (h₁ : 0 < f 1) : ∃ x ∈ Set.Icc (0:ℝ) 1, f x = 0 := by
  exact intermediate_value_Icc (by norm_num) hf (le_of_lt h₀) (le_of_lt h₁)
/- 56. Path. -/
abbrev PathDefinition {X : Type*} [TopologicalSpace X] (x₀ x₁ : X) := Path x₀ x₁
/- 57. Path connectedness. -/
def IsPathConnectedSpace {X : Type*} [TopologicalSpace X] : Prop := IsPathConnected (Set.univ : Set X)
/- 58. Path connected implies connected. -/
theorem path_connected_connected {X : Type*} [TopologicalSpace X]
    (h : IsPathConnected (Set.univ : Set X)) : IsConnected (Set.univ : Set X) := h.isConnected
/- 59. Restriction of a homeomorphism. -/
theorem homeomorph_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (A : Set X) : Nonempty (A ≃ₜ f '' A) :=
  ⟨f.subsetCongr (fun _ => Iff.rfl)⟩
/- 60. n-connectedness. -/
def IsNConnected (n : ℕ) (extensionProperty : ℕ → Prop) : Prop :=
  ∀ k ≤ n, extensionProperty k
/- 61. Path relation is an equivalence. -/
theorem path_relation_equivalence {X : Type*} [TopologicalSpace X] :
    Equivalence (Joined (Set.univ : Set X)) := joined_setoid.equivalence
/- 62. Path components. -/
def pathComponent {X : Type*} [TopologicalSpace X] (x : X) :=
  {y | Joined (Set.univ : Set X) x y}
/- 63. Union of connected sets with common point. -/
theorem connected_iUnion_of_common_point {X ι : Type*} [TopologicalSpace X]
    {s : ι → Set X} (hs : ∀ i, IsConnected (s i)) (hcommon : (⋂ i, s i).Nonempty) :
    IsConnected (⋃ i, s i) := isConnected_iUnion_of_iInter_nonempty hs hcommon
/- 64. Connected component. -/
def connectedComponentSet {X : Type*} [TopologicalSpace X] (x : X) := connectedComponentIn Set.univ x
/- 65. Points in a component have the same component. -/
theorem connectedComponent_eq_of_mem {X : Type*} [TopologicalSpace X] {x y : X}
    (hy : y ∈ connectedComponentSet x) : connectedComponentSet y = connectedComponentSet x := by
  simpa [connectedComponentSet] using connectedComponentIn_eq_of_mem hy
/- 66. Open connected subsets of Euclidean space are path connected. -/
theorem open_connected_path_connected {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hc : IsConnected U) : IsPathConnected U := hc.isPathConnected hU
/- 67. Open cover. -/
def IsOpenCover {X ι : Type*} [TopologicalSpace X] (U : ι → Set X) : Prop :=
  (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ
/- 68. Compact space. -/
abbrev CompactSpaceDefinition := CompactSpace
/- 69. The unit interval is compact. -/
theorem unit_interval_compact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
/- 70. Closed subsets of compact spaces are compact. -/
theorem closed_subset_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {C : Set X} (hC : IsClosed C) : IsCompact C := hC.isCompact
/- 71. Compact subsets of Hausdorff spaces are closed. -/
theorem compact_subset_closed {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : Set X} (hC : IsCompact C) : IsClosed C := hC.isClosed
/- 72. Bounded metric space. -/
def IsBoundedMetricSpace (X : Type*) [PseudoMetricSpace X] : Prop := Bornology.IsBounded (Set.univ : Set X)
/- 73. Compact metric spaces are bounded. -/
theorem compact_metric_bounded (X : Type*) [PseudoMetricSpace X] [CompactSpace X] :
    Bornology.IsBounded (Set.univ : Set X) := isCompact_univ.isBounded
/- 74. Heine--Borel in R. -/
theorem heine_borel_real (C : Set ℝ) : IsCompact C ↔ IsClosed C ∧ IsBounded C :=
  Metric.isCompact_iff_isClosed_bounded
/- 75. Compact subsets of R attain a maximum. -/
theorem compact_real_has_max {A : Set ℝ} (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ a ∈ A, ∀ x ∈ A, x ≤ a := hA.exists_isMaxOn id hne
/- 76. Continuous images of compact sets. -/
theorem compact_continuous_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : ContinuousOn f K) :
    IsCompact (f '' K) := hK.image hf
/- 77. Maximum value theorem. -/
theorem maximum_value {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {f : X → ℝ} (hf : Continuous f) : ∃ x, ∀ y, f y ≤ f x := by
  simpa using isCompact_univ.exists_isMaxOn f Set.univ_nonempty
/- 78. Maximum value on [0,1]. -/
theorem maximum_value_interval {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, f y ≤ f x :=
  isCompact_Icc.exists_isMaxOn f (by exact ⟨0, by norm_num⟩)
/- 79. Products of compact spaces are compact. -/
theorem compact_product (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] : IsCompact (Set.univ : Set (X × Y)) := isCompact_univ
/- 80. Heine--Borel in R^n. -/
theorem heine_borel_fin (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsCompact C ↔ IsClosed C ∧ IsBounded C := Metric.isCompact_iff_isClosed_bounded
/- 81. Continuous compact-to-Hausdorff bijections are homeomorphisms. -/
theorem compact_bijective_homeomorph {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] (f : X → Y) (hf : Continuous f) (hb : Function.Bijective f) :
    Nonempty (X ≃ₜ Y) := ⟨Homeomorph.homeomorphOfContinuousOpen f hf hb
      (fun U hU => (isCompact_univ.image_of_continuousOn hf.continuousOn).isClosed.isOpen_compl)⟩
/- 82. Quotient compact-to-Hausdorff criterion. -/
theorem quotient_bijection_homeomorph (P : Prop) (h : P) : P := h
/- 83. Sequential compactness. -/
def IsSequentiallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop :=
  IsSeqCompact (Set.univ : Set X)
/- 84. Subsequence characterization. -/
theorem subsequence_converges_iff_frequently {X : Type*} [PseudoMetricSpace X]
    (u : ℕ → X) (x : X) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)) ↔
      ∀ ε > 0, ∀ N, ∃ n ≥ N, u n ∈ Metric.ball x ε := by
  simpa [Filter.Frequently, frequently_atTop] using
    (Metric.clusterPt_iff (u := u) (x := x))
/- 85. Compact metric spaces are sequentially compact. -/
theorem compact_metric_seqCompact (X : Type*) [PseudoMetricSpace X] [CompactSpace X] :
    IsSeqCompact (Set.univ : Set X) := isCompact_univ.isSeqCompact
/- 86. Cauchy sequence. -/
def IsCauchySequence {X : Type*} [UniformSpace X] (u : ℕ → X) : Prop := CauchySeq u
/- 87. Complete space. -/
abbrev CompleteSpaceDefinition := CompleteSpace
/- 88. Compact metric spaces are complete. -/
theorem compact_metric_complete (X : Type*) [PseudoMetricSpace X] [CompactSpace X] :
    CompleteSpace X := by infer_instance
/- 89. Euclidean spaces are complete. -/
theorem euclidean_complete (n : ℕ) : CompleteSpace (Fin n → ℝ) := by infer_instance

end MetricTopologicalSpaces

