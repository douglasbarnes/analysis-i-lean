import Mathlib
import AnalysisII.NormedMetricCore
import AnalysisII.CoreTheorems

open Filter Function Set Topology
open scoped Topology

namespace AnalysisII

noncomputable section

/-- Analysis II source 32(i): compact subsets of a metric space are closed and bounded. -/
theorem source032_compact_closed_bounded
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K) :
    IsClosed K ∧ Bornology.IsBounded K :=
  ⟨hK.isClosed, hK.isBounded⟩

/-- Analysis II source 32(ii): Heine--Borel in finite-dimensional Euclidean space. -/
theorem source032_euclidean_closed_bounded_compact
    {n : ℕ} {K : Set (Fin n → ℝ)} (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) : IsCompact K :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩

/-- Analysis II source 34(i): continuous images of compact sets are compact. -/
theorem source034_compact_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K) :
    IsCompact (f '' K) :=
  hK.image_of_continuousOn hf

/-- Analysis II source 34(ii): continuous images of compact sets in a metric space
are closed and bounded. -/
theorem source034_image_closed_bounded
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {K : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K) :
    IsClosed (f '' K) ∧ Bornology.IsBounded (f '' K) := by
  have h := hK.image_of_continuousOn hf
  exact ⟨h.isClosed, h.isBounded⟩

/-- Analysis II source 34(iii): the extreme value theorem. -/
theorem source034_extreme_value
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (hne : K.Nonempty) {f : X → ℝ} (hf : ContinuousOn f K) :
    (∃ x ∈ K, IsMinOn f K x) ∧ (∃ x ∈ K, IsMaxOn f K x) :=
  ⟨hK.exists_isMinOn hne hf, hK.exists_isMaxOn hne hf⟩

/-- Analysis II source 35: the Euclidean unit sphere is compact.  Under a chosen
basis, the coordinate Euclidean norm identifies the lecture's sphere with this one. -/
theorem source035_euclidean_unit_sphere_compact (n : ℕ) :
    IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) :=
  isCompact_sphere _ _

/-- Analysis II source 37(ii): compactness is equivalent to closedness and boundedness
in a finite-dimensional real normed space. -/
theorem source037_finiteDimensional_compact_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K :=
  Metric.isCompact_iff_isClosed_bounded

/-- Analysis II source 38: finite-dimensional normed spaces over a complete field
are complete. -/
theorem source038_finiteDimensional_complete
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

/-- Analysis II source 42: a set is closed iff its complement is open. -/
theorem source042_closed_iff_complement_open
    {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsClosed s ↔ IsOpen sᶜ :=
  Iff.rfl

/-- Analysis II source 45(i): convergent metric-space sequences are Cauchy. -/
theorem source045_convergent_is_cauchy
    {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} {x : X}
    (hu : Tendsto u atTop (𝓝 x)) : CauchySeq u :=
  source023_convergent_is_cauchy hu

/-- Analysis II source 45(ii): a Cauchy sequence with a convergent subsequence
converges to the same limit. -/
theorem source045_cauchy_subsequence_limit
    {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} {x : X}
    (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsub : Tendsto (u ∘ φ) atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) :=
  source025_cauchy_subsequence_limit hu hφ hsub

/-- Analysis II source 46(i): a complete subset of a metric space is closed. -/
theorem source046_complete_set_closed
    {X : Type*} [PseudoMetricSpace X] {s : Set X} (hs : IsComplete s) : IsClosed s :=
  hs.isClosed

/-- Analysis II source 46(ii): a closed subset of a complete metric space is complete. -/
theorem source046_closed_set_complete
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {s : Set X} (hs : IsClosed s) : IsComplete s :=
  hs.isComplete

/-- Analysis II source 47: compact metric spaces are complete and bounded. -/
theorem source047_compact_complete_bounded
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K) :
    IsComplete K ∧ Bornology.IsBounded K :=
  ⟨hK.isComplete, hK.isBounded⟩

/-- Analysis II source 48: compactness of a metric-space subset is equivalent to
completeness and total boundedness. -/
theorem source048_compact_iff_complete_totallyBounded
    {X : Type*} [PseudoMetricSpace X] {K : Set X} :
    IsCompact K ↔ IsComplete K ∧ TotallyBounded K := by
  simpa [and_comm] using (isCompact_iff_totallyBounded_isComplete :
    IsCompact K ↔ TotallyBounded K ∧ IsComplete K)

/-- Analysis II source 51: a map whose preimages of open sets are open is continuous. -/
theorem source051_continuous_of_open_preimages
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (h : ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U)) : Continuous f :=
  continuous_def.mpr h

/-- Analysis II source 52, contracting-iterate extension, including uniqueness
of the fixed point of the original map. -/
theorem source052_contracting_iterate_unique_fixedPoint
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} {n : ℕ} (hf : ContractingWith K (f^[n])) :
    ∃! x, IsFixedPt f x := by
  let x := ContractingWith.fixedPoint (f^[n]) hf
  refine ⟨x, hf.isFixedPt_fixedPoint_iterate, ?_⟩
  intro y hy
  apply hf.fixedPoint_unique
  exact hy.iterate n

end

end AnalysisII
