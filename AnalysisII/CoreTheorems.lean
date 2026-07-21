import Mathlib

open Filter Function Set Topology
open scoped Topology

namespace AnalysisII

/-! ## Uniform convergence -/

/-- Analysis II, source theorem 1: uniform convergence implies the uniform Cauchy property. -/
theorem source001_uniformCauchySeqOn_of_tendstoUniformly
    {α β : Type*} [UniformSpace β] {F : ℕ → α → β} {f : α → β}
    (hF : TendstoUniformly F f atTop) : UniformCauchySeqOn F atTop univ :=
  hF.tendstoUniformlyOn.uniformCauchySeqOn

/-- Analysis II, source theorem 1, reverse direction once the pointwise limit is fixed. -/
theorem source001_tendstoUniformly_of_uniformCauchySeqOn
    {α β : Type*} [UniformSpace β] {F : ℕ → α → β} {f : α → β}
    (hF : UniformCauchySeqOn F atTop univ)
    (hpoint : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  tendstoUniformlyOn_univ.mp <|
    hF.tendstoUniformlyOn_of_tendsto fun x _ => hpoint x

/-- Analysis II, source theorem 2: the uniform limit of continuous functions is continuous. -/
theorem source002_uniform_limit_continuous
    {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {f : α → β}
    (hF : TendstoUniformly F f atTop) (hcont : ∀ n, Continuous (F n)) :
    Continuous f :=
  hF.continuous (Filter.Eventually.of_forall hcont)

/-- Analysis II, source theorem 10/49: Heine--Cantor on a compact set. -/
theorem source010_heineCantor
    {α β : Type*} [UniformSpace α] [UniformSpace β]
    {s : Set α} {f : α → β} (hs : IsCompact s) (hf : ContinuousOn f s) :
    UniformContinuousOn f s :=
  hs.uniformContinuousOn_of_continuous hf

/-! ## Metric and topological results -/

/-- Analysis II, source theorem 28: metric balls are open. -/
theorem source028_metric_ball_open {α : Type*} [PseudoMetricSpace α] (x : α) (r : ℝ) :
    IsOpen (Metric.ball x r) :=
  Metric.isOpen_ball

/-- Analysis II, source theorem 39: uniqueness of limits in a metric (indeed Hausdorff) space. -/
theorem source039_limit_unique
    {α : Type*} [TopologicalSpace α] [T2Space α] {u : ℕ → α} {x y : α}
    (hx : Tendsto u atTop (𝓝 x)) (hy : Tendsto u atTop (𝓝 y)) : x = y :=
  tendsto_nhds_unique hx hy

/-- Analysis II, source theorem 41(i): arbitrary unions of open sets are open. -/
theorem source041_iUnion_open
    {α ι : Type*} [TopologicalSpace α] (s : ι → Set α) (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

/-- Analysis II, source theorem 41(ii): finite intersections, in the binary case. -/
theorem source041_inter_open
    {α : Type*} [TopologicalSpace α] {s t : Set α} (hs : IsOpen s) (ht : IsOpen t) :
    IsOpen (s ∩ t) :=
  hs.inter ht

/-- Analysis II, source theorem 43(i): arbitrary intersections of closed sets are closed. -/
theorem source043_iInter_closed
    {α ι : Type*} [TopologicalSpace α] (s : ι → Set α) (hs : ∀ i, IsClosed (s i)) :
    IsClosed (⋂ i, s i) :=
  isClosed_iInter hs

/-- Analysis II, source theorem 43(ii): finite unions, in the binary case. -/
theorem source043_union_closed
    {α : Type*} [TopologicalSpace α] {s t : Set α} (hs : IsClosed s) (ht : IsClosed t) :
    IsClosed (s ∪ t) :=
  hs.union ht

/-- Analysis II, source theorem 44: finite subsets of a T₁ space are closed. -/
theorem source044_finite_closed
    {α : Type*} [TopologicalSpace α] [T1Space α] {s : Set α} (hs : s.Finite) :
    IsClosed s :=
  hs.isClosed

/-! ## Contractions -/

/-- Analysis II, source theorem 52: Banach's contraction mapping theorem. -/
theorem source052_contraction_unique_fixedPoint
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {K : ℝ≥0} {f : α → α} (hf : ContractingWith K f) :
    ∃! x, IsFixedPt f x := by
  refine ⟨ContractingWith.fixedPoint f hf, hf.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hf.fixedPoint_unique hy

/-- Analysis II, source theorem 52, contracting-iterate extension. -/
theorem source052_fixedPoint_of_contracting_iterate
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {K : ℝ≥0} {f : α → α} {n : ℕ} (hf : ContractingWith K (f^[n])) :
    IsFixedPt f (ContractingWith.fixedPoint (f^[n]) hf) :=
  hf.isFixedPt_fixedPoint_iterate

/-! ## Fréchet differentiation -/

/-- Analysis II, source theorem 54: uniqueness of the Fréchet derivative. -/
theorem source054_fderiv_unique
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' f'' : E →L[𝕜] F} {x : E}
    (hf' : HasFDerivAt f f' x) (hf'' : HasFDerivAt f f'' x) : f' = f'' :=
  hf'.unique hf''

/-- Analysis II, source theorem 55(i): differentiability implies continuity. -/
theorem source055_fderiv_continuous
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {x : E} (hf : HasFDerivAt f f' x) :
    ContinuousAt f x :=
  hf.continuousAt

/-- Analysis II, source theorem 55(iv): a continuous linear map is its own derivative. -/
theorem source055_continuousLinearMap_derivative
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) (x : E) : HasFDerivAt A A x :=
  A.hasFDerivAt

/-- Analysis II, source theorem 57(iv): the defining operator-norm estimate. -/
theorem source057_apply_le_opNorm
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) (x : E) : ‖A x‖ ≤ ‖A‖ * ‖x‖ :=
  A.le_opNorm x

/-- Analysis II, source theorem 59: the Fréchet chain rule. -/
theorem source059_chain_rule
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {g : F → G} {f' : E →L[𝕜] F} {g' : F →L[𝕜] G} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' (f x)) :
    HasFDerivAt (g ∘ f) (g'.comp f') x :=
  hg.comp x hf

end AnalysisII
