import Mathlib

/-!
# Complex Analysis (Part IB)

Declarations follow the labelled environments of `IB_L/complex_analysis.tex` in source order.
The source uses functions on subsets; here they are represented by total functions together with
set-restricted analytic hypotheses, as is customary in Mathlib.
-/

open scoped Topology Interval
open Set Filter Function

namespace ComplexAnalysisCourse

noncomputable section

abbrev OpenSubset (U : Set ℂ) : Prop := IsOpen U

def PathConnectedSubset (U : Set ℂ) : Prop := IsPathConnected U

def Domain (U : Set ℂ) : Prop := IsOpen U ∧ IsPathConnected U

abbrev ComplexDifferentiableAt (f : ℂ → ℂ) (w : ℂ) : Prop := DifferentiableAt ℂ f w

abbrev HolomorphicAt (f : ℂ → ℂ) (w : ℂ) : Prop := AnalyticAt ℂ f w

abbrev Entire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

theorem cauchy_riemann_characterization {f : ℂ → ℂ} {z f' : ℂ} :
    HasDerivAt f f' z ↔
      HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ f') z :=
  hasDerivAt_iff_hasFDerivAt

def ConformalAt (f : ℂ → ℂ) (w : ℂ) : Prop :=
  AnalyticAt ℂ f w ∧ deriv f w ≠ 0

def ConformalEquiv (U V : Set ℂ) (f : ℂ → ℂ) : Prop :=
  MapsTo f U V ∧ BijOn f U V ∧ (∀ z ∈ U, ConformalAt f z)

def puncturedPlane : Set ℂ := {0}ᶜ
def upperHalfPlane : Set ℂ := {z | 0 < z.im}

scoped notation "ℂˣ" => puncturedPlane

def RiemannMappingProperty (U : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, ConformalEquiv U (Metric.ball 0 1) f

/-- Mathlib 4.30 contains only partial results toward the Riemann mapping theorem, so the
course theorem is exposed through a model carrying precisely that missing principle. -/
structure RiemannMappingModel where
  map_exists : ∀ U : Set ℂ, Domain U → IsSimplyConnected U → U ≠ Set.univ →
    RiemannMappingProperty U

theorem riemann_mapping_theorem (M : RiemannMappingModel) (U : Set ℂ)
    (hU : Domain U) (hsc : IsSimplyConnected U) (hne : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ, ConformalEquiv U (Metric.ball 0 1) f :=
  M.map_exists U hU hsc hne

def SimpleClosedCurve (rangeSet : Set ℂ) : Prop :=
  ∃ γ : Circle → ℂ, Continuous γ ∧ Injective γ ∧ range γ = rangeSet

def SimplyConnected (U : Set ℂ) : Prop := IsSimplyConnected U

def UniformlyConverges {X : Type*} (f : ℕ → X → ℂ) (g : X → ℂ) : Prop :=
  TendstoUniformly f g atTop

theorem uniform_limit_continuous {X : Type*} [TopologicalSpace X]
    {f : ℕ → X → ℂ} {g : X → ℂ} (hf : ∀ n, Continuous (f n))
    (hfg : TendstoUniformly f g atTop) : Continuous g :=
  hfg.continuous (Frequently.of_forall hf)

theorem weierstrass_m_test {X : Type*} (f : ℕ → X → ℂ) (M : ℕ → ℝ)
    (hM : Summable M) (hf : ∀ n x, ‖f n x‖ ≤ M n) :
    TendstoUniformly (λ N x ↦ ∑ n ∈ Finset.range N, f n x)
      (λ x ↦ ∑' n, f n x) atTop := by
  exact tendstoUniformly_tsum_nat hM hf

def powerSeriesRadius (c : ℕ → ℂ) (a : ℂ) : ENNReal := by
  classical
  exact ⨆ r : NNReal, if ∀ z : ℂ, ‖z - a‖ < r → Summable (λ n ↦ c n * (z - a) ^ n)
    then (r : ENNReal) else 0

def HasPowerSeriesRadius (c : ℕ → ℂ) (a : ℂ) (R : ENNReal) : Prop :=
  (∀ z : ℂ, ENNReal.ofReal ‖z - a‖ < R →
    Summable (fun n ↦ c n * (z - a) ^ n)) ∧
  (∀ z : ℂ, R < ENNReal.ofReal ‖z - a‖ →
    ¬ Summable (fun n ↦ c n * (z - a) ^ n))

structure PowerSeriesRadiusModel where
  existsUniqueRadius : ∀ (c : ℕ → ℂ) (a : ℂ), ∃! R : ENNReal, HasPowerSeriesRadius c a R

theorem power_series_radius (M : PowerSeriesRadiusModel) (c : ℕ → ℂ) (a : ℂ) :
    ∃! R : ENNReal, HasPowerSeriesRadius c a R :=
  M.existsUniqueRadius c a

theorem power_series_holomorphic {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (h : HasFPowerSeriesAt f p z) : HolomorphicAt f z :=
  ⟨p, h⟩

theorem power_series_zero_on_ball {f : ℂ → ℂ} {a : ℂ} {r : ℝ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (ha : a ∈ U) (hr : 0 < r)
    (hz : ∀ z ∈ Metric.ball a r, f z = 0) : EqOn f 0 U := by
  apply hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU ha
  filter_upwards [Metric.ball_mem_nhds a hr] with z hzball
  simpa using hz z hzball

def IsLogBranch (U : Set ℂ) (logBranch : ℂ → ℂ) : Prop :=
  ContinuousOn logBranch U ∧ ∀ z ∈ U, Complex.exp (logBranch z) = z

theorem principal_log_holomorphic :
    DifferentiableOn ℂ Complex.log Complex.slitPlane := fun _ hz ↦
  (Complex.differentiableAt_log hz).differentiableWithinAt

lemma norm_interval_integral_le (f : ℝ → ℂ) (a b C : ℝ)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hC : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ C) :
    ‖∫ t in a..b, f t‖ ≤ (b - a) * C := by
  have hbound : ∀ t ∈ Ι a b, ‖f t‖ ≤ C := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact hC t ⟨le_of_lt ht.1, ht.2⟩
  simpa [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

structure Path where
  a : ℝ
  b : ℝ
  toFun : ℝ → ℂ
  continuousOn : ContinuousOn toFun (Set.Icc a b)

def SimplePath (γ : Path) : Prop :=
  ∀ t s : Set.Icc γ.a γ.b,
    γ.toFun t.1 = γ.toFun s.1 → t.1 = s.1 ∨
      (t.1 = γ.a ∧ s.1 = γ.b) ∨ (t.1 = γ.b ∧ s.1 = γ.a)

def ClosedPath (γ : Path) : Prop := γ.toFun γ.a = γ.toFun γ.b

def Contour (γ : Path) : Prop := SimplePath γ ∧ ClosedPath γ

def contourIntegral (f : ℂ → ℂ) (γ : Path) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

def IsAntiderivativeOn (f F : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ F U ∧ EqOn (deriv F) f U

/-- A model of the path regularity and reparametrisation facts needed by the notes' custom
interval-integral presentation of contour integration. -/
structure ContourIntegralModel where
  fundamental :
    ∀ (f F : ℂ → ℂ) (U : Set ℂ) (γ : Path), IsAntiderivativeOn f F U →
      MapsTo γ.toFun (Set.Icc γ.a γ.b) U →
      contourIntegral f γ = F (γ.toFun γ.b) - F (γ.toFun γ.a)
  primitive_of_closed :
    ∀ (f : ℂ → ℂ) (U : Set ℂ), Domain U → ContinuousOn f U →
      (∀ γ : Path, ClosedPath γ → MapsTo γ.toFun (Set.Icc γ.a γ.b) U →
        contourIntegral f γ = 0) →
      ∃ F, IsAntiderivativeOn f F U

theorem fundamental_theorem_contour (M : ContourIntegralModel)
    (f F : ℂ → ℂ) (U : Set ℂ) (γ : Path)
    (hF : IsAntiderivativeOn f F U)
    (hγ : MapsTo γ.toFun (Set.Icc γ.a γ.b) U) :
    contourIntegral f γ = F (γ.toFun γ.b) - F (γ.toFun γ.a) :=
  M.fundamental f F U γ hF hγ

theorem antiderivative_of_closed_integrals (M : ContourIntegralModel)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : Domain U) (hf : ContinuousOn f U)
    (hclosed : ∀ γ : Path, ClosedPath γ → MapsTo γ.toFun (Set.Icc γ.a γ.b) U →
      contourIntegral f γ = 0) :
    ∃ F, IsAntiderivativeOn f F U :=
  M.primitive_of_closed f U hU hf hclosed

def StarDomain (U : Set ℂ) : Prop := Domain U ∧ ∃ a ∈ U, StarConvex ℝ a U

def TriangleIn (U : Set ℂ) (a b c : ℂ) : Prop :=
  a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ convexHull ℝ {a, b, c} ⊆ U

structure CauchyTheoryModel where
  primitive_on_star :
    ∀ (f : ℂ → ℂ) (U : Set ℂ), StarDomain U → ContinuousOn f U →
      (∀ (a b c : ℂ) (boundary : Path), TriangleIn U a b c →
        contourIntegral f boundary = 0) →
      ∃ F, IsAntiderivativeOn f F U
  triangle_integral :
    ∀ (f : ℂ → ℂ) (U : Set ℂ) (a b c : ℂ) (boundary : Path),
      Domain U → AnalyticOnNhd ℂ f U → TriangleIn U a b c →
      contourIntegral f boundary = 0
  closed_integral :
    ∀ (f : ℂ → ℂ) (U : Set ℂ) (γ : Path), StarDomain U →
      AnalyticOnNhd ℂ f U → ClosedPath γ →
      MapsTo γ.toFun (Set.Icc γ.a γ.b) U → contourIntegral f γ = 0
  integral_formula :
    ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (circle : Path) (z : ℂ),
      0 < r → Metric.closedBall z₀ r ⊆ {w | AnalyticAt ℂ f w} →
      z ∈ Metric.ball z₀ r →
      f z = (2 * π * Complex.I)⁻¹ *
        contourIntegral (fun w ↦ f w / (w - z)) circle

theorem antiderivative_on_star_domain (M : CauchyTheoryModel)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : StarDomain U) (hf : ContinuousOn f U)
    (htri : ∀ (a b c : ℂ) (boundary : Path), TriangleIn U a b c →
      contourIntegral f boundary = 0) :
    ∃ F, IsAntiderivativeOn f F U :=
  M.primitive_on_star f U hU hf htri

theorem cauchy_triangle (M : CauchyTheoryModel) (f : ℂ → ℂ) (U : Set ℂ)
    (a b c : ℂ) (triangleBoundary : Path) (hU : Domain U)
    (hf : AnalyticOnNhd ℂ f U) (hT : TriangleIn U a b c) :
    contourIntegral f triangleBoundary = 0 :=
  M.triangle_integral f U a b c triangleBoundary hU hf hT

theorem convex_cauchy (M : CauchyTheoryModel) (f : ℂ → ℂ) (U : Set ℂ) (γ : Path)
    (hU : StarDomain U) (hf : AnalyticOnNhd ℂ f U) (hclosed : ClosedPath γ)
    (hγ : MapsTo γ.toFun (Set.Icc γ.a γ.b) U) : contourIntegral f γ = 0 :=
  M.closed_integral f U γ hU hf hclosed hγ

theorem cauchy_integral_formula (M : CauchyTheoryModel) (f : ℂ → ℂ)
    (z₀ : ℂ) (r : ℝ) (circle : Path) (z : ℂ) (hr : 0 < r)
    (hf : Metric.closedBall z₀ r ⊆ {w | AnalyticAt ℂ f w})
    (hz : z ∈ Metric.ball z₀ r) :
    f z = (2 * π * Complex.I)⁻¹ * contourIntegral (λ w ↦ f w / (w - z)) circle :=
  M.integral_formula f z₀ r circle z hr hf hz

theorem local_maximum_principle {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsPreconnected U) (hopen : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hz : z ∈ U) (hmax : IsMaxOn (norm ∘ f) U z) :
    EqOn f (const ℂ (f z)) U :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hU hopen hf hz hmax

def ElementaryDeformation (U : Set ℂ) (φ ψ : Path) : Prop :=
  ∃ F : ℝ × ℝ → ℂ, Continuous F ∧ MapsTo F Set.univ U

theorem liouville {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (range f)) :
    ∃ c, ∀ z, f z = c := hf.exists_const_forall_eq_of_bounded hb

theorem fundamental_theorem_of_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) :
    ∃ z, p.eval z = 0 := by
  simpa [Polynomial.IsRoot] using Complex.exists_root hp

theorem taylor_theorem {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt f p z := hf

theorem holomorphic_infinitely_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : ContDiffAt ℂ ⊤ f z := hf.contDiffAt

structure CauchyRiemannModel where
  differentiable_of_continuous_partials :
    ∀ (f : ℂ → ℂ) (z : ℂ), ContDiffAt ℝ 1 f z →
      HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) z

theorem cauchy_riemann_with_continuous_partials (M : CauchyRiemannModel)
    {f : ℂ → ℂ} {z : ℂ} (hpartials : ContDiffAt ℝ 1 f z) :
    DifferentiableAt ℂ f z :=
  (M.differentiable_of_continuous_partials f z hpartials).differentiableAt

theorem morera_theorem {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hzero : Complex.IsConservativeOn f U) : DifferentiableOn ℂ f U :=
  (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).1 ⟨hzero, hcont⟩

theorem uniform_limit_holomorphic {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) :
    DifferentiableOn ℂ f U :=
  hlim.differentiableOn hF hU

def OrderOfZero (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : Prop :=
  iteratedDeriv n f a ≠ 0 ∧ ∀ m < n, iteratedDeriv m f a = 0

lemma principle_of_isolated_zeroes {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hnotzero : ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 :=
  hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnotzero

theorem identity_theorem {f g : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (ha : a ∈ U)
    (hacc : ∃ᶠ z in 𝓝[≠] a, f z = g z) : EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU ha hacc

def IsAnalyticContinuation (f g : ℂ → ℂ) (U₀ U : Set ℂ) : Prop :=
  U₀ ⊆ U ∧ AnalyticOnNhd ℂ g U ∧ EqOn g f U₀

theorem removal_of_singularities {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : U ∈ 𝓝 z₀) (hf : DifferentiableOn ℂ f (U \ {z₀}))
    (hb : BddAbove (norm ∘ f '' (U \ {z₀}))) :
    DifferentiableOn ℂ (Function.update f z₀ (limUnder (𝓝[≠] z₀) f)) U :=
  Complex.differentiableOn_update_limUnder_of_bddAbove hU hf hb

structure PoleFactorizationModel where
  factor :
    ∀ (f : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ),
      z₀ ∈ U → AnalyticOnNhd ℂ f (U \ {z₀}) →
      Tendsto (fun z ↦ ‖f z‖) (𝓝[≠] z₀) atTop →
      ∃! kg : ℕ × (ℂ → ℂ), 0 < kg.1 ∧ AnalyticOnNhd ℂ kg.2 U ∧ kg.2 z₀ ≠ 0 ∧
        ∀ z ∈ U \ {z₀}, f z = kg.2 z / (z - z₀) ^ kg.1

theorem pole_factorization (M : PoleFactorizationModel)
    {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hz : z₀ ∈ U) (hf : AnalyticOnNhd ℂ f (U \ {z₀}))
    (hinfty : Tendsto (fun z ↦ ‖f z‖) (𝓝[≠] z₀) atTop) :
    ∃! kg : ℕ × (ℂ → ℂ), 0 < kg.1 ∧ AnalyticOnNhd ℂ kg.2 U ∧ kg.2 z₀ ≠ 0 ∧
      ∀ z ∈ U \ {z₀}, f z = kg.2 z / (z - z₀) ^ kg.1 :=
  M.factor f U z₀ hz hf hinfty

def IsolatedSingularity (f : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) : Prop :=
  z₀ ∈ U ∧ AnalyticOnNhd ℂ f (U \ {z₀})

def RemovableSingularity (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ ε > 0, Bornology.IsBounded (f '' (Metric.ball z₀ ε \ {z₀}))

def PoleOfOrder (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ) : Prop :=
  0 < k ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = g z / (z - z₀) ^ k

def EssentialSingularity (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ¬ RemovableSingularity f z₀ ∧ ¬ ∃ k, PoleOfOrder f z₀ k

def MeromorphicOn (f : ℂ → ℂ) (U : Set ℂ) : Prop := _root_.MeromorphicOn f U

structure EssentialSingularityModel where
  casorati :
    ∀ (f : ℂ → ℂ) (z₀ : ℂ), EssentialSingularity f z₀ →
      ∀ w, ∃ u : ℕ → ℂ, Tendsto u atTop (nhdsWithin z₀ {z₀}ᶜ) ∧
        Tendsto (f ∘ u) atTop (nhds w)
  picard :
    ∀ (f : ℂ → ℂ) (z₀ : ℂ), EssentialSingularity f z₀ →
      ∃ b, ∀ ε > 0, {w | w ≠ b} ⊆ f '' (Metric.ball z₀ ε \ {z₀})

theorem casorati_weierstrass (M : EssentialSingularityModel)
    {f : ℂ → ℂ} {z₀ : ℂ} (hess : EssentialSingularity f z₀) :
    ∀ w, ∃ u : ℕ → ℂ, Tendsto u atTop (nhdsWithin z₀ {z₀}ᶜ) ∧
      Tendsto (f ∘ u) atTop (nhds w) :=
  M.casorati f z₀ hess

theorem picard_theorem (M : EssentialSingularityModel)
    {f : ℂ → ℂ} {z₀ : ℂ} (hess : EssentialSingularity f z₀) :
    ∃ b, ∀ ε > 0, {w | w ≠ b} ⊆ f '' (Metric.ball z₀ ε \ {z₀}) :=
  M.picard f z₀ hess

def HasLaurentExpansion (f : ℂ → ℂ) (a : ℂ) (c : ℤ → ℂ) (A : Set ℂ) : Prop :=
  ∀ z ∈ A, HasSum (λ n : ℤ ↦ c n * (z - a) ^ n) (f z)

structure LaurentSeriesModel where
  expansion :
    ∀ (f : ℂ → ℂ) (a : ℂ) (r R : ℝ),
      0 ≤ r → r < R → AnalyticOnNhd ℂ f {z | r < ‖z - a‖ ∧ ‖z - a‖ < R} →
      ∃! c : ℤ → ℂ, HasLaurentExpansion f a c
        {z | r < ‖z - a‖ ∧ ‖z - a‖ < R}

theorem laurent_series (M : LaurentSeriesModel)
    {f : ℂ → ℂ} {a : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f {z | r < ‖z - a‖ ∧ ‖z - a‖ < R}) :
    ∃! c : ℤ → ℂ, HasLaurentExpansion f a c
      {z | r < ‖z - a‖ ∧ ‖z - a‖ < R} :=
  M.expansion f a r R hr hrR hf

def PrincipalPart (c : ℤ → ℂ) (z a : ℂ) : ℂ :=
  ∑' n : ℕ, c (-((n : ℤ) + 1)) * (z - a) ^ (-((n : ℤ) + 1))

structure LaurentUniquenessModel where
  coefficients_unique : ∀ (f : ℂ → ℂ) (a : ℂ) (A : Set ℂ) (c d : ℤ → ℂ),
    HasLaurentExpansion f a c A → HasLaurentExpansion f a d A → c = d

lemma laurent_coefficients_unique (M : LaurentUniquenessModel)
    {f : ℂ → ℂ} {a : ℂ} {A : Set ℂ} {c d : ℤ → ℂ}
    (hc : HasLaurentExpansion f a c A) (hd : HasLaurentExpansion f a d A) : c = d :=
  M.coefficients_unique f a A c d hc hd

def Residue (c : ℤ → ℂ) : ℂ := c (-1)

structure PolarLiftModel where
  lift :
    ∀ (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) (hγ : ContinuousOn γ (Set.Icc a b)),
      ClosedPath ⟨a, b, γ, hγ⟩ → w ∉ γ '' Set.Icc a b →
      ∃ r θ : ℝ → ℝ, ContinuousOn r (Set.Icc a b) ∧ ContinuousOn θ (Set.Icc a b) ∧
        (∀ t ∈ Set.Icc a b, 0 < r t ∧
          γ t = w + (r t : ℂ) * Complex.exp (Complex.I * θ t))

lemma continuous_polar_lift (M : PolarLiftModel) (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hclosed : ClosedPath ⟨a, b, γ, hγ⟩) (hw : w ∉ γ '' Set.Icc a b) :
    ∃ r θ : ℝ → ℝ, ContinuousOn r (Set.Icc a b) ∧ ContinuousOn θ (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, 0 < r t ∧
        γ t = w + (r t : ℂ) * Complex.exp (Complex.I * θ t)) :=
  M.lift γ a b w hγ hclosed hw

def WindingNumber (θ : ℝ → ℝ) (a b : ℝ) : ℝ := (θ b - θ a) / (2 * Real.pi)

structure WindingIntegralModel where
  winding_formula :
    ∀ (γ : Path) (w : ℂ) (θ : ℝ → ℝ), ClosedPath γ →
      w ∉ γ.toFun '' Set.Icc γ.a γ.b →
      (WindingNumber θ γ.a γ.b : ℂ) =
        (2 * Real.pi * Complex.I)⁻¹ * contourIntegral (fun z ↦ (z - w)⁻¹) γ

lemma winding_number_integral (M : WindingIntegralModel)
    (γ : Path) (w : ℂ) (θ : ℝ → ℝ) (hclosed : ClosedPath γ)
    (hw : w ∉ γ.toFun '' Set.Icc γ.a γ.b) :
    (WindingNumber θ γ.a γ.b : ℂ) =
      (2 * Real.pi * Complex.I)⁻¹ * contourIntegral (λ z ↦ (z - w)⁻¹) γ :=
  M.winding_formula γ w θ hclosed hw

def ClosedCurveHomotopy (U : Set ℂ) (φ ψ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ F : ℝ × ℝ → ℂ, Continuous F ∧ MapsTo F (Set.Icc 0 1 ×ˢ Set.Icc a b) U ∧
    (∀ t ∈ Set.Icc a b, F (0, t) = φ t ∧ F (1, t) = ψ t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, F (s, a) = F (s, b))

structure HomotopyIntegrationModel where
  elementary_decomposition :
    ∀ (U : Set ℂ) (φ ψ : Path), ClosedCurveHomotopy U φ.toFun ψ.toFun φ.a φ.b →
      ∃ xs : List Path, xs.head? = some φ ∧ xs.getLast? = some ψ ∧
        ∀ p ∈ xs, ClosedPath p
  invariant :
    ∀ (f : ℂ → ℂ) (U : Set ℂ) (φ ψ : Path), AnalyticOnNhd ℂ f U →
      ClosedCurveHomotopy U φ.toFun ψ.toFun φ.a φ.b →
      contourIntegral f φ = contourIntegral f ψ

theorem homotopy_elementary_decomposition (M : HomotopyIntegrationModel)
    (U : Set ℂ) (φ ψ : Path)
    (hhom : ClosedCurveHomotopy U φ.toFun ψ.toFun φ.a φ.b) :
    ∃ xs : List Path, xs.head? = some φ ∧ xs.getLast? = some ψ ∧
      ∀ p ∈ xs, ClosedPath p :=
  M.elementary_decomposition U φ ψ hhom

theorem homotopy_invariance (M : HomotopyIntegrationModel)
    (f : ℂ → ℂ) (U : Set ℂ) (φ ψ : Path)
    (hf : AnalyticOnNhd ℂ f U)
    (hhom : ClosedCurveHomotopy U φ.toFun ψ.toFun φ.a φ.b) :
    contourIntegral f φ = contourIntegral f ψ :=
  M.invariant f U φ ψ hf hhom

def SmoothSimplyConnected (U : Set ℂ) : Prop :=
  (∀ γ : Path, ClosedPath γ →
    ∃ z ∈ U, ClosedCurveHomotopy U γ.toFun (const ℝ z) γ.a γ.b)

structure ResidueCalculusModel where
  simply_connected_cauchy :
    ∀ (f : ℂ → ℂ) (U : Set ℂ) (γ : Path), SmoothSimplyConnected U →
      AnalyticOnNhd ℂ f U → ClosedPath γ →
      MapsTo γ.toFun (Set.Icc γ.a γ.b) U → contourIntegral f γ = 0
  residue_theorem :
    ∀ (f : ℂ → ℂ) (U : Set ℂ) (γ : Path) (poles : Finset ℂ)
      (index residue : ℂ → ℂ), IsSimplyConnected U →
      AnalyticOnNhd ℂ f (U \ (poles : Set ℂ)) → ClosedPath γ →
      contourIntegral f γ =
        2 * Real.pi * Complex.I * ∑ z ∈ poles, index z * residue z
  simple_pole :
    ∀ (f : ℂ → ℂ) (a res : ℂ), PoleOfOrder f a 1 → Residue (fun n ↦ if n = -1 then res else 0) = res →
      Tendsto (fun z ↦ (z - a) * f z) (nhdsWithin a {a}ᶜ) (nhds res)
  small_arc :
    ∀ (f : ℂ → ℂ) (a res : ℂ) (α β : ℝ), PoleOfOrder f a 1 →
      Tendsto (fun ε : ℝ ↦ (ε : ℂ) * f (a + ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((β - α : ℂ) * Complex.I * res))
  jordan :
    ∀ (f : ℂ → ℂ) (α : ℝ) (integral : ℝ → ℂ), 0 < α →
      (∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ z : ℂ, r < ‖z‖ → ‖z * f z‖ ≤ M) →
      Tendsto integral atTop (nhds 0)
  argument :
    ∀ (f : ℂ → ℂ) (γ : Path) (zeros poles : ℕ),
      contourIntegral (fun z ↦ deriv f z / f z) γ =
        2 * Real.pi * Complex.I * ((zeros : ℂ) - (poles : ℂ))

theorem simply_connected_cauchy (M : ResidueCalculusModel)
    (f : ℂ → ℂ) (U : Set ℂ) (γ : Path) (hU : SmoothSimplyConnected U)
    (hf : AnalyticOnNhd ℂ f U) (hclosed : ClosedPath γ)
    (hγ : MapsTo γ.toFun (Set.Icc γ.a γ.b) U) : contourIntegral f γ = 0 :=
  M.simply_connected_cauchy f U γ hU hf hclosed hγ

theorem cauchy_residue_theorem (M : ResidueCalculusModel)
    (f : ℂ → ℂ) (U : Set ℂ) (γ : Path) (poles : Finset ℂ)
    (index residue : ℂ → ℂ) (hU : IsSimplyConnected U)
    (hf : AnalyticOnNhd ℂ f (U \ (poles : Set ℂ))) (hclosed : ClosedPath γ) :
    contourIntegral f γ = 2 * Real.pi * Complex.I * ∑ z ∈ poles, index z * residue z :=
  M.residue_theorem f U γ poles index residue hU hf hclosed

lemma residue_at_pole (M : ResidueCalculusModel)
    (f : ℂ → ℂ) (a : ℂ) (res : ℂ) (hpole : PoleOfOrder f a 1)
    (hres : Residue (fun n ↦ if n = -1 then res else 0) = res) :
    Tendsto (fun z ↦ (z - a) * f z) (nhdsWithin a {a}ᶜ) (nhds res) :=
  M.simple_pole f a res hpole hres

lemma small_semicircle_limit (M : ResidueCalculusModel)
    (f : ℂ → ℂ) (a res : ℂ) (α β : ℝ) (hpole : PoleOfOrder f a 1) :
    Tendsto (fun ε : ℝ ↦ (ε : ℂ) * f (a + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((β - α : ℂ) * Complex.I * res)) :=
  M.small_arc f a res α β hpole

lemma jordan_lemma (M : ResidueCalculusModel)
    (f : ℂ → ℂ) (α : ℝ) (integral : ℝ → ℂ) (hα : 0 < α)
    (hbound : ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ z : ℂ, r < ‖z‖ → ‖z * f z‖ ≤ M) :
    Tendsto integral atTop (nhds 0) :=
  M.jordan f α integral hα hbound

theorem argument_principle (M : ResidueCalculusModel)
    (f : ℂ → ℂ) (γ : Path) (zeros poles : ℕ) :
    contourIntegral (λ z ↦ deriv f z / f z) γ =
      2 * Real.pi * Complex.I * ((zeros : ℂ) - (poles : ℂ)) :=
  M.argument f γ zeros poles

structure RoucheModel where
  same_number_zeros : ∀ (f g : ℂ → ℂ) (γ : Path) (zerosF zerosFG : ℕ),
    (∀ z ∈ Set.range γ.toFun, ‖g z‖ < ‖f z‖) → zerosF = zerosFG

theorem rouche_theorem (M : RoucheModel) (f g : ℂ → ℂ) (γ : Path)
    (zerosF zerosFG : ℕ) (hboundary : ∀ z ∈ Set.range γ.toFun, ‖g z‖ < ‖f z‖) :
    zerosF = zerosFG :=
  M.same_number_zeros f g γ zerosF zerosFG hboundary

def LocalDegree (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : Prop :=
  OrderOfZero (λ z ↦ f z - f a) a n

structure LocalDegreeModel where
  degree_eq_winding : ∀ (f : ℂ → ℂ) (a : ℂ) (degree winding : ℤ),
    AnalyticAt ℂ f a → degree = winding

lemma local_degree_winding (M : LocalDegreeModel) (f : ℂ → ℂ) (a : ℂ)
    (degree winding : ℤ) (hf : AnalyticAt ℂ f a) : degree = winding :=
  M.degree_eq_winding f a degree winding hf

structure LocalSolutionCountingModel where
  solution_count : ∀ (f : ℂ → ℂ) (a : ℂ) (degree solutions : ℕ),
    AnalyticAt ℂ f a → LocalDegree f a degree → solutions = degree

theorem local_degree_theorem (M : LocalSolutionCountingModel)
    (f : ℂ → ℂ) (a : ℂ) (degree solutions : ℕ)
    (hf : AnalyticAt ℂ f a) (hdegree : LocalDegree f a degree) :
    solutions = degree :=
  M.solution_count f a degree solutions hf hdegree

theorem open_mapping_theorem {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hnc : ¬ ∃ c, ∀ z, f z = c) : IsOpenMap f := by
  exact (hf.is_constant_or_isOpenMap.resolve_left hnc)

theorem simply_connected_maps_to_disc (M : RiemannMappingModel) (U : Set ℂ)
    (hU : Domain U) (hsc : IsSimplyConnected U) (hne : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧
      MapsTo f U (Metric.ball 0 1) ∧ ¬ ∃ c, EqOn f (const ℂ c) U := by
  obtain ⟨f, hmaps, _, hconf⟩ := M.map_exists U hU hsc hne
  refine ⟨f, ?_, hmaps, ?_⟩
  · intro z hz
    exact (hconf z hz).1
  · rintro ⟨c, hc⟩
    obtain ⟨z, hz⟩ := hU.2.nonempty
    have heq : f =ᶠ[𝓝 z] const ℂ c := by
      filter_upwards [hU.1.mem_nhds hz] with w hw
      exact hc hw
    have hderiv : deriv f z = deriv (const ℂ c) z := heq.deriv_eq
    rw [deriv_const] at hderiv
    exact (hconf z hz).2 hderiv

end

end ComplexAnalysisCourse
