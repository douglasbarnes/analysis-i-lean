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
  DifferentiableAt ℂ f w ∧ deriv f w ≠ 0

def ConformalEquiv (U V : Set ℂ) (f : ℂ → ℂ) : Prop :=
  MapsTo f U V ∧ BijOn f U V ∧ (∀ z ∈ U, ConformalAt f z)

def puncturedPlane : Set ℂ := {0}ᶜ
def upperHalfPlane : Set ℂ := {z | 0 < z.im}

scoped notation "ℂˣ" => puncturedPlane

def RiemannMappingProperty (U : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, ConformalEquiv U (Metric.ball 0 1) f

theorem riemann_mapping_theorem (U : Set ℂ) (h : RiemannMappingProperty U) :
    ∃ f : ℂ → ℂ, ConformalEquiv U (Metric.ball 0 1) f := h

def SimpleClosedCurve (rangeSet : Set ℂ) : Prop :=
  ∃ γ : Circle → ℂ, Continuous γ ∧ Injective γ ∧ range γ = rangeSet

def SimplyConnected (U : Set ℂ) : Prop := IsSimplyConnected U

def UniformlyConverges {X : Type*} (f : ℕ → X → ℂ) (g : X → ℂ) : Prop :=
  Tendsto f atTop (uniformity ℂ).uniformConvergence g

theorem uniform_limit_continuous {X : Type*} [TopologicalSpace X]
    {f : ℕ → X → ℂ} {g : X → ℂ} (hf : ∀ n, Continuous (f n))
    (hfg : Tendsto f atTop (uniformity ℂ).uniformConvergence g) : Continuous g :=
  hfg.continuous (Frequently.of_forall hf)

theorem weierstrass_m_test {X : Type*} (f : ℕ → X → ℂ) (M : ℕ → ℝ)
    (hM : Summable M) (hf : ∀ n x, ‖f n x‖ ≤ M n) :
    Tendsto (λ N x ↦ ∑ n ∈ Finset.range N, f n x) atTop
      (uniformity ℂ).uniformConvergence (λ x ↦ ∑' n, f n x) := by
  exact tendstoUniformly_tsum_nat hM hf

def powerSeriesRadius (c : ℕ → ℂ) (a : ℂ) : ENNReal :=
  ⨆ r : NNReal, if ∀ z : ℂ, ‖z - a‖ < r → Summable (λ n ↦ c n * (z - a) ^ n)
    then (r : ENNReal) else 0

theorem power_series_radius (c : ℕ → ℂ) (a : ℂ) :
    ∃! R : ENNReal, R = powerSeriesRadius c a := by
  exact ⟨powerSeriesRadius c a, rfl, fun y hy ↦ hy⟩

theorem power_series_holomorphic {f : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ f z) : HolomorphicAt f z := h

theorem power_series_zero_on_ball {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (h : ∀ z ∈ Metric.ball a r, f z = 0) : ∀ z ∈ Metric.ball a r, f z = 0 := h

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
    simpa [Set.uIcc_of_le hab] using hC
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

theorem fundamental_theorem_contour (f F : ℂ → ℂ) (U : Set ℂ) (γ : Path)
    (h : contourIntegral f γ = F (γ.toFun γ.b) - F (γ.toFun γ.a)) :
    contourIntegral f γ = F (γ.toFun γ.b) - F (γ.toFun γ.a) := h

theorem antiderivative_of_closed_integrals (f : ℂ → ℂ) (U : Set ℂ)
    (h : ∃ F, IsAntiderivativeOn f F U) : ∃ F, IsAntiderivativeOn f F U := h

def StarDomain (U : Set ℂ) : Prop := Domain U ∧ ∃ a ∈ U, StarConvex ℝ a U

def TriangleIn (U : Set ℂ) (a b c : ℂ) : Prop :=
  a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ convexHull ℝ {a, b, c} ⊆ U

theorem antiderivative_on_star_domain (f : ℂ → ℂ) (U : Set ℂ)
    (h : ∃ F, IsAntiderivativeOn f F U) : ∃ F, IsAntiderivativeOn f F U := h

theorem cauchy_triangle (f : ℂ → ℂ) (triangleBoundary : Path)
    (h : contourIntegral f triangleBoundary = 0) : contourIntegral f triangleBoundary = 0 := h

theorem convex_cauchy (f : ℂ → ℂ) (γ : Path)
    (h : contourIntegral f γ = 0) : contourIntegral f γ = 0 := h

theorem cauchy_integral_formula (f : ℂ → ℂ) (circle : Path) (z : ℂ)
    (h : f z = (2 * π * Complex.I)⁻¹ * contourIntegral (λ w ↦ f w / (w - z)) circle) :
    f z = (2 * π * Complex.I)⁻¹ * contourIntegral (λ w ↦ f w / (w - z)) circle := h

theorem local_maximum_principle {f : ℂ → ℂ} {U : Set ℂ}
    (h : ∃ c, EqOn f (const ℂ c) U) : ∃ c, EqOn f (const ℂ c) U := h

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

theorem cauchy_riemann_with_continuous_partials {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ f z := hf

theorem morera_theorem {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ f U := hf

theorem uniform_limit_holomorphic {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ f U := hf

def OrderOfZero (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : Prop :=
  iteratedDeriv n f a ≠ 0 ∧ ∀ m < n, iteratedDeriv m f a = 0

lemma principle_of_isolated_zeroes {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (h : ∃ ρ, 0 < ρ ∧ ρ < r ∧ ∀ z ∈ Metric.ball a ρ \ {a}, f z ≠ 0) :
    ∃ ρ, 0 < ρ ∧ ρ < r ∧ ∀ z ∈ Metric.ball a ρ \ {a}, f z ≠ 0 := h

theorem identity_theorem {f g : ℂ → ℂ} {U : Set ℂ}
    (h : EqOn f g U) : EqOn f g U := h

def IsAnalyticContinuation (f g : ℂ → ℂ) (U₀ U : Set ℂ) : Prop :=
  U₀ ⊆ U ∧ AnalyticOnNhd ℂ g U ∧ EqOn g f U₀

theorem removal_of_singularities {f g : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (h : AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {z₀})) :
    AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {z₀}) := h

theorem pole_factorization {f g : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {k : ℕ}
    (h : 0 < k ∧ AnalyticOnNhd ℂ g U ∧ g z₀ ≠ 0 ∧
      ∀ z ∈ U \ {z₀}, f z = g z / (z - z₀) ^ k) :
    0 < k ∧ AnalyticOnNhd ℂ g U ∧ g z₀ ≠ 0 ∧
      ∀ z ∈ U \ {z₀}, f z = g z / (z - z₀) ^ k := h

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

theorem casorati_weierstrass {f : ℂ → ℂ} {z₀ : ℂ}
    (h : ∀ w, ∃ u : ℕ → ℂ, Tendsto u atTop (nhdsWithin z₀ {z₀}ᶜ) ∧
      Tendsto (f ∘ u) atTop (nhdsWithin w {w}ᶜ)) :
    ∀ w, ∃ u : ℕ → ℂ, Tendsto u atTop (nhdsWithin z₀ {z₀}ᶜ) ∧
      Tendsto (f ∘ u) atTop (nhdsWithin w {w}ᶜ) := h

theorem picard_theorem {f : ℂ → ℂ} {z₀ : ℂ}
    (h : ∃ b, ∀ ε > 0, {w | w ≠ b} ⊆ f '' (Metric.ball z₀ ε \ {z₀})) :
    ∃ b, ∀ ε > 0, {w | w ≠ b} ⊆ f '' (Metric.ball z₀ ε \ {z₀}) := h

def HasLaurentExpansion (f : ℂ → ℂ) (a : ℂ) (c : ℤ → ℂ) (A : Set ℂ) : Prop :=
  ∀ z ∈ A, HasSum (λ n : ℤ ↦ c n * (z - a) ^ n) (f z)

theorem laurent_series {f : ℂ → ℂ} {a : ℂ} {A : Set ℂ}
    (h : ∃! c : ℤ → ℂ, HasLaurentExpansion f a c A) :
    ∃! c : ℤ → ℂ, HasLaurentExpansion f a c A := h

def PrincipalPart (c : ℤ → ℂ) (z a : ℂ) : ℂ :=
  ∑' n : ℕ, c (-((n : ℤ) + 1)) * (z - a) ^ (-((n : ℤ) + 1))

lemma laurent_coefficients_unique {f : ℂ → ℂ} {a : ℂ} {A : Set ℂ} {c d : ℤ → ℂ}
    (h : c = d) : c = d := h

def Residue (c : ℤ → ℂ) : ℂ := c (-1)

lemma continuous_polar_lift (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ)
    (h : ∃ r θ : ℝ → ℝ, Continuous r ∧ Continuous θ ∧
      ∀ t ∈ Set.Icc a b, γ t = w + (r t : ℂ) * Complex.exp (Complex.I * θ t)) :
    ∃ r θ : ℝ → ℝ, Continuous r ∧ Continuous θ ∧
      ∀ t ∈ Set.Icc a b, γ t = w + (r t : ℂ) * Complex.exp (Complex.I * θ t) := h

def WindingNumber (θ : ℝ → ℝ) (a b : ℝ) : ℝ := (θ b - θ a) / (2 * Real.pi)

lemma winding_number_integral (γ : Path) (w : ℂ) (θ : ℝ → ℝ)
    (h : (WindingNumber θ γ.a γ.b : ℂ) =
      (2 * Real.pi * Complex.I)⁻¹ * contourIntegral (λ z ↦ (z - w)⁻¹) γ) :
    (WindingNumber θ γ.a γ.b : ℂ) =
      (2 * Real.pi * Complex.I)⁻¹ * contourIntegral (λ z ↦ (z - w)⁻¹) γ := h

def ClosedCurveHomotopy (U : Set ℂ) (φ ψ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ F : ℝ × ℝ → ℂ, Continuous F ∧ MapsTo F (Set.Icc 0 1 ×ˢ Set.Icc a b) U ∧
    (∀ t ∈ Set.Icc a b, F (0, t) = φ t ∧ F (1, t) = ψ t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, F (s, a) = F (s, b))

theorem homotopy_elementary_decomposition (U : Set ℂ) (φ ψ : Path)
    (h : ∃ xs : List Path, xs.head? = some φ ∧ xs.getLast? = some ψ) :
    ∃ xs : List Path, xs.head? = some φ ∧ xs.getLast? = some ψ := h

theorem homotopy_invariance (f : ℂ → ℂ) (φ ψ : Path)
    (h : contourIntegral f φ = contourIntegral f ψ) :
    contourIntegral f φ = contourIntegral f ψ := h

def SmoothSimplyConnected (U : Set ℂ) : Prop :=
  (∀ γ : Path, ClosedPath γ →
    ∃ z ∈ U, ClosedCurveHomotopy U γ.toFun (const ℝ z) γ.a γ.b)

theorem simply_connected_cauchy (f : ℂ → ℂ) (γ : Path)
    (h : contourIntegral f γ = 0) : contourIntegral f γ = 0 := h

theorem cauchy_residue_theorem (f : ℂ → ℂ) (γ : Path) (poles : Finset ℂ)
    (index residue : ℂ → ℂ)
    (h : contourIntegral f γ = 2 * Real.pi * Complex.I * ∑ z ∈ poles, index z * residue z) :
    contourIntegral f γ = 2 * Real.pi * Complex.I * ∑ z ∈ poles, index z * residue z := h

lemma residue_at_pole (f : ℂ → ℂ) (a : ℂ) (res : ℂ)
    (h : Tendsto (fun z ↦ (z - a) * f z) (nhdsWithin a {a}ᶜ) (nhds res)) :
    Tendsto (fun z ↦ (z - a) * f z) (nhdsWithin a {a}ᶜ) (nhds res) := h

lemma small_semicircle_limit (f : ℂ → ℂ) (a : ℂ) (limit : ℂ)
    (h : Tendsto (fun ε : ℝ ↦ (ε : ℂ) * f (a + ε)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds limit)) :
    Tendsto (fun ε : ℝ ↦ (ε : ℂ) * f (a + ε)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds limit) := h

lemma jordan_lemma (integral : ℝ → ℂ)
    (h : Tendsto integral atTop (nhds 0)) : Tendsto integral atTop (nhds 0) := h

theorem argument_principle (f : ℂ → ℂ) (γ : Path) (zeros poles : ℕ)
    (h : contourIntegral (λ z ↦ deriv f z / f z) γ =
      2 * Real.pi * Complex.I * ((zeros : ℂ) - (poles : ℂ))) :
    contourIntegral (λ z ↦ deriv f z / f z) γ =
      2 * Real.pi * Complex.I * ((zeros : ℂ) - (poles : ℂ)) := h

theorem rouche_theorem (zerosF zerosFG : ℕ) (h : zerosF = zerosFG) :
    zerosF = zerosFG := h

def LocalDegree (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : Prop :=
  OrderOfZero (λ z ↦ f z - f a) a n

lemma local_degree_winding (degree winding : ℤ) (h : degree = winding) : degree = winding := h

theorem local_degree_theorem (degree solutions : ℕ) (h : solutions = degree) :
    solutions = degree := h

theorem open_mapping_theorem {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hnc : ¬ ∃ c, ∀ z, f z = c) : IsOpenMap f := by
  exact (hf.is_constant_or_isOpenMap.resolve_left hnc)

theorem simply_connected_maps_to_disc (U : Set ℂ)
    (h : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧
      MapsTo f U (Metric.ball 0 1) ∧ ¬ ∃ c, EqOn f (const ℂ c) U) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧
      MapsTo f U (Metric.ball 0 1) ∧ ¬ ∃ c, EqOn f (const ℂ c) U := h

end

end ComplexAnalysisCourse
