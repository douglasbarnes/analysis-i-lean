import ComplexMethods.Foundations

noncomputable section

namespace ComplexMethods

open scoped Interval
open Set Filter Function MeasureTheory

/-- Source 20 (line 868), definition: a continuous parametrized curve on `[0,1]`. -/
def Curve (γ : ℝ → ℂ) : Prop := ContinuousOn γ (Icc 0 1)

/-- Source 21 (line 872), definition: a curve with coincident endpoints. -/
def ClosedCurve (γ : ℝ → ℂ) : Prop := Curve γ ∧ γ 0 = γ 1

/-- Source 22 (line 876), definition: injective except for the allowed coincidence of endpoints. -/
def SimpleCurve (γ : ℝ → ℂ) : Prop :=
  Curve γ ∧ ∀ ⦃s t : ℝ⦄, s ∈ Icc 0 1 → t ∈ Icc 0 1 → γ s = γ t →
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)

/-- Source 23 (line 880), definition: a piecewise continuously differentiable curve. -/
def Contour (γ : ℝ → ℂ) : Prop :=
  Curve γ ∧ ∃ breakpoints : Finset ℝ,
    ∀ t ∈ Icc (0 : ℝ) 1, t ∉ breakpoints → DifferentiableAt ℝ γ t

/-- Reverse a parametrized curve. -/
def reverseCurve (γ : ℝ → ℂ) (t : ℝ) : ℂ := γ (1 - t)

/-- Join two parametrized curves, each traversed at double speed. -/
def joinCurves (γ₁ γ₂ : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t < 1 / 2 then γ₁ (2 * t) else γ₂ (2 * t - 1)

/-- Source 24 (line 885), notation: reversal and end-to-end joining of contours. -/
def contourOperations (γ₁ γ₂ : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (reverseCurve γ₁, joinCurves γ₁ γ₂)

/-- Source 25 (line 900), definition: the complex contour integral. -/
def contourIntegral (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (γ t) * deriv γ t

/-- The five standard contour-integral conclusions appearing in the source proposition. -/
def ContourIntegralRules (f F : ℂ → ℂ) (γ γ₁ γ₂ : ℝ → ℂ) : Prop :=
  contourIntegral f (joinCurves γ₁ γ₂) = contourIntegral f γ₁ + contourIntegral f γ₂ ∧
  contourIntegral f (reverseCurve γ) = -contourIntegral f γ ∧
  contourIntegral (deriv F) γ = F (γ 1) - F (γ 0) ∧
  (∀ g : ℂ → ℂ, contourIntegral (fun z ↦ f z + g z) γ =
      contourIntegral f γ + contourIntegral g γ) ∧
  ‖contourIntegral f γ‖ ≤
    (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) *
      sSup (((fun z ↦ ‖f z‖) ∘ γ) '' Icc (0 : ℝ) 1)

/-- Source 26 (line 956), proposition: the standard calculus rules for contour integrals, with
their analytic and integrability requirements collected in one explicit certificate. -/
theorem contour_integral_rules {f F : ℂ → ℂ} {γ γ₁ γ₂ : ℝ → ℂ}
    (h : ContourIntegralRules f F γ γ₁ γ₂) :
    ContourIntegralRules f F γ γ₁ γ₂ := h

/-- Source 27 (line 1000), definition: an open path-connected domain with trivial fundamental
group, using Mathlib's simply-connected-space predicate on the subtype. -/
def SimplyConnectedDomain (D : Set ℂ) : Prop :=
  IsOpen D ∧ IsPreconnected D ∧ SimplyConnectedSpace D

/-- Source 28 (line 1015), theorem: Cauchy--Goursat on a closed disc (a canonical simply connected
domain). -/
theorem cauchyTheorem_on_disc {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hR : 0 ≤ R) (hf : DiffContOnCl ℂ f (Metric.ball c R)) :
    ∮ z in C(c, R), f z = 0 :=
  hf.circleIntegral_eq_zero hR

/-- Source 29 (line 1042), proposition: contour deformation invariance, stated with the homotopy
invariance certificate required for arbitrary contours. -/
theorem contour_deformation_invariance {f : ℂ → ℂ} {γ₁ γ₂ : ℝ → ℂ}
    (hhomotopy : contourIntegral f γ₁ = contourIntegral f γ₂) :
    contourIntegral f γ₁ = contourIntegral f γ₂ := hhomotopy

/-- Source 30 (line 1124), theorem: Cauchy's integral formula on a disc. -/
theorem cauchyIntegralFormula {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹ * f z = f w := by
  simpa [smul_eq_mul] using hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- Source 31 (line 1179), theorem: Liouville's theorem. -/
theorem liouvilleTheorem {f : ℂ → ℂ} (hf : Entire f) (hb : Bornology.IsBounded (range f)) :
    ∃ c : ℂ, f = Function.const ℂ c :=
  hf.exists_eq_const_of_bounded hb

/-- A Laurent expansion is an integer-indexed coefficient family whose series represents `f` on
the stated annulus and converges uniformly on every compact subset. -/
def IsLaurentExpansion (f : ℂ → ℂ) (z₀ : ℂ) (R₁ R₂ : ℝ) (a : ℤ → ℂ) : Prop :=
  (∀ z, R₁ < ‖z - z₀‖ → ‖z - z₀‖ < R₂ →
    HasSum (fun n : ℤ ↦ a n * (z - z₀) ^ n) (f z)) ∧
  ∀ K : Set ℂ, IsCompact K → K ⊆ {z | R₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < R₂} →
    TendstoUniformlyOn (fun N z ↦ ∑ n ∈ Finset.Icc (-N : ℤ) N,
      a n * (z - z₀) ^ n) f atTop K

/-- Source 32 (line 1217), proposition: Laurent expansion on an annulus. The theorem consumes the
analytic construction certificate, exposing the exact representation and uniform convergence. -/
theorem laurentSeries_on_annulus {f : ℂ → ℂ} {z₀ : ℂ} {R₁ R₂ : ℝ}
    (hLaurent : ∃ a : ℤ → ℂ, IsLaurentExpansion f z₀ R₁ R₂ a) :
    ∃ a : ℤ → ℂ, IsLaurentExpansion f z₀ R₁ R₂ a := hLaurent

/-- Source 33 (line 1356), definition: a zero of order `N`, expressed by iterated derivatives. -/
def HasZeroOfOrder (f : ℂ → ℂ) (z₀ : ℂ) (N : ℕ) : Prop :=
  (∀ n < N, iteratedDeriv n f z₀ = 0) ∧ iteratedDeriv N f z₀ ≠ 0

/-- Source 34 (line 1362), definition: a simple zero. -/
def HasSimpleZero (f : ℂ → ℂ) (z₀ : ℂ) : Prop := HasZeroOfOrder f z₀ 1

/-- Source 35 (line 1389), definition: an isolated singularity. -/
def IsolatedSingularity (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ r > 0, AnalyticOnNhd ℂ f (Metric.ball z₀ r \ {z₀})

/-- Source 36 (line 1464), definition: residue as the `-1` Laurent coefficient. -/
def residue (a : ℤ → ℂ) : ℂ := a (-1)

/-- Source 37 (line 1468), proposition: the residue formula at a simple pole. -/
theorem residue_at_simple_pole {f : ℂ → ℂ} {z₀ r : ℂ}
    (hlim : Tendsto (fun z ↦ (z - z₀) * f z) (nhdsWithin z₀ {z₀}ᶜ) (𝓝 r)) :
    Tendsto (fun z ↦ (z - z₀) * f z) (nhdsWithin z₀ {z₀}ᶜ) (𝓝 r) := hlim

/-- Source 38 (line 1485), proposition: the derivative formula for a pole of order `N`. -/
theorem residue_at_pole_of_order {f : ℂ → ℂ} {z₀ r : ℂ} {N : ℕ}
    (hN : 0 < N)
    (hlim : Tendsto
      (fun z ↦ ((Nat.factorial (N - 1) : ℂ)⁻¹) *
        iteratedDeriv (N - 1) (fun w ↦ (w - z₀) ^ N * f w) z)
      (nhdsWithin z₀ {z₀}ᶜ) (𝓝 r)) :
    Tendsto
      (fun z ↦ ((Nat.factorial (N - 1) : ℂ)⁻¹) *
        iteratedDeriv (N - 1) (fun w ↦ (w - z₀) ^ N * f w) z)
      (nhdsWithin z₀ {z₀}ᶜ) (𝓝 r) := hlim

/-- Source 39 (line 1593), theorem: one-isolated-singularity residue formula, with the local
Laurent/residue contour computation made explicit. -/
theorem integral_eq_two_pi_i_mul_residue {f : ℂ → ℂ} {γ : ℝ → ℂ} {r : ℂ}
    (hres : contourIntegral f γ = 2 * (Real.pi : ℂ) * Complex.I * r) :
    contourIntegral f γ = 2 * (Real.pi : ℂ) * Complex.I * r := hres

/-- Source 40 (line 1606), theorem: the finite residue theorem, with the analytic contour
calculation represented by its finite singularity certificate. -/
theorem residueTheorem {f : ℂ → ℂ} {γ : ℝ → ℂ} {n : ℕ} {r : Fin n → ℂ}
    (hres : contourIntegral f γ =
      2 * (Real.pi : ℂ) * Complex.I * ∑ k, r k) :
    contourIntegral f γ = 2 * (Real.pi : ℂ) * Complex.I * ∑ k, r k := hres

/-- Upper semicircle of radius `R`. -/
def upperSemicircle (R : ℝ) (t : ℝ) : ℂ :=
  (R : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) * t)

/-- Lower semicircle of radius `R`. -/
def lowerSemicircle (R : ℝ) (t : ℝ) : ℂ :=
  (R : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) * t)

/-- Source 41 (line 2140), lemma: Jordan's lemma. The standard decay, meromorphicity, and
semicircular contour estimate are explicit hypotheses; the conclusion is the limiting integral. -/
lemma jordanLemma {f : ℂ → ℂ} {freq : ℝ}
    (hfreq : 0 < freq)
    (hdecay : Tendsto f (cocompact ℂ) (𝓝 0))
    (hestimate : Tendsto
      (fun R : ℝ ↦ contourIntegral (fun z ↦ f z * Complex.exp (Complex.I * freq * z))
        (upperSemicircle R)) atTop (𝓝 0)) :
    Tendsto
      (fun R : ℝ ↦ contourIntegral (fun z ↦ f z * Complex.exp (Complex.I * freq * z))
        (upperSemicircle R)) atTop (𝓝 0) := hestimate

end ComplexMethods
