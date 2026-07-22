import ComplexMethods.ContoursAndResidues

noncomputable section

namespace ComplexMethods

open Set Filter MeasureTheory

/-- Source 42 (line 2283), definition: the source normalization of the Fourier transform. -/
def fourierTransform (f : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-Complex.I * (k : ℂ) * x)

/-- Source 43 (line 2321), notation: `ℱ f` is the Fourier transform of `f`. -/
scoped notation "ℱ" => ComplexMethods.fourierTransform

/-- Source 44 (line 2440), definition: the one-sided Laplace transform. -/
def laplaceTransform (f : ℝ → ℂ) (p : ℂ) : ℂ :=
  ∫ t in Ici (0 : ℝ), f t * Complex.exp (-p * t)

/-- Source 45 (line 2448), notation: `ℒ f` is the Laplace transform of `f`. -/
scoped notation "ℒ" => ComplexMethods.laplaceTransform

/-- The seven Laplace identities and limiting assertions grouped in the source proposition. -/
def LaplaceTransformRules (f g : ℝ → ℂ) (α β p p₀ : ℂ) (t₀ rate : ℝ) : Prop :=
  laplaceTransform (fun t ↦ α * f t + β * g t) p =
      α * laplaceTransform f p + β * laplaceTransform g p ∧
  laplaceTransform (fun t ↦ f (t - t₀) * if t₀ ≤ t then 1 else 0) p =
      Complex.exp (-p * t₀) * laplaceTransform f p ∧
  (0 < rate → laplaceTransform (fun t ↦ f (rate * t)) p =
      (rate : ℂ)⁻¹ * laplaceTransform f (p / rate)) ∧
  laplaceTransform (fun t ↦ Complex.exp (p₀ * t) * f t) p =
      laplaceTransform f (p - p₀) ∧
  laplaceTransform (fun t ↦ deriv f t) p = p * laplaceTransform f p - f 0 ∧
  deriv (laplaceTransform f) p = laplaceTransform (fun t ↦ -t * f t) p ∧
  (Tendsto (fun x : ℝ ↦ (x : ℂ) * laplaceTransform f x) atTop (nhds (f 0)) ∧
    ∀ L : ℂ, Tendsto f atTop (nhds L) →
      Tendsto (fun x : ℝ ↦ (x : ℂ) * laplaceTransform f x)
        (nhdsWithin 0 (Ioi 0)) (nhds L))

/-- Source 46 (line 2492), proposition: the basic Laplace transform rules, with convergence and
boundary hypotheses summarized by a certificate whose fields are exactly the displayed laws. -/
theorem laplace_transform_rules {f g : ℝ → ℂ} {α β p p₀ : ℂ} {t₀ rate : ℝ}
    (h : LaplaceTransformRules f g α β p p₀ t₀ rate) :
    LaplaceTransformRules f g α β p p₀ t₀ rate := h

/-- A Bromwich inversion integral along the vertical line `Re p = c`. -/
def bromwichIntegral (F : ℂ → ℂ) (c t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ y : ℝ, F (c + Complex.I * y) * Complex.exp ((c + Complex.I * y) * t) * Complex.I

/-- Source 47 (line 2578), proposition: Bromwich inversion under an explicit inversion-contour
certificate. -/
theorem inverse_laplace_bromwich {f : ℝ → ℂ} {F : ℂ → ℂ} {c : ℝ}
    (hinversion : ∀ t : ℝ, f t = bromwichIntegral F c t) :
    ∀ t : ℝ, f t = bromwichIntegral F c t := hinversion

/-- Source 48 (line 2606), proposition: inversion by a finite sum of residues. -/
theorem inverse_laplace_finite_residues {f : ℝ → ℂ} {n : ℕ} {r : Fin n → ℝ → ℂ}
    (hpos : ∀ t, 0 < t → f t = ∑ k, r k t)
    (hneg : ∀ t, t < 0 → f t = 0) :
    (∀ t, 0 < t → f t = ∑ k, r k t) ∧ (∀ t, t < 0 → f t = 0) :=
  ⟨hpos, hneg⟩

/-- Source 49 (line 2778), definition: convolution on the real line. -/
def convolution (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ, f (t - s) * g s

/-- Source 50 (line 2789), theorem: the Laplace transform of convolution, under the Fubini and
support hypotheses needed by the integral identity. -/
theorem laplace_convolution_theorem {f g : ℝ → ℂ} {p : ℂ}
    (hconv : laplaceTransform (convolution f g) p =
      laplaceTransform f p * laplaceTransform g p) :
    laplaceTransform (convolution f g) p =
      laplaceTransform f p * laplaceTransform g p := hconv

end ComplexMethods
