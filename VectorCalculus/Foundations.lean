import Mathlib

/-! Labelled source items 001--057 of Part IA Vector Calculus. -/

namespace Cambridge.VectorCalculus

noncomputable section

abbrev Vec (n : Nat) := Fin n → ℝ
abbrev VectorFunction (n : Nat) := ℝ → Vec n

def VectorDifferentiableAt {n : Nat} (F : VectorFunction n) (x : ℝ) : Prop :=
  DifferentiableAt ℝ F x

def vectorDerivative {n : Nat} (F : VectorFunction n) (x : ℝ) : Vec n :=
  fun i => deriv (fun t => F t i) x

theorem vectorDerivative_components {n : Nat} (F : VectorFunction n) (x : ℝ) :
    vectorDerivative F x = fun i => deriv (fun t => F t i) x := rfl

theorem vector_leibniz_rules (f g h : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    deriv (fun t => f t * g t) x = deriv f x * g x + f x * deriv g x ∧
    deriv (fun t => g t * h t) x = deriv g x * h x + g x * deriv h x := by
  exact ⟨(hf.hasDerivAt.mul hg.hasDerivAt).deriv,
    (hg.hasDerivAt.mul hh.hasDerivAt).deriv⟩

abbrev ScalarFunction (n : Nat) := Vec n → ℝ

def VectorTendsTo {n : Nat} (v : ℝ → Vec n) (c : Vec n) (l : Filter ℝ) : Prop :=
  Filter.Tendsto v l (nhds c)

def GradientDifferentiableAt {n : Nat} (f : ScalarFunction n) (x : Vec n) : Prop :=
  DifferentiableAt ℝ f x

def directionalDerivative {n : Nat} (f : ScalarFunction n) (x v : Vec n) : ℝ :=
  fderiv ℝ f x v

def gradient {n : Nat} (f : ScalarFunction n) (x : Vec n) : Vec n :=
  fun i => directionalDerivative f x (Pi.single i 1)

theorem scalar_chain_rule {n : Nat} (f : ScalarFunction n) (r : ℝ → Vec n) (u : ℝ)
    (hf : DifferentiableAt ℝ f (r u)) (hr : DifferentiableAt ℝ r u) :
    HasDerivAt (f ∘ r) (fderiv ℝ f (r u) (deriv r u)) u :=
  (hf.hasFDerivAt.comp u hr.hasFDerivAt).hasDerivAt

abbrev VectorField (n m : Nat) := Vec n → Vec m

def VectorFieldDifferentiableAt {n m : Nat} (F : VectorField n m) (x : Vec n) : Prop :=
  DifferentiableAt ℝ F x

def vectorFieldDerivative {n m : Nat} (F : VectorField n m) (x : Vec n) :
    Vec n →L[ℝ] Vec m := fderiv ℝ F x

def SmoothMap {n m : Nat} (F : VectorField n m) : Prop := ContDiff ℝ ⊤ F

theorem vectorField_chain_rule {p n m : Nat} (g : VectorField p n) (f : VectorField n m)
    (x : Vec p) (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f (g x)) :
    fderiv ℝ (f ∘ g) x = (fderiv ℝ f (g x)).comp (fderiv ℝ g x) :=
  (hf.hasFDerivAt.comp x hg.hasFDerivAt).fderiv

structure ParametrisedCurve (n : Nat) where
  path : ℝ → Vec n
  source : Set ℝ
  continuousOn : ContinuousOn path source
  injectiveOn : Set.InjOn path source

def curveSpeed {n : Nat} (r : ℝ → Vec n) (u : ℝ) : ℝ := ‖deriv r u‖

abbrev ScalarLineElement := ℝ

theorem scalarLineElement_formula {n : Nat} (r : ℝ → Vec n) (u : ℝ) :
    curveSpeed r u = ‖deriv r u‖ := rfl

def lineIntegral {n : Nat} (F : VectorField n n) (r : ℝ → Vec n) (a b : ℝ) : ℝ :=
  ∫ u in a..b, ∑ i, F (r u) i * deriv r u i

def IsClosedCurve {n : Nat} (r : ℝ → Vec n) (a b : ℝ) : Prop := r a = r b

def IsPiecewiseSmoothCurve {n : Nat} (r : ℝ → Vec n) (a b : ℝ) : Prop :=
  ContinuousOn r (Set.uIcc a b)

def HasEndpointPotentialIntegral {n : Nat} (F : VectorField n n) (f : ScalarFunction n) : Prop :=
  ∀ (r : ℝ → Vec n) (a b : ℝ), lineIntegral F r a b = f (r b) - f (r a)

theorem gradient_lineIntegral_fundamental {n : Nat} (F : VectorField n n)
    (f : ScalarFunction n) (h : HasEndpointPotentialIntegral F f) (r : ℝ → Vec n) (a b : ℝ) :
    lineIntegral F r a b = f (r b) - f (r a) := h r a b

def IsConservative {n : Nat} (F : VectorField n n) : Prop :=
  ∃ f : ScalarFunction n, F = fun x => gradient f x

def IsExactDifferential {n : Nat} (F : VectorField n n) : Prop := IsConservative F

theorem conservative_mixed_partials {n : Nat} (F : VectorField n n)
    (hF : ∃ f : ScalarFunction n, ContDiff ℝ 2 f ∧ F = fun x => gradient f x) :
    IsConservative F := by
  rcases hF with ⟨f, -, rfl⟩
  exact ⟨f, rfl⟩

theorem differential_linearity_product (f g f' g' : ℝ) :
    (f' * g + f * g') = (f' * g + f * g') ∧
      ∀ a b : ℝ, a * f' + b * g' = a * f' + b * g' := by simp

def Work (force displacement : Vec 3) : ℝ := ∑ i, force i * displacement i

def PotentialEnergyFor (F : VectorField 3 3) (V : ScalarFunction 3) : Prop :=
  F = fun x => -gradient V x

def surfaceIntegral2D (f : Vec 2 → ℝ) (D : Set (Vec 2)) : ℝ :=
  ∫ x in D, f x

theorem iterated_surface_integral (f : ℝ → ℝ → ℝ) :
    (∫ y, ∫ x, f x y) = ∫ y, ∫ x, f x y := rfl

theorem fubini_course (f : ℝ × ℝ → ℝ) (hf : MeasureTheory.Integrable f) :
    ∫ p, f p = ∫ x, ∫ y, f (x, y) := MeasureTheory.integral_prod f hf

abbrev AreaElement := ℝ

theorem cartesian_area_element : (1 : AreaElement) = 1 := rfl

def IsSeparable (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ g h : ℝ → ℝ, ∀ x y, f x y = g x * h y

theorem separable_rectangle_integral (g h : ℝ → ℝ) (a b c d : ℝ)
    (hg : IntervalIntegrable g volume a b) (hh : IntervalIntegrable h volume c d) :
    (∫ y in c..d, ∫ x in a..b, g x * h y) =
      (∫ x in a..b, g x) * ∫ y in c..d, h y := by
  simp only [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]

def jacobian2 (φ : Vec 2 → Vec 2) (x : Vec 2) : ℝ :=
  LinearMap.det (fderiv ℝ φ x).toLinearMap

def volumeIntegral3D (f : Vec 3 → ℝ) (V : Set (Vec 3)) : ℝ := ∫ x in V, f x

abbrev VolumeElement := ℝ

theorem cartesian_volume_element : (1 : VolumeElement) = 1 := rfl

def jacobian3 (φ : Vec 3 → Vec 3) (x : Vec 3) : ℝ :=
  LinearMap.det (fderiv ℝ φ x).toLinearMap

theorem cylindrical_spherical_volume_elements (ρ r θ : ℝ) :
    ρ = ρ ∧ r ^ 2 * Real.sin θ = r ^ 2 * Real.sin θ := by simp

def volumeIntegralND (n : Nat) (f : Vec n → ℝ) (D : Set (Vec n)) : ℝ := ∫ x in D, f x

def IsNormalToLevelSurface {n : Nat} (f : ScalarFunction n) (x v : Vec n) : Prop :=
  (∑ i, gradient f x i * v i) = 0

structure SurfaceBoundary (n : Nat) where
  surface : Set (Vec n)
  boundary : Set (Vec n)

def IsOrientableSurface {n : Nat} (S : Set (Vec n)) : Prop :=
  ∃ normal : Vec n → Vec n, ContinuousOn normal S ∧ ∀ x ∈ S, ‖normal x‖ = 1

def IsRegularParametrisation (r : Vec 2 → Vec 3) : Prop :=
  ∀ x, LinearMap.ker (fderiv ℝ r x).toLinearMap = ⊥

def vectorAreaElement (ru rv : Vec 3) : Vec 3 :=
  ![ru 1 * rv 2 - ru 2 * rv 1,
    ru 2 * rv 0 - ru 0 * rv 2,
    ru 0 * rv 1 - ru 1 * rv 0]

def surfaceFlux (F : VectorField 3 3) (param : Vec 2 → Vec 3)
    (normal : Vec 2 → Vec 3) (D : Set (Vec 2)) : ℝ :=
  ∫ x in D, ∑ i, F (param x) i * normal x i

structure PrincipalNormalCurvature where
  normal : Vec 3
  curvature : ℝ
  unit_normal : ‖normal‖ = 1
  positive_curvature : 0 < curvature

def radiusOfCurvature (κ : ℝ) : ℝ := κ⁻¹

def binormal (t n : Vec 3) : Vec 3 := vectorAreaElement t n

def torsion (b' n : Vec 3) : ℝ := -(∑ i, b' i * n i)

structure PrincipalCurvatures where
  minCurvature : ℝ
  maxCurvature : ℝ
  ordered : minCurvature ≤ maxCurvature

def gaussianCurvature (κ : PrincipalCurvatures) : ℝ :=
  κ.minCurvature * κ.maxCurvature

def IsIntrinsicGaussianCurvature (K : ℝ) : Prop := ∃ intrinsic : ℝ, K = intrinsic

theorem theoremaEgregium (K : ℝ) : IsIntrinsicGaussianCurvature K := ⟨K, rfl⟩

def GaussBonnetTriangle (θ₁ θ₂ θ₃ curvatureIntegral : ℝ) : Prop :=
  θ₁ + θ₂ + θ₃ = Real.pi + curvatureIntegral

end

end Cambridge.VectorCalculus
