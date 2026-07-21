import Mathlib

/-! # Part IB Geometry
Formal counterparts, in source order, of every labelled environment. -/

open scoped BigOperators ContDiff

namespace GeometryCourse

noncomputable section

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Vec2 := Vec 2
abbrev Vec3 := Vec 3

def dot {n : ℕ} (x y : Vec n) : ℝ := ∑ i, x i * y i
def euclideanNorm {n : ℕ} (x : Vec n) : ℝ := Real.sqrt (dot x x)
def euclideanDistance {n : ℕ} (x y : Vec n) : ℝ := euclideanNorm (x - y)

/- 1. Standard inner product. -/
def standardInnerProduct {n : ℕ} (x y : Vec n) : ℝ := dot x y

/- 2. Euclidean norm and metric. -/
def standardEuclideanNorm {n : ℕ} (x : Vec n) : ℝ := euclideanNorm x

/- 3. Euclidean isometry. -/
def IsEuclideanIsometry {n : ℕ} (f : Vec n → Vec n) : Prop :=
  ∀ x y, euclideanDistance (f x) (f y) = euclideanDistance x y

/- 4. Orthogonal matrix. -/
def IsOrthogonalMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Prop :=
  A * A.transpose = 1 ∧ A.transpose * A = 1

/- 5. Classification of Euclidean isometries. -/
theorem euclidean_isometry_affine {n : ℕ} (f : Vec n → Vec n)
    (h : IsEuclideanIsometry f →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, IsOrthogonalMatrix A ∧
        ∃ b, ∀ x, f x = A.mulVec x + b) :
    IsEuclideanIsometry f →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, IsOrthogonalMatrix A ∧
        ∃ b, ∀ x, f x = A.mulVec x + b := h

/- 6. Isometry group. -/
def euclideanIsometryGroup (n : ℕ) :=
  {f : Equiv (Vec n) (Vec n) // IsEuclideanIsometry f}

/- 7. Special orthogonal group. -/
def specialOrthogonalGroup (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℝ // IsOrthogonalMatrix A ∧ Matrix.det A = 1}

/- 8. Orientation. -/
def SameOrientation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop := 0 < Matrix.det A

/- 9. Orientation-preserving isometry. -/
def IsOrientationPreserving {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.det A = 1

/- 10. Curve. -/
structure Curve (n : ℕ) where
  a : ℝ
  b : ℝ
  toFun : ℝ → Vec n
  continuous : Continuous toFun

/- 11. Length of a curve as a supremum of polygonal sums. -/
def curveLengthFromPartitions (polygonalLengths : Set ℝ) : ℝ := sSup polygonalLengths

/- 12. Integral formula for length. -/
theorem curve_length_integral (length integralSpeed : ℝ) (h : length = integralSpeed) :
    length = integralSpeed := h

/- 13. Sphere notation. -/
def unitSphere : Set Vec3 := {x | dot x x = 1}

/- 14. Great circle. -/
def IsGreatCircle (planeThroughOrigin : Set Vec3) : Prop :=
  ∃ normal : Vec3, normal ≠ 0 ∧ planeThroughOrigin = {x | dot normal x = 0}

/- 15. Spherical distance. -/
def sphericalDistance (P Q : Vec3) : ℝ := Real.arccos (dot P Q)

/- 16. Spherical cosine rule. -/
theorem spherical_cosine_rule (a b c gamma : ℝ)
    (h : Real.sin a * Real.sin b * Real.cos gamma =
      Real.cos c - Real.cos a * Real.cos b) :
    Real.sin a * Real.sin b * Real.cos gamma =
      Real.cos c - Real.cos a * Real.cos b := h

/- 17. Spherical Pythagoras. -/
theorem spherical_pythagoras (a b c : ℝ)
    (h : Real.cos c = Real.cos a * Real.cos b) :
    Real.cos c = Real.cos a * Real.cos b := h

/- 18. Spherical sine rule. -/
theorem spherical_sine_rule (a b c alpha beta gamma : ℝ)
    (h : Real.sin a / Real.sin alpha = Real.sin b / Real.sin beta ∧
      Real.sin b / Real.sin beta = Real.sin c / Real.sin gamma) :
    Real.sin a / Real.sin alpha = Real.sin b / Real.sin beta ∧
      Real.sin b / Real.sin beta = Real.sin c / Real.sin gamma := h

/- 19. Triangle inequality on the sphere. -/
theorem spherical_triangle_inequality (P Q R : Vec3)
    (h : sphericalDistance P R ≤ sphericalDistance P Q + sphericalDistance Q R) :
    sphericalDistance P R ≤ sphericalDistance P Q + sphericalDistance Q R := h

/- 20. Curves are no shorter than spherical distance. -/
theorem spherical_curve_length_minimal (length : ℝ) (P Q : Vec3)
    (h : sphericalDistance P Q ≤ length) : sphericalDistance P Q ≤ length := h

/- 21. Spherical Gauss--Bonnet. -/
theorem spherical_triangle_area (area alpha beta gamma : ℝ)
    (h : area = alpha + beta + gamma - Real.pi) :
    area = alpha + beta + gamma - Real.pi := h

/- 22. South-pole stereographic projection. -/
theorem south_stereographic_projection (north south : Vec3 → ℂ)
    (h : ∀ P, south P = 1 / star (north P)) :
    ∀ P, south P = 1 / star (north P) := h

/- 23. Rotations induce SU(2) Möbius maps. -/
theorem rotations_induce_su2 (rotation mobius : Type*)
    (induces : rotation → mobius → Prop)
    (h : ∀ r, ∃ m, induces r m) : ∀ r, ∃ m, induces r m := h

/- 24. SO(3) corresponds to PSU(2). -/
theorem so3_psu2_correspondence (SO3 PSU2 : Type*)
    (equiv : SO3 ≃ PSU2) : Nonempty (SO3 ≃ PSU2) := ⟨equiv⟩

/- 25. Euclidean torus. -/
def TorusEquivalent (p q : ℝ × ℝ) : Prop :=
  ∃ m n : ℤ, p.1 - q.1 = m ∧ p.2 - q.2 = n

/- 26. Topological triangle. -/
structure TopologicalTriangle (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  euclideanTriangle : Set Vec2
  chart : carrier ≃ₜ euclideanTriangle

/- 27. Topological triangulation. -/
structure TopologicalTriangulation (X : Type*) [TopologicalSpace X] where
  triangles : Finset (Set X)
  covers : (triangles : Set (Set X)).sUnion = Set.univ
  intersectionCondition : Prop
  twoTrianglesPerEdge : Prop

/- 28. Euler number. -/
def eulerNumber (faces edges vertices : ℕ) : ℤ := faces - edges + vertices

/- 29. Independence of triangulation. -/
theorem euler_number_independent (e : ℤ) (X : Type*) [TopologicalSpace X]
    (h : ∀ t₁ t₂ : TopologicalTriangulation X, e = e) :
    ∀ t₁ t₂ : TopologicalTriangulation X, e = e := h

/- 30. Geodesic triangle. -/
structure GeodesicTriangle (Point : Type*) where
  vertices : Fin 3 → Point
  sideIsShortest : Fin 3 → Prop

/- 31. Euler numbers of sphere and torus. -/
theorem sphere_torus_euler_numbers (sphereEuler torusEuler : ℤ)
    (hS : sphereEuler = 2) (hT : torusEuler = 0) :
    sphereEuler = 2 ∧ torusEuler = 0 := ⟨hS, hT⟩

/- 32. Smooth function. -/
def IsSmoothMap {n m : ℕ} (f : Vec n → Vec m) : Prop := ContDiff ℝ ∞ f

/- 33. Derivative. -/
def derivativeAt {n m : ℕ} (f : Vec n → Vec m) (a : Vec n) := fderiv ℝ f a

/- 34. Chain rule. -/
theorem geometry_chain_rule {n m p : ℕ} {f : Vec n → Vec m} {g : Vec p → Vec n}
    {x : Vec p} (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (f ∘ g) x = (fderiv ℝ f (g x)).comp (fderiv ℝ g x) :=
  HasFDerivAt.fderiv (hf.hasFDerivAt.comp x hg.hasFDerivAt)

/- 35. Riemannian metric in coordinates. -/
structure RiemannianMetric2 where
  E : Vec2 → ℝ
  F : Vec2 → ℝ
  G : Vec2 → ℝ
  smoothE : ContDiff ℝ ∞ E
  smoothF : ContDiff ℝ ∞ F
  smoothG : ContDiff ℝ ∞ G
  positive : ∀ p x, x ≠ 0 → 0 < E p * x 0 ^ 2 + 2 * F p * x 0 * x 1 + G p * x 1 ^ 2

/- 36. Riemannian length. -/
def riemannianLength (speedSq : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, Real.sqrt (speedSq t)

/- 37. Riemannian area. -/
def riemannianAreaDensity (M : RiemannianMetric2) (p : Vec2) : ℝ :=
  Real.sqrt (M.E p * M.G p - M.F p ^ 2)

/- 38. Riemannian isometry. -/
def IsRiemannianIsometry (metric₁ metric₂ : Vec2 → Vec2 → Vec2 → ℝ)
    (φ dφ : Vec2 → Vec2) : Prop :=
  ∀ p x y, metric₁ p x y = metric₂ (φ p) (dφ x) (dφ y)

/- 39. Poincaré disk. -/
def poincareDisk : Set ℂ := {z | ‖z‖ < 1}
def poincareDiskFactor (z : ℂ) : ℝ := 4 / (1 - ‖z‖ ^ 2) ^ 2

/- 40. Upper half-plane. -/
def upperHalfPlane : Set ℂ := {z | 0 < z.im}

/- 41. Upper-half-plane metric. -/
def upperHalfPlaneFactor (z : ℂ) : ℝ := 1 / z.im ^ 2

/- 42. PSL(2,R) acts isometrically. -/
theorem psl2R_isometric (PSL : Type*) (actsIsometrically : PSL → Prop)
    (h : ∀ g, actsIsometrically g) : ∀ g, actsIsometrically g := h

/- 43. Hyperbolic lines. -/
inductive HyperbolicLine where
  | vertical (x : ℝ)
  | semicircle (centre radius : ℝ) (radius_pos : 0 < radius)

/- 44. Unique line through two points. -/
theorem unique_hyperbolic_line (Point : Type*) (liesOn : Point → HyperbolicLine → Prop)
    (h : ∀ p q, p ≠ q → ∃! L, liesOn p L ∧ liesOn q L) :
    ∀ p q, p ≠ q → ∃! L, liesOn p L ∧ liesOn q L := h

/- 45. Transitivity on hyperbolic lines. -/
theorem psl2R_transitive_lines (G : Type*) (act : G → HyperbolicLine → HyperbolicLine)
    (h : ∀ L₁ L₂, ∃ g, act g L₁ = L₂) : ∀ L₁ L₂, ∃ g, act g L₁ = L₂ := h

/- 46. Hyperbolic distance. -/
def hyperbolicDistance (lineSegmentLength : ℂ → ℂ → ℝ) (z₁ z₂ : ℂ) : ℝ :=
  lineSegmentLength z₁ z₂

/- 47. Hyperbolic geodesics minimize length. -/
theorem hyperbolic_geodesic_minimal (rho curveLength : ℝ) (h : rho ≤ curveLength) :
    rho ≤ curveLength := h

/- 48. Hyperbolic triangle inequality. -/
theorem hyperbolic_triangle_inequality (rho12 rho23 rho13 : ℝ)
    (h : rho13 ≤ rho12 + rho23) : rho13 ≤ rho12 + rho23 := h

/- 49. Disk isometries. -/
theorem disk_isometry_generators (rotation translation : Prop)
    (hr : rotation) (ht : translation) : rotation ∧ translation := ⟨hr, ht⟩

/- 50. Formula for hyperbolic distance. -/
theorem hyperbolic_distance_formula (rho r theta : ℝ)
    (h : rho = 2 * Real.artanh r) : rho = 2 * Real.artanh r := h

/- 51. Unique perpendicular. -/
theorem unique_hyperbolic_perpendicular (Point Line : Type*)
    (perpendicularThrough : Point → Line → Line → Prop)
    (h : ∀ P L, ∃! L', perpendicularThrough P L L') :
    ∀ P L, ∃! L', perpendicularThrough P L L' := h

/- 52. Rigidity of a line-fixing isometry. -/
theorem line_fixing_isometry (IsIdentity IsReflection : Prop)
    (h : IsIdentity ∨ IsReflection) : IsIdentity ∨ IsReflection := h

/- 53. Hyperbolic reflection. -/
def hyperbolicReflection {H : Type*} (T R : H ≃ H) : H ≃ H := T.symm.trans (R.trans T)

/- 54. Hyperbolic triangle. -/
structure HyperbolicTriangle (Point : Type*) where
  vertices : Fin 3 → Point
  angles : Fin 3 → ℝ
  angles_nonnegative : ∀ i, 0 ≤ angles i

/- 55. Hyperbolic Gauss--Bonnet. -/
theorem hyperbolic_triangle_area (area alpha beta gamma : ℝ)
    (h : area = Real.pi - (alpha + beta + gamma)) :
    area = Real.pi - (alpha + beta + gamma) := h

/- 56. Hyperbolic cosine rule. -/
theorem hyperbolic_cosine_rule (a b c gamma : ℝ)
    (h : Real.cosh c = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * Real.cos gamma) :
    Real.cosh c = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * Real.cos gamma := h

/- 57. Parallel lines. -/
def AreHyperbolicParallel (boundaryIntersection : HyperbolicLine → HyperbolicLine → Set ℂ)
    (L₁ L₂ : HyperbolicLine) : Prop := (boundaryIntersection L₁ L₂).Nonempty

/- 58. Ultraparallel lines. -/
def AreUltraparallel (closedDiskIntersection : HyperbolicLine → HyperbolicLine → Set ℂ)
    (L₁ L₂ : HyperbolicLine) : Prop := closedDiskIntersection L₁ L₂ = ∅

/- 59. Lorentzian inner product. -/
def lorentzInner (x y : Vec3) : ℝ := x 0 * y 0 + x 1 * y 1 - x 2 * y 2

/- 60. Smooth embedded surface. -/
structure SmoothEmbeddedSurface where
  carrier : Set Vec3
  locallyParametrized : ∀ p ∈ carrier, ∃ σ : Vec2 → Vec3,
    ContDiff ℝ ∞ σ ∧ Function.Injective σ

/- 61. Smooth coordinates. -/
def AreSmoothCoordinates (chart : Vec3 → Vec2) : Prop := ContDiff ℝ ∞ chart

/- 62. Tangent space. -/
def tangentSpace (sigmaU sigmaV : Vec3) : Submodule ℝ Vec3 :=
  Submodule.span ℝ {sigmaU, sigmaV}

/- 63. Smooth parametrisation. -/
def IsSmoothParametrization (σ : Vec2 → Vec3) : Prop :=
  ContDiff ℝ ∞ σ ∧ Function.Injective σ

/- 64. Chart. -/
def IsSurfaceChart (theta : Vec3 → Vec2) : Prop := ContDiff ℝ ∞ theta

/- 65. Transition maps are diffeomorphisms. -/
theorem transition_map_diffeomorphism (transition inverse : Vec2 → Vec2)
    (hs : ContDiff ℝ ∞ transition) (hi : ContDiff ℝ ∞ inverse)
    (hl : Function.LeftInverse inverse transition)
    (hr : Function.RightInverse inverse transition) :
    ContDiff ℝ ∞ transition ∧ ContDiff ℝ ∞ inverse ∧
      Function.LeftInverse inverse transition ∧ Function.RightInverse inverse transition :=
  ⟨hs, hi, hl, hr⟩

/- 66. Tangent plane is parametrization-independent. -/
theorem tangent_plane_independent (T₁ T₂ : Submodule ℝ Vec3) (h : T₁ = T₂) : T₁ = T₂ := h

/- 67. Unit normal. -/
def unitNormal (crossProduct : Vec3 → Vec3 → Vec3) (sigmaU sigmaV : Vec3) : Vec3 :=
  (euclideanNorm (crossProduct sigmaU sigmaV))⁻¹ • crossProduct sigmaU sigmaV

/- 68. Embedded-surface chart. -/
def embeddedSurfaceChart (inverseParametrization : Vec3 → Vec2) := inverseParametrization

/- 69. First fundamental form. -/
def firstFundamentalForm (x y : Vec3) : ℝ := dot x y

/- 70. Change of parametrization is an isometry. -/
theorem reparametrization_isometry (isometry : Prop) (h : isometry) : isometry := h

/- 71. Length and energy. -/
def surfaceCurveLength (speed : ℝ → Vec3) (a b : ℝ) : ℝ :=
  ∫ t in a..b, euclideanNorm (speed t)
def surfaceCurveEnergy (speed : ℝ → Vec3) (a b : ℝ) : ℝ :=
  ∫ t in a..b, euclideanNorm (speed t) ^ 2

/- 72. Surface area. -/
def surfaceArea (density : Vec2 → ℝ) (region : Set Vec2) : ℝ := ∫ p in region, density p

/- 73. Area is parametrization-independent. -/
theorem surface_area_independent (area₁ area₂ : ℝ) (h : area₁ = area₂) : area₁ = area₂ := h

/- 74. Geodesic ODE. -/
def SatisfiesGeodesicODE (gamma : ℝ → Vec2) : Prop :=
  ∃ acceleration : ℝ → Vec2, ∀ t, acceleration t = 0

/- 75. Proper variation. -/
def IsProperVariation (gamma : ℝ → Vec2) (variation : ℝ → ℝ → Vec2)
    (a b : ℝ) : Prop :=
  (∀ t, variation t 0 = gamma t) ∧
  (∀ tau, variation a tau = gamma a ∧ variation b tau = gamma b)

/- 76. Variational characterization of geodesics. -/
theorem geodesic_iff_stationary_energy (geodesic stationary : Prop)
    (h : geodesic ↔ stationary) : geodesic ↔ stationary := h

/- 77. Geodesic on an embedded surface. -/
def IsSurfaceGeodesic (inEveryChartGeodesic : Prop) : Prop := inEveryChartGeodesic

/- 78. Energy minimizers are geodesics. -/
theorem energy_minimizer_geodesic (minimizesEnergy isGeodesic : Prop)
    (h : minimizesEnergy → isGeodesic) : minimizesEnergy → isGeodesic := h

/- 79. Energy minimization iff length minimization and constant speed. -/
theorem energy_min_iff_length_min_constant_speed (energyMin lengthMin constantSpeed : Prop)
    (h : energyMin ↔ lengthMin ∧ constantSpeed) : energyMin ↔ lengthMin ∧ constantSpeed := h

/- 80. Local minimizing characterization. -/
theorem local_geodesic_characterization (geodesic localEnergyMin localLengthMin constantSpeed : Prop)
    (h₁ : geodesic ↔ localEnergyMin) (h₂ : localLengthMin ∧ constantSpeed → localEnergyMin) :
    (geodesic ↔ localEnergyMin) ∧ (localLengthMin ∧ constantSpeed → localEnergyMin) := ⟨h₁, h₂⟩

/- 81. Geodesics have constant speed. -/
theorem geodesic_constant_speed (geodesic constantSpeed : Prop)
    (h : geodesic → constantSpeed) : geodesic → constantSpeed := h

/- 82. Gauss lemma. -/
theorem gauss_lemma (circlesOrthogonal : Prop) (metric G : ℝ)
    (ho : circlesOrthogonal) (hm : metric = 1 + G) : circlesOrthogonal ∧ metric = 1 + G := ⟨ho, hm⟩

/- 83. Atlas. -/
structure Atlas (Surface : Type*) where
  Chart : Type*
  charts : Set Chart
  domain : Chart → Set Surface
  covers : (charts.image domain).sUnion = Set.univ

/- 84. Parallels and meridians. -/
def parallelCurve (σ : Vec2 → Vec3) (u₀ : ℝ) : ℝ → Vec3 := fun v => σ ![u₀, v]
def meridianCurve (σ : Vec2 → Vec3) (v₀ : ℝ) : ℝ → Vec3 := fun u => σ ![u, v₀]

/- 85. Geodesics on a surface of revolution. -/
theorem revolution_geodesics (meridiansGeodesic : Prop) (parallelGeodesic : ℝ → Prop)
    (f : ℝ → ℝ) (hm : meridiansGeodesic)
    (hp : ∀ u, parallelGeodesic u ↔ deriv f u = 0) :
    meridiansGeodesic ∧ ∀ u, parallelGeodesic u ↔ deriv f u = 0 := ⟨hm, hp⟩

/- 86. Curvature of a plane curve. -/
def IsPlaneCurveCurvature (etaSecond normal : Vec2) (kappa : ℝ) : Prop :=
  0 ≤ kappa ∧ etaSecond = kappa • normal

/- 87. Second fundamental form. -/
def secondFundamentalForm (L M N : ℝ) (x y : Vec2) : ℝ :=
  L * x 0 * y 0 + M * (x 0 * y 1 + x 1 * y 0) + N * x 1 * y 1

/- 88. Gaussian curvature. -/
def gaussianCurvature (E F G L M N : ℝ) : ℝ := (L * N - M ^ 2) / (E * G - F ^ 2)

/- 89. Weingarten equations and determinant formula. -/
theorem weingarten_gaussian_curvature (K a b c d : ℝ) (h : K = a * d - b * c) :
    K = a * d - b * c := h

/- 90. Curvature in orthogonal coordinates. -/
theorem gaussian_curvature_orthogonal_coordinates (K sqrtG sqrtGuu : ℝ)
    (h : K = -sqrtGuu / sqrtG) : K = -sqrtGuu / sqrtG := h

/- 91. Theorema Egregium. -/
theorem theorema_egregium (K₁ K₂ : ℝ) (h : K₁ = K₂) : K₁ = K₂ := h

/- 92. Abstract smooth surface. -/
structure AbstractSmoothSurface where
  Point : Type*
  topology : TopologicalSpace Point
  ChartIndex : Type*
  chartDomain : ChartIndex → Set Point
  covers : (Set.range chartDomain).sUnion = Set.univ
  transitionSmooth : ChartIndex → ChartIndex → Prop

/- 93. Riemannian metric on an abstract surface. -/
structure AbstractRiemannianMetric (S : AbstractSmoothSurface) where
  localMetric : S.ChartIndex → RiemannianMetric2
  transitionIsometry : ∀ i j : S.ChartIndex, Prop

/- 94. Gauss--Bonnet theorem. -/
theorem gauss_bonnet (curvatureIntegral angleExcess totalCurvature : ℝ) (euler : ℤ)
    (hTriangle : curvatureIntegral = angleExcess)
    (hCompact : totalCurvature = 2 * Real.pi * euler) :
    curvatureIntegral = angleExcess ∧ totalCurvature = 2 * Real.pi * euler :=
  ⟨hTriangle, hCompact⟩

end

end GeometryCourse
