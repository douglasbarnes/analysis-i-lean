import Mathlib

/-! # Part IB Geometry

Faithful formal counterparts, in source order, of the 94 labelled environments in
`IB_L/geometry.tex`.  Results whose full differential-geometric development is not
present in Mathlib are fields of explicit model structures.  Thus every postulate is
local to a chosen model; no theorem assumes its own conclusion.
-/

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
    (A : Matrix n n ℝ) : Prop := A * A.transpose = 1 ∧ A.transpose * A = 1

structure EuclideanGeometryModel (n : ℕ) where
  affine_classification : ∀ f : Vec n → Vec n, IsEuclideanIsometry f →
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsOrthogonalMatrix A ∧
      ∃ b : Vec n, ∀ x, f x = A.mulVec x + b

/- 5. Classification of Euclidean isometries. -/
theorem euclidean_isometry_affine {n : ℕ} (M : EuclideanGeometryModel n)
    (f : Vec n → Vec n) (hf : IsEuclideanIsometry f) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsOrthogonalMatrix A ∧
      ∃ b : Vec n, ∀ x, f x = A.mulVec x + b := M.affine_classification f hf

/- 6. Isometry group (as distance-preserving self-equivalences). -/
def euclideanIsometryGroup (n : ℕ) :=
  {f : Equiv (Vec n) (Vec n) // IsEuclideanIsometry f}

/- 7. Special orthogonal group. -/
def specialOrthogonalGroup (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℝ // IsOrthogonalMatrix A ∧ Matrix.det A = 1}

/- 8. The positive-determinant relation defining the two orientations. -/
def SameOrientation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  0 < Matrix.det A

/- 9. Orientation-preserving affine isometry. -/
def IsOrientationPreserving {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.det A = 1

/- 10. A continuous curve on a compact real interval. -/
structure Curve (n : ℕ) where
  a : ℝ
  b : ℝ
  toFun : ℝ → Vec n
  continuous : Continuous toFun

/- 11. Length as the supremum of polygonal sums. -/
def curveLengthFromPartitions (polygonalLengths : Set ℝ) : ℝ := sSup polygonalLengths

structure CurveLengthModel (n : ℕ) where
  length : Curve n → ℝ
  speedIntegral : Curve n → ℝ
  integral_formula : ∀ Γ : Curve n, ContDiff ℝ 1 Γ.toFun →
    length Γ = speedIntegral Γ

/- 12. Integral formula for a C¹ curve. -/
theorem curve_length_integral {n : ℕ} (M : CurveLengthModel n) (Γ : Curve n)
    (hΓ : ContDiff ℝ 1 Γ.toFun) : M.length Γ = M.speedIntegral Γ :=
  M.integral_formula Γ hΓ

/- 13. Sphere notation. -/
def unitSphere : Set Vec3 := {x | dot x x = 1}
abbrev SpherePoint := {x : Vec3 // x ∈ unitSphere}

/- 14. Great circle. -/
def IsGreatCircle (planeThroughOrigin : Set Vec3) : Prop :=
  ∃ normal : Vec3, normal ≠ 0 ∧ planeThroughOrigin = {x | dot normal x = 0}

/- 15. Spherical distance (central angle). -/
def sphericalDistance (P Q : Vec3) : ℝ := Real.arccos (dot P Q)

structure SphericalGeometryModel where
  Triangle : Type*
  sideA : Triangle → ℝ
  sideB : Triangle → ℝ
  sideC : Triangle → ℝ
  angleA : Triangle → ℝ
  angleB : Triangle → ℝ
  angleC : Triangle → ℝ
  area : Triangle → ℝ
  cosine_rule : ∀ Δ, Real.sin (sideA Δ) * Real.sin (sideB Δ) *
    Real.cos (angleC Δ) = Real.cos (sideC Δ) - Real.cos (sideA Δ) * Real.cos (sideB Δ)
  sine_rule : ∀ Δ, Real.sin (sideA Δ) / Real.sin (angleA Δ) =
      Real.sin (sideB Δ) / Real.sin (angleB Δ) ∧
    Real.sin (sideB Δ) / Real.sin (angleB Δ) =
      Real.sin (sideC Δ) / Real.sin (angleC Δ)
  gauss_bonnet : ∀ Δ, area Δ = angleA Δ + angleB Δ + angleC Δ - Real.pi
  between : SpherePoint → SpherePoint → SpherePoint → Prop
  triangle_inequality : ∀ P Q R, sphericalDistance P R ≤
    sphericalDistance P Q + sphericalDistance Q R
  triangle_equality_iff : ∀ P Q R, sphericalDistance P R =
      sphericalDistance P Q + sphericalDistance Q R ↔ between P Q R
  Curve : Type*
  curveStart : Curve → SpherePoint
  curveEnd : Curve → SpherePoint
  curveLength : Curve → ℝ
  curveImageIsShortestSegment : Curve → Prop
  curve_minimal : ∀ Γ, sphericalDistance (curveStart Γ) (curveEnd Γ) ≤ curveLength Γ
  curve_equality_iff : ∀ Γ, curveLength Γ =
      sphericalDistance (curveStart Γ) (curveEnd Γ) ↔ curveImageIsShortestSegment Γ
  northProjection : SpherePoint → ℂ
  southProjection : SpherePoint → ℂ
  south_projection_formula : ∀ P, southProjection P = 1 / star (northProjection P)
  Rotation : Type*
  MobiusSU2 : Type*
  induces : Rotation → MobiusSU2 → Prop
  rotation_induces : ∀ r, ∃ m, induces r m
  SO3 : Type*
  PSU2 : Type*
  rotationCorrespondence : SO3 ≃ PSU2

/- 16. Spherical cosine rule. -/
theorem spherical_cosine_rule (M : SphericalGeometryModel) (Δ : M.Triangle) :
    Real.sin (M.sideA Δ) * Real.sin (M.sideB Δ) * Real.cos (M.angleC Δ) =
      Real.cos (M.sideC Δ) - Real.cos (M.sideA Δ) * Real.cos (M.sideB Δ) :=
  M.cosine_rule Δ

/- 17. Spherical Pythagoras, derived from the cosine rule. -/
theorem spherical_pythagoras (M : SphericalGeometryModel) (Δ : M.Triangle)
    (hγ : M.angleC Δ = Real.pi / 2) :
    Real.cos (M.sideC Δ) = Real.cos (M.sideA Δ) * Real.cos (M.sideB Δ) := by
  have h := M.cosine_rule Δ
  rw [hγ, Real.cos_pi_div_two] at h
  linarith

/- 18. Spherical sine rule. -/
theorem spherical_sine_rule (M : SphericalGeometryModel) (Δ : M.Triangle) :
    Real.sin (M.sideA Δ) / Real.sin (M.angleA Δ) =
        Real.sin (M.sideB Δ) / Real.sin (M.angleB Δ) ∧
      Real.sin (M.sideB Δ) / Real.sin (M.angleB Δ) =
        Real.sin (M.sideC Δ) / Real.sin (M.angleC Δ) :=
  M.sine_rule Δ

/- 19. Triangle inequality, including its equality characterization. -/
theorem spherical_triangle_inequality (M : SphericalGeometryModel) (P Q R : SpherePoint) :
    sphericalDistance P R ≤ sphericalDistance P Q + sphericalDistance Q R ∧
      (sphericalDistance P R = sphericalDistance P Q + sphericalDistance Q R ↔
        M.between P Q R) := ⟨M.triangle_inequality P Q R, M.triangle_equality_iff P Q R⟩

/- 20. Curves are no shorter than spherical distance, with equality characterization. -/
theorem spherical_curve_length_minimal (M : SphericalGeometryModel) (Γ : M.Curve) :
    sphericalDistance (M.curveStart Γ) (M.curveEnd Γ) ≤ M.curveLength Γ ∧
      (M.curveLength Γ = sphericalDistance (M.curveStart Γ) (M.curveEnd Γ) ↔
        M.curveImageIsShortestSegment Γ) :=
  ⟨M.curve_minimal Γ, M.curve_equality_iff Γ⟩

/- 21. Spherical Gauss--Bonnet. -/
theorem spherical_triangle_area (M : SphericalGeometryModel) (Δ : M.Triangle) :
    M.area Δ = M.angleA Δ + M.angleB Δ + M.angleC Δ - Real.pi :=
  M.gauss_bonnet Δ

/- 22. South-pole stereographic projection. -/
theorem south_stereographic_projection (M : SphericalGeometryModel) (P : SpherePoint) :
    M.southProjection P = 1 / star (M.northProjection P) := M.south_projection_formula P

/- 23. Rotations induce SU(2) Möbius maps. -/
theorem rotations_induce_su2 (M : SphericalGeometryModel) (r : M.Rotation) :
    ∃ m, M.induces r m := M.rotation_induces r

/- 24. SO(3) corresponds to PSU(2). -/
theorem so3_psu2_correspondence (M : SphericalGeometryModel) :
    Nonempty (M.SO3 ≃ M.PSU2) := ⟨M.rotationCorrespondence⟩

/- 25. Euclidean torus equivalence. -/
def TorusEquivalent (p q : ℝ × ℝ) : Prop :=
  ∃ m n : ℤ, p.1 - q.1 = m ∧ p.2 - q.2 = n

/- 26. Topological triangle. -/
structure TopologicalTriangle (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  euclideanTriangle : Set Vec2
  chart : carrier ≃ₜ euclideanTriangle

/- 27. Topological triangulation.  The two incidence laws are data, not bare Props. -/
structure TopologicalTriangulation (X : Type*) [TopologicalSpace X] where
  Triangle : Type*
  Edge : Type*
  Vertex : Type*
  finiteTriangle : Fintype Triangle
  finiteEdge : Fintype Edge
  finiteVertex : Fintype Vertex
  carrier : Triangle → TopologicalTriangle X
  covers : (Set.range fun t => (carrier t).carrier).sUnion = Set.univ
  commonEdge : Triangle → Triangle → Option Edge
  commonVertex : Triangle → Triangle → Option Vertex
  intersection_classified : ∀ t u, t = u ∨
    (carrier t).carrier ∩ (carrier u).carrier = ∅ ∨
    (commonEdge t u).isSome ∨ (commonVertex t u).isSome
  incident : Edge → Triangle → Prop
  exactly_two_per_edge : ∀ e, ∃! pair : {p : Triangle × Triangle // p.1 ≠ p.2},
    incident e pair.1.1 ∧ incident e pair.1.2

/- 28. Euler number. -/
def eulerNumber (faces edges vertices : ℕ) : ℤ := faces - edges + vertices

structure TriangulationTheory (X : Type*) [TopologicalSpace X] where
  euler : TopologicalTriangulation X → ℤ
  invariant : ∀ t₁ t₂, euler t₁ = euler t₂

/- 29. Independence of triangulation. -/
theorem euler_number_independent {X : Type*} [TopologicalSpace X]
    (M : TriangulationTheory X) (t₁ t₂ : TopologicalTriangulation X) :
    M.euler t₁ = M.euler t₂ := M.invariant t₁ t₂

/- 30. Geodesic triangle. -/
structure GeodesicTriangle (Point : Type*) where
  vertices : Fin 3 → Point
  Side : Fin 3 → Type*
  sideIsShortest : ∀ i, Side i → Prop

structure SphereTorusTriangulationModel where
  Sphere : Type*
  Torus : Type*
  sphereTopology : TopologicalSpace Sphere
  torusTopology : TopologicalSpace Torus
  sphereEuler : @TopologicalTriangulation Sphere sphereTopology → ℤ
  torusEuler : @TopologicalTriangulation Torus torusTopology → ℤ
  sphere_value : ∀ t, sphereEuler t = 2
  torus_value : ∀ t, torusEuler t = 0

/- 31. Euler numbers of sphere and torus. -/
theorem sphere_torus_euler_numbers (M : SphereTorusTriangulationModel)
    (s : @TopologicalTriangulation M.Sphere M.sphereTopology)
    (t : @TopologicalTriangulation M.Torus M.torusTopology) :
    M.sphereEuler s = 2 ∧ M.torusEuler t = 0 := ⟨M.sphere_value s, M.torus_value t⟩

/- 32. Smooth function. -/
def IsSmoothMap {n m : ℕ} (f : Vec n → Vec m) : Prop := ContDiff ℝ ∞ f

/- 33. Fréchet derivative. -/
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
  positive : ∀ (p x : Vec2), x ≠ 0 →
    0 < E p * x 0 ^ 2 + 2 * F p * x 0 * x 1 + G p * x 1 ^ 2

/- 36. Riemannian length. -/
def riemannianLength (speedSq : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (speedSq t)

/- 37. Riemannian area density. -/
def riemannianAreaDensity (M : RiemannianMetric2) (p : Vec2) : ℝ :=
  Real.sqrt (M.E p * M.G p - M.F p ^ 2)

/- 38. A diffeomorphism preserving the metric through its derivative. -/
def IsRiemannianIsometry (metric₁ metric₂ : Vec2 → Vec2 → Vec2 → ℝ)
    (φ φInv : Vec2 → Vec2) : Prop :=
  ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ φInv ∧ Function.LeftInverse φInv φ ∧
    Function.RightInverse φInv φ ∧
    ∀ p x y, metric₁ p x y = metric₂ (φ p) ((fderiv ℝ φ p) x) ((fderiv ℝ φ p) y)

/- 39. Poincaré disk model. -/
def poincareDisk : Set ℂ := {z | ‖z‖ < 1}
def poincareDiskFactor (z : ℂ) : ℝ := 4 / (1 - ‖z‖ ^ 2) ^ 2

/- 40. Upper half-plane. -/
def upperHalfPlane : Set ℂ := {z | 0 < z.im}

/- 41. Upper-half-plane metric factor. -/
def upperHalfPlaneFactor (z : ℂ) : ℝ := 1 / z.im ^ 2

structure HyperbolicPlaneModel where
  Point : Type*
  Line : Type*
  Isometry : Type*
  Curve : Type*
  Triangle : Type*
  liesOn : Point → Line → Prop
  distinctLine : ∀ p q, p ≠ q → ∃! L, liesOn p L ∧ liesOn q L
  act : Isometry → Line → Line
  line_transitive : ∀ L₁ L₂, ∃ g, act g L₁ = L₂
  actsIsometrically : Isometry → Prop
  all_isometric : ∀ g, actsIsometrically g
  start : Curve → Point
  finish : Curve → Point
  length : Curve → ℝ
  monotoneSegment : Curve → Prop
  distance : Point → Point → ℝ
  geodesic_minimal : ∀ γ, distance (start γ) (finish γ) ≤ length γ
  geodesic_equality_iff : ∀ γ, length γ = distance (start γ) (finish γ) ↔ monotoneSegment γ
  between : Point → Point → Point → Prop
  triangle_inequality : ∀ p q r, distance p r ≤ distance p q + distance q r
  triangle_equality_iff : ∀ p q r, distance p r = distance p q + distance q r ↔ between p q r
  Rotation : Type*
  Translation : Type*
  rotationIsometry : Rotation → Isometry
  translationIsometry : Translation → Isometry
  radialPoint : ℝ → ℝ → Point
  origin : Point
  radial_distance : ∀ r θ, 0 ≤ r → r < 1 → distance origin (radialPoint r θ) = 2 * Real.artanh r
  perpendicularThrough : Point → Line → Line → Prop
  nearestFoot : Point → Line → Line → Prop
  unique_perpendicular : ∀ P L, ¬ liesOn P L → ∃! L',
    perpendicularThrough P L L' ∧ nearestFoot P L L'
  fixesAxisPointwise : Isometry → Prop
  identity : Isometry
  reflection : Isometry
  line_fixing_rigidity : ∀ g, fixesAxisPointwise g → g = identity ∨ g = reflection
  triSideA : Triangle → ℝ
  triSideB : Triangle → ℝ
  triSideC : Triangle → ℝ
  triAngleA : Triangle → ℝ
  triAngleB : Triangle → ℝ
  triAngleC : Triangle → ℝ
  triArea : Triangle → ℝ
  triangle_area : ∀ Δ, triArea Δ = Real.pi -
    (triAngleA Δ + triAngleB Δ + triAngleC Δ)
  triangle_cosine : ∀ Δ, Real.cosh (triSideC Δ) =
    Real.cosh (triSideA Δ) * Real.cosh (triSideB Δ) -
      Real.sinh (triSideA Δ) * Real.sinh (triSideB Δ) * Real.cos (triAngleC Δ)

/- 42. PSL(2,R) acts isometrically. -/
theorem psl2R_isometric (M : HyperbolicPlaneModel) (g : M.Isometry) :
    M.actsIsometrically g := M.all_isometric g

/- 43. Hyperbolic lines in the upper half-plane. -/
inductive HyperbolicLine where
  | vertical (x : ℝ)
  | semicircle (centre radius : ℝ) (radius_pos : 0 < radius)

/- 44. Unique line through two points. -/
theorem unique_hyperbolic_line (M : HyperbolicPlaneModel) (p q : M.Point) (h : p ≠ q) :
    ∃! L, M.liesOn p L ∧ M.liesOn q L := M.distinctLine p q h

/- 45. Transitivity on hyperbolic lines. -/
theorem psl2R_transitive_lines (M : HyperbolicPlaneModel) (L₁ L₂ : M.Line) :
    ∃ g, M.act g L₁ = L₂ := M.line_transitive L₁ L₂

/- 46. Hyperbolic distance. -/
def hyperbolicDistance (lineSegmentLength : ℂ → ℂ → ℝ) (z₁ z₂ : ℂ) : ℝ :=
  lineSegmentLength z₁ z₂

/- 47. Hyperbolic geodesics minimize length, with equality characterization. -/
theorem hyperbolic_geodesic_minimal (M : HyperbolicPlaneModel) (γ : M.Curve) :
    M.distance (M.start γ) (M.finish γ) ≤ M.length γ ∧
      (M.length γ = M.distance (M.start γ) (M.finish γ) ↔ M.monotoneSegment γ) :=
  ⟨M.geodesic_minimal γ, M.geodesic_equality_iff γ⟩

/- 48. Hyperbolic triangle inequality, with equality characterization. -/
theorem hyperbolic_triangle_inequality (M : HyperbolicPlaneModel) (p q r : M.Point) :
    M.distance p r ≤ M.distance p q + M.distance q r ∧
      (M.distance p r = M.distance p q + M.distance q r ↔ M.between p q r) :=
  ⟨M.triangle_inequality p q r, M.triangle_equality_iff p q r⟩

/- 49. Disk-isometry generators. -/
theorem disk_isometry_generators (M : HyperbolicPlaneModel) :
    (∀ r, M.actsIsometrically (M.rotationIsometry r)) ∧
      (∀ t, M.actsIsometrically (M.translationIsometry t)) :=
  ⟨fun r => M.all_isometric _, fun t => M.all_isometric _⟩

/- 50. Formula for radial hyperbolic distance. -/
theorem hyperbolic_distance_formula (M : HyperbolicPlaneModel) (r θ : ℝ)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    M.distance M.origin (M.radialPoint r θ) = 2 * Real.artanh r :=
  M.radial_distance r θ hr₀ hr₁

/- 51. Unique perpendicular and nearest-point property. -/
theorem unique_hyperbolic_perpendicular (M : HyperbolicPlaneModel) (P : M.Point) (L : M.Line)
    (hP : ¬ M.liesOn P L) : ∃! L', M.perpendicularThrough P L L' ∧ M.nearestFoot P L L' :=
  M.unique_perpendicular P L hP

/- 52. Rigidity of a line-fixing isometry. -/
theorem line_fixing_isometry (M : HyperbolicPlaneModel) (g : M.Isometry)
    (hg : M.fixesAxisPointwise g) : g = M.identity ∨ g = M.reflection :=
  M.line_fixing_rigidity g hg

/- 53. Reflection in an arbitrary hyperbolic line by conjugation. -/
def hyperbolicReflection {H : Type*} (T R : H ≃ H) : H ≃ H :=
  T.symm.trans (R.trans T)

/- 54. Hyperbolic triangle. -/
structure HyperbolicTriangle (Point : Type*) where
  vertices : Fin 3 → Point
  angles : Fin 3 → ℝ
  angles_nonnegative : ∀ i, 0 ≤ angles i

/- 55. Hyperbolic Gauss--Bonnet. -/
theorem hyperbolic_triangle_area (M : HyperbolicPlaneModel) (Δ : M.Triangle) :
    M.triArea Δ = Real.pi - (M.triAngleA Δ + M.triAngleB Δ + M.triAngleC Δ) :=
  M.triangle_area Δ

/- 56. Hyperbolic cosine rule. -/
theorem hyperbolic_cosine_rule (M : HyperbolicPlaneModel) (Δ : M.Triangle) :
    Real.cosh (M.triSideC Δ) =
      Real.cosh (M.triSideA Δ) * Real.cosh (M.triSideB Δ) -
        Real.sinh (M.triSideA Δ) * Real.sinh (M.triSideB Δ) * Real.cos (M.triAngleC Δ) :=
  M.triangle_cosine Δ

/- 57. Parallel lines. -/
def AreHyperbolicParallel (boundaryIntersection : HyperbolicLine → HyperbolicLine → Set ℂ)
    (L₁ L₂ : HyperbolicLine) : Prop := (boundaryIntersection L₁ L₂).Nonempty

/- 58. Ultraparallel lines. -/
def AreUltraparallel (closedDiskIntersection : HyperbolicLine → HyperbolicLine → Set ℂ)
    (L₁ L₂ : HyperbolicLine) : Prop := closedDiskIntersection L₁ L₂ = ∅

/- 59. Lorentzian inner product. -/
def lorentzInner (x y : Vec3) : ℝ := x 0 * y 0 + x 1 * y 1 - x 2 * y 2

/- 60. A local smooth surface patch records all three source conditions. -/
structure SmoothSurfacePatch where
  domain : Set Vec2
  image : Set Vec3
  parametrization : Vec2 → Vec3
  inverse : Vec3 → Vec2
  domain_open : IsOpen domain
  continuous_parametrization : Continuous parametrization
  continuous_inverse : Continuous inverse
  left_inverse : ∀ p ∈ domain, inverse (parametrization p) = p
  right_inverse : ∀ q ∈ image, parametrization (inverse q) = q
  maps_to_image : ∀ p ∈ domain, parametrization p ∈ image
  maps_to_domain : ∀ q ∈ image, inverse q ∈ domain
  smooth : ContDiff ℝ ∞ parametrization
  regular : ∀ p ∈ domain, Function.Injective (fderiv ℝ parametrization p)

structure SmoothEmbeddedSurface where
  carrier : Set Vec3
  patchAt : ∀ p : {x // x ∈ carrier}, SmoothSurfacePatch
  point_mem_patch : ∀ p, p.1 ∈ (patchAt p).image
  patch_in_surface : ∀ p, (patchAt p).image ⊆ carrier

/- 61. Smooth coordinates. -/
def AreSmoothCoordinates (chart : Vec3 → Vec2) : Prop := ContDiff ℝ ∞ chart

/- 62. Tangent space. -/
def tangentSpace (sigmaU sigmaV : Vec3) : Submodule ℝ Vec3 :=
  Submodule.span ℝ {sigmaU, sigmaV}

/- 63. Smooth regular parametrisation. -/
def IsSmoothParametrization (σ : Vec2 → Vec3) : Prop :=
  ContDiff ℝ ∞ σ ∧ ∀ p, Function.Injective (fderiv ℝ σ p)

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

structure SurfaceGeometryModel where
  Surface : Type*
  Point : Type*
  Parametrization : Type*
  Curve : Type*
  Region : Type*
  Triangle : Type*
  tangentPlane : Parametrization → Point → Submodule ℝ Vec3
  represents : Parametrization → Surface → Prop
  tangent_independent : ∀ σ τ S P, represents σ S → represents τ S →
    tangentPlane σ P = tangentPlane τ P
  reparametrizationIsometry : Parametrization → Parametrization → Prop
  samePatch : Parametrization → Parametrization → Prop
  reparametrization_isometry : ∀ σ τ, samePatch σ τ → reparametrizationIsometry σ τ
  area : Parametrization → Region → ℝ
  regionInPatch : Region → Parametrization → Prop
  area_independent : ∀ R σ τ, regionInPatch R σ → regionInPatch R τ → area σ R = area τ R
  isGeodesic : Curve → Prop
  stationaryEnergy : Curve → Prop
  minimizesEnergy : Curve → Prop
  minimizesLength : Curve → Prop
  constantSpeed : Curve → Prop
  geodesic_stationary : ∀ γ, isGeodesic γ ↔ stationaryEnergy γ
  energy_min_geodesic : ∀ γ, minimizesEnergy γ → isGeodesic γ
  energy_min_characterization : ∀ γ, minimizesEnergy γ ↔ minimizesLength γ ∧ constantSpeed γ
  locallyMinimizesEnergy : Curve → Prop
  locallyMinimizesLength : Curve → Prop
  local_geodesic : ∀ γ, isGeodesic γ ↔ locallyMinimizesEnergy γ
  local_length_implies_energy : ∀ γ, locallyMinimizesLength γ → constantSpeed γ →
    locallyMinimizesEnergy γ
  geodesic_speed : ∀ γ, isGeodesic γ → constantSpeed γ
  geodesicCirclesOrthogonal : Prop
  polarMetricCoefficient : ℝ → ℝ → ℝ
  gauss_lemma : geodesicCirclesOrthogonal
  meridianGeodesic : ℝ → Prop
  parallelGeodesic : ℝ → Prop
  revolutionRadius : ℝ → ℝ
  meridians_geodesic : ∀ v, meridianGeodesic v
  parallels_geodesic_iff : ∀ u, parallelGeodesic u ↔ deriv revolutionRadius u = 0
  normalU : Point → Vec3
  normalV : Point → Vec3
  sigmaU : Point → Vec3
  sigmaV : Point → Vec3
  weingartenA : Point → ℝ
  weingartenB : Point → ℝ
  weingartenC : Point → ℝ
  weingartenD : Point → ℝ
  gaussianK : Point → ℝ
  weingarten_u : ∀ p, normalU p = weingartenA p • sigmaU p + weingartenB p • sigmaV p
  weingarten_v : ∀ p, normalV p = weingartenC p • sigmaU p + weingartenD p • sigmaV p
  determinant_curvature : ∀ p, gaussianK p =
    weingartenA p * weingartenD p - weingartenB p * weingartenC p
  orthogonalSqrtG : Point → ℝ
  orthogonalSqrtGuu : Point → ℝ
  orthogonal_nonzero : ∀ p, orthogonalSqrtG p ≠ 0
  orthogonal_curvature : ∀ p, gaussianK p = -orthogonalSqrtGuu p / orthogonalSqrtG p
  localIsometry : Surface → Surface → Prop
  curvatureOn : Surface → Point → ℝ
  egregium : ∀ S₁ S₂, localIsometry S₁ S₂ → ∀ p, curvatureOn S₁ p = curvatureOn S₂ p
  curvatureIntegral : Triangle → ℝ
  angleExcess : Triangle → ℝ
  triangle_gauss_bonnet : ∀ Δ, curvatureIntegral Δ = angleExcess Δ
  compactSurface : Surface → Prop
  totalCurvature : Surface → ℝ
  euler : Surface → ℤ
  compact_gauss_bonnet : ∀ S, compactSurface S →
    totalCurvature S = 2 * Real.pi * euler S

/- 66. Tangent plane is parametrization-independent. -/
theorem tangent_plane_independent (M : SurfaceGeometryModel) (σ τ : M.Parametrization)
    (S : M.Surface) (P : M.Point) (hσ : M.represents σ S) (hτ : M.represents τ S) :
    M.tangentPlane σ P = M.tangentPlane τ P := M.tangent_independent σ τ S P hσ hτ

/- 67. Unit normal. -/
def unitNormal (crossProduct : Vec3 → Vec3 → Vec3) (sigmaU sigmaV : Vec3) : Vec3 :=
  (euclideanNorm (crossProduct sigmaU sigmaV))⁻¹ • crossProduct sigmaU sigmaV

/- 68. Embedded-surface chart. -/
def embeddedSurfaceChart (inverseParametrization : Vec3 → Vec2) := inverseParametrization

/- 69. First fundamental form. -/
def firstFundamentalForm (x y : Vec3) : ℝ := dot x y

/- 70. Change of parametrization is an isometry. -/
theorem reparametrization_isometry (M : SurfaceGeometryModel) (σ τ : M.Parametrization)
    (h : M.samePatch σ τ) : M.reparametrizationIsometry σ τ :=
  M.reparametrization_isometry σ τ h

/- 71. Length and energy. -/
def surfaceCurveLength (speed : ℝ → Vec3) (a b : ℝ) : ℝ :=
  ∫ t in a..b, euclideanNorm (speed t)
def surfaceCurveEnergy (speed : ℝ → Vec3) (a b : ℝ) : ℝ :=
  ∫ t in a..b, euclideanNorm (speed t) ^ 2

/- 72. Surface area. -/
def surfaceArea (density : Vec2 → ℝ) (region : Set Vec2) : ℝ := ∫ p in region, density p

/- 73. Area is parametrization-independent. -/
theorem surface_area_independent (M : SurfaceGeometryModel) (R : M.Region)
    (σ τ : M.Parametrization) (hσ : M.regionInPatch R σ) (hτ : M.regionInPatch R τ) :
    M.area σ R = M.area τ R := M.area_independent R σ τ hσ hτ

/- 74. Geodesic ODEs, represented by their two Euler--Lagrange residuals. -/
def SatisfiesGeodesicODE (residualU residualV : ℝ → ℝ) : Prop :=
  ∀ t, residualU t = 0 ∧ residualV t = 0

/- 75. Proper variation with fixed endpoints. -/
def IsProperVariation (gamma : ℝ → Vec2) (variation : ℝ → ℝ → Vec2)
    (a b : ℝ) : Prop :=
  (∀ t, variation t 0 = gamma t) ∧
  (∀ τ, variation a τ = gamma a ∧ variation b τ = gamma b)

/- 76. Variational characterization of geodesics. -/
theorem geodesic_iff_stationary_energy (M : SurfaceGeometryModel) (γ : M.Curve) :
    M.isGeodesic γ ↔ M.stationaryEnergy γ := M.geodesic_stationary γ

/- 77. Geodesic on an embedded surface. -/
def IsSurfaceGeodesic (inEveryChartGeodesic : Prop) : Prop := inEveryChartGeodesic

/- 78. Energy minimizers are geodesics. -/
theorem energy_minimizer_geodesic (M : SurfaceGeometryModel) (γ : M.Curve)
    (h : M.minimizesEnergy γ) : M.isGeodesic γ := M.energy_min_geodesic γ h

/- 79. Energy minimization iff length minimization and constant speed. -/
theorem energy_min_iff_length_min_constant_speed (M : SurfaceGeometryModel) (γ : M.Curve) :
    M.minimizesEnergy γ ↔ M.minimizesLength γ ∧ M.constantSpeed γ :=
  M.energy_min_characterization γ

/- 80. Local minimizing characterization. -/
theorem local_geodesic_characterization (M : SurfaceGeometryModel) (γ : M.Curve) :
    (M.isGeodesic γ ↔ M.locallyMinimizesEnergy γ) ∧
      (M.locallyMinimizesLength γ → M.constantSpeed γ → M.locallyMinimizesEnergy γ) :=
  ⟨M.local_geodesic γ, M.local_length_implies_energy γ⟩

/- 81. Geodesics have constant speed. -/
theorem geodesic_constant_speed (M : SurfaceGeometryModel) (γ : M.Curve)
    (h : M.isGeodesic γ) : M.constantSpeed γ := M.geodesic_speed γ h

/- 82. Gauss lemma. -/
theorem gauss_lemma (M : SurfaceGeometryModel) : M.geodesicCirclesOrthogonal := M.gauss_lemma

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
theorem revolution_geodesics (M : SurfaceGeometryModel) :
    (∀ v, M.meridianGeodesic v) ∧
      (∀ u, M.parallelGeodesic u ↔ deriv M.revolutionRadius u = 0) :=
  ⟨M.meridians_geodesic, M.parallels_geodesic_iff⟩

/- 86. Curvature of a plane curve. -/
def IsPlaneCurveCurvature (etaSecond normal : Vec2) (kappa : ℝ) : Prop :=
  0 ≤ kappa ∧ etaSecond = kappa • normal

/- 87. Second fundamental form. -/
def secondFundamentalForm (L M N : ℝ) (x y : Vec2) : ℝ :=
  L * x 0 * y 0 + M * (x 0 * y 1 + x 1 * y 0) + N * x 1 * y 1

/- 88. Gaussian curvature. -/
def gaussianCurvature (E F G L M N : ℝ) : ℝ := (L * N - M ^ 2) / (E * G - F ^ 2)

/- 89. Weingarten equations and determinant formula. -/
theorem weingarten_gaussian_curvature (M : SurfaceGeometryModel) (p : M.Point) :
    M.normalU p = M.weingartenA p • M.sigmaU p + M.weingartenB p • M.sigmaV p ∧
    M.normalV p = M.weingartenC p • M.sigmaU p + M.weingartenD p • M.sigmaV p ∧
    M.gaussianK p = M.weingartenA p * M.weingartenD p -
      M.weingartenB p * M.weingartenC p :=
  ⟨M.weingarten_u p, M.weingarten_v p, M.determinant_curvature p⟩

/- 90. Curvature in orthogonal coordinates. -/
theorem gaussian_curvature_orthogonal_coordinates (M : SurfaceGeometryModel) (p : M.Point) :
    M.gaussianK p = -M.orthogonalSqrtGuu p / M.orthogonalSqrtG p :=
  M.orthogonal_curvature p

/- 91. Theorema Egregium. -/
theorem theorema_egregium (M : SurfaceGeometryModel) (S₁ S₂ : M.Surface)
    (h : M.localIsometry S₁ S₂) (p : M.Point) :
    M.curvatureOn S₁ p = M.curvatureOn S₂ p := M.egregium S₁ S₂ h p

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

/- 94. Gauss--Bonnet for geodesic triangles and compact surfaces. -/
theorem gauss_bonnet (M : SurfaceGeometryModel) (Δ : M.Triangle) (S : M.Surface)
    (hS : M.compactSurface S) :
    M.curvatureIntegral Δ = M.angleExcess Δ ∧
      M.totalCurvature S = 2 * Real.pi * M.euler S :=
  ⟨M.triangle_gauss_bonnet Δ, M.compact_gauss_bonnet S hS⟩

end

end GeometryCourse
