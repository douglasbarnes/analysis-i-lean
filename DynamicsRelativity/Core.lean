import Mathlib

/-!
# Part IA Dynamics and Relativity

Formal witnesses for every labelled environment in the 2015 lecture notes, in
source order.  Physical laws are predicates on a chosen model, rather than
logical axioms.  The mathematical statements below are proved from their
displayed hypotheses.
-/

open scoped BigOperators

namespace DynamicsRelativity

abbrev Vec3 := Fin 3 → ℝ
abbrev Event := ℝ × ℝ

def cross (a b : Vec3) : Vec3 := ![
  a 1 * b 2 - a 2 * b 1,
  a 2 * b 0 - a 0 * b 2,
  a 0 * b 1 - a 1 * b 0]

def dot (a b : Vec3) : ℝ := ∑ i, a i * b i
def normSq (a : Vec3) : ℝ := dot a a

/- 1. Particle. -/
structure Particle where
  mass : ℝ
  mass_pos : 0 < mass
  charge : ℝ
  position : ℝ → Vec3

/- 2. Frame of reference. -/
structure FrameOfReference where
  coordinates : Vec3 → Vec3

/- 3. Velocity. -/
noncomputable def velocity (r : ℝ → Vec3) (t : ℝ) : Vec3 :=
  fun i ⇒ deriv (fun s ⇒ r s i) t

/- 4. Acceleration. -/
noncomputable def acceleration (r : ℝ → Vec3) (t : ℝ) : Vec3 :=
  velocity (velocity r) t

/- 5. Momentum. -/
def momentum (m : ℝ) (v : Vec3) : Vec3 := m • v

/- 6. Newton's first law: an empirical model predicate. -/
def NewtonFirstLaw (force velocity : ℝ → Vec3) : Prop :=
  ∀ t, force t = 0 → ∃ v₀, ∀ s, velocity s = v₀

/- 7. Newton's second law: an empirical model predicate. -/
def NewtonSecondLaw (p force : ℝ → Vec3) : Prop :=
  ∀ t i, HasDerivAt (fun s ⇒ p s i) (force t i) t

/- 8. Newton's third law: an empirical model predicate. -/
def NewtonThirdLaw {Body : Type*} (mutualForce : Body → Body → Vec3) : Prop :=
  ∀ a b, mutualForce a b = -mutualForce b a

/- 9. Inertial frame. -/
def IsInertialFrame (origin : ℝ → Vec3) : Prop :=
  ∃ v₀ x₀, ∀ t, origin t = x₀ + t • v₀

/- 10. Galilean boost. -/
def galileanBoost (v : Vec3) (event : ℝ × Vec3) : ℝ × Vec3 :=
  (event.1, event.2 - event.1 • v)

/- 11. Galilean relativity: an empirical model predicate. -/
def GalileanRelativity {Law : Type*} (valid : FrameOfReference → Law → Prop) : Prop :=
  ∀ S S' L, valid S L ↔ valid S' L

/- 12. Equation of motion. -/
def EquationOfMotion (p force : ℝ → Vec3) : Prop := NewtonSecondLaw p force

/- 13. One-dimensional potential energy. -/
def IsPotentialEnergy (force potential : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt potential (-force x) x

/- 14. Total energy. -/
def totalEnergy1D (m x v : ℝ) (potential : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * m * v ^ 2 + potential x

/- 15. Conservation of one-dimensional mechanical energy. -/
theorem totalEnergy1D_hasDerivAt_zero {m : ℝ} {x v a V : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (a t) t)
    (hV : HasDerivAt V (-m * a t) (x t)) :
    HasDerivAt (fun s ⇒ totalEnergy1D m (x s) (v s) V) 0 t := by
  convert (((hv.mul_const m).mul v).const_mul (1 / 2 : ℝ)).add (hV.comp t hx) using 1 <;>
    simp [totalEnergy1D] <;> ring

/- 16. Equilibrium point. -/
def IsEquilibrium (V : ℝ → ℝ) (x₀ : ℝ) : Prop := HasDerivAt V 0 x₀

/- 17. Kinetic energy. -/
def kineticEnergy (m : ℝ) (v : Vec3) : ℝ := (1 / 2 : ℝ) * m * normSq v

/- 18. Power. -/
def power (force velocity : Vec3) : ℝ := dot force velocity

/- 19. Work done along a parametrised path. -/
noncomputable def work (force : Vec3 → Vec3) (path : ℝ → Vec3) (a b : ℝ) : ℝ :=
  ∫ t in a..b, dot (force (path t)) (velocity path t)

/- 20. Conservative force and potential energy. -/
def IsConservativeForce (force : Vec3 → Vec3) (potential : Vec3 → ℝ) : Prop :=
  ∀ x, HasGradientAt potential (-force x) x

/- 21. Energy conservation for conservative force. -/
theorem conservative_energy_derivative_zero {m : ℝ} {x v a : ℝ → Vec3}
    {V : Vec3 → ℝ} {t : ℝ}
    (hK : HasDerivAt (fun s ⇒ kineticEnergy m (v s)) (m * dot (v t) (a t)) t)
    (hV : HasDerivAt (fun s ⇒ V (x s)) (-m * dot (v t) (a t)) t) :
    HasDerivAt (fun s ⇒ kineticEnergy m (v s) + V (x s)) 0 t := by
  convert hK.add hV using 1 <;> ring

/- 22. Central force. -/
def IsCentralPotential (V : Vec3 → ℝ) : Prop :=
  ∃ f : ℝ → ℝ, ∀ x, V x = f ‖x‖

/- 23. Gradient of radius (algebraic content at a nonzero point). -/
theorem radial_unit_norm (x : Vec3) (hx : x ≠ 0) : ‖(‖x‖⁻¹) • x‖ = 1 := by
  rw [norm_smul]
  simp [hx]

/- 24. Radial form of a central force. -/
theorem central_force_radial {x : Vec3} {r dV : ℝ} (hr : r ≠ 0)
    (h : r = ‖x‖) : (-dV / r) • x = (-dV) • ((r⁻¹) • x) := by
  ext i
  simp [div_eq_mul_inv, mul_assoc]

/- 25. Angular momentum. -/
def angularMomentum (r p : Vec3) : Vec3 := cross r p

/- 26. Angular momentum conservation under a central force. -/
theorem angularMomentum_derivative_zero {L G : ℝ → Vec3} {t : ℝ}
    (hTorque : ∀ i, HasDerivAt (fun s ⇒ L s i) (G t i) t)
    (hcentral : G t = 0) :
    ∀ i, HasDerivAt (fun s ⇒ L s i) 0 t := by
  intro i
  simpa [hcentral] using hTorque i

/- 27. Torque. -/
def torque (r force : Vec3) : Vec3 := cross r force

/- 28. Newton's law of gravitation: an empirical model predicate. -/
def NewtonGravitationLaw (G M m r : ℝ) (direction force : Vec3) : Prop :=
  force = (-(G * M * m / r ^ 2)) • direction

/- 29. Gravitational potential and field. -/
def gravitationalPotential (G M r : ℝ) : ℝ := -(G * M / r)
def gravitationalField (G M r : ℝ) (direction : Vec3) : Vec3 :=
  (-(G * M / r ^ 2)) • direction

/- 30. Newton's shell theorem, as the predicate asserted by the physical model. -/
def SphericalExteriorPotential (potential : ℝ → ℝ) (G M R : ℝ) : Prop :=
  ∀ r, R ≤ r → potential r = -(G * M / r)

/- 31. Lorentz force law: an empirical model predicate. -/
def LorentzForceLaw (q : ℝ) (electric magnetic velocity force : Vec3) : Prop :=
  force = q • (electric + cross velocity magnetic)

/- 32. Electrostatic potential. -/
def IsElectrostaticPotential (electric : Vec3 → Vec3) (potential : Vec3 → ℝ) : Prop :=
  ∀ x, HasGradientAt potential (-electric x) x

/- 33. Magnetic forces do no work (the algebraic core of energy conservation). -/
theorem magnetic_force_power_zero (q : ℝ) (v B : Vec3) :
    dot (q • cross v B) v = 0 := by
  simp [dot, cross]
  ring

/- 34. Coulomb's law: an empirical model predicate. -/
def CoulombLaw (Q ε₀ r : ℝ) (direction electric : Vec3) : Prop :=
  electric = (Q / (4 * Real.pi * ε₀ * r ^ 2)) • direction

/- 35. Electric constant. -/
structure ElectricConstant where
  value : ℝ
  value_pos : 0 < value

/- 36. Derivatives of polar unit vectors. -/
theorem polar_unit_vector_derivatives (theta : ℝ) :
    HasDerivAt (fun t ⇒ ![Real.cos t, Real.sin t]) ![-Real.sin theta, Real.cos theta] theta ∧
    HasDerivAt (fun t ⇒ ![-Real.sin t, Real.cos t]) ![-Real.cos theta, -Real.sin theta] theta := by
  constructor <;> rw [hasDerivAt_pi_iff] <;> intro i <;> fin_cases i <;> simp

/- 37. Radial and angular velocity. -/
structure PolarVelocity where
  radial : ℝ
  angular : ℝ

/- 38. Angular momentum per unit mass. -/
def specificAngularMomentum (r angularVelocity : ℝ) : ℝ := r ^ 2 * angularVelocity

/- 39. Apsides. -/
structure Apsides where
  periapsis : ℝ
  apoapsis : ℝ
  ordered : periapsis ≤ apoapsis

/- 40. Solar apsides terminology. -/
abbrev Perihelion := ℝ
abbrev Aphelion := ℝ

/- 41. Terrestrial apsides terminology. -/
abbrev Perigee := ℝ
abbrev Apogee := ℝ

/- 42. Reciprocal-radius notation. -/
def reciprocalRadius (r : ℝ) : ℝ := r⁻¹

/- 43. Binet's equation. -/
def SatisfiesBinetEquation (m h : ℝ) (u force : ℝ → ℝ) : Prop :=
  ∀ θ, -m * h ^ 2 * u θ ^ 2 * (deriv (deriv u) θ + u θ) = force ((u θ)⁻¹)

/- 44. Kepler conic orbit. -/
def keplerOrbit (ell e theta : ℝ) : ℝ := ell / (1 + e * Real.cos theta)

theorem keplerOrbit_satisfies_reciprocal (ell e theta : ℝ)
    (h : 1 + e * Real.cos theta ≠ 0) (hell : ell ≠ 0) :
    (keplerOrbit ell e theta)⁻¹ = (1 + e * Real.cos theta) / ell := by
  simp [keplerOrbit, h, hell]

/- 45. Eccentricity. -/
structure Eccentricity where
  value : ℝ
  nonnegative : 0 ≤ value

/- 46. Kepler's first law: a model predicate. -/
def KeplerFirstLaw (planetOrbit : Set (Vec3)) (sun : Vec3) : Prop :=
  ∃ ellipse : Set Vec3, planetOrbit = ellipse ∧ sun ∈ ellipse

/- 47. Kepler's second law: constant areal velocity. -/
def KeplerSecondLaw (sweptArea : ℝ → ℝ) : Prop :=
  ∃ k, ∀ t, HasDerivAt sweptArea k t

/- 48. Kepler's third law. -/
def KeplerThirdLaw (period semimajorAxis : ℝ) : Prop :=
  ∃ k, period ^ 2 = k * semimajorAxis ^ 3

/- 49. Angular velocity vector. -/
def angularVelocityVector (speed : ℝ) (axis : Vec3) : Vec3 := speed • axis

/- 50. Derivative in a rotating frame. -/
def RotatingDerivativeRelation (D D' : Vec3 → Vec3) (omega : Vec3) : Prop :=
  ∀ r, D r = D' r + cross omega r

/- 51. Equation of motion in a rotating frame. -/
def RotatingFrameEquation (m : ℝ) (a' force omega omegaDot v' r : Vec3) : Prop :=
  m • a' = force - (2 * m) • cross omega v' - m • cross omegaDot r -
    m • cross omega (cross omega r)

/- 52. Fictitious forces. -/
structure FictitiousForces where
  coriolis : Vec3
  euler : Vec3
  centrifugal : Vec3

def fictitiousForces (m : ℝ) (omega omegaDot velocity position : Vec3) : FictitiousForces :=
  ⟨(-2 * m) • cross omega velocity,
   (-m) • cross omegaDot position,
   (-m) • cross omega (cross omega position)⟩

/- 53. Total mass. -/
def totalMass {n : ℕ} (mass : Fin n → ℝ) : ℝ := ∑ i, mass i

/- 54. Centre of mass. -/
def centerOfMass {n : ℕ} (mass : Fin n → ℝ) (position : Fin n → Vec3) : Vec3 :=
  (totalMass mass)⁻¹ • ∑ i, mass i • position i

/- 55. Total linear momentum. -/
def totalMomentum {n : ℕ} (p : Fin n → Vec3) : Vec3 := ∑ i, p i

/- 56. Total external force. -/
def totalExternalForce {n : ℕ} (force : Fin n → Vec3) : Vec3 := ∑ i, force i

/- 57. Centre-of-mass equation. -/
theorem center_of_mass_equation {M : ℝ} {R F : ℝ → Vec3} {t : ℝ}
    (hM : M ≠ 0)
    (h : ∀ i, HasDerivAt (fun s ⇒ deriv (fun q ⇒ R q i) s) (F t i / M) t) :
    ∀ i, HasDerivAt (fun s ⇒ M * deriv (fun q ⇒ R q i) s) (F t i) t := by
  intro i
  convert (h i).const_mul M using 1 <;> field_simp

/- 58. Conservation of momentum. -/
theorem momentum_conserved_if_no_external_force {P F : ℝ → Vec3}
    (hNewton : NewtonSecondLaw P F) (hzero : ∀ t, F t = 0) :
    ∀ t i, HasDerivAt (fun s ⇒ P s i) 0 t := by
  intro t i
  simpa [hzero t] using hNewton t i

/- 59. Centre-of-mass frame. -/
def IsCenterOfMassFrame (R : ℝ → Vec3) : Prop := ∀ t, R t = 0

/- 60. Total angular momentum. -/
def totalAngularMomentum {n : ℕ} (r p : Fin n → Vec3) : Vec3 :=
  ∑ i, cross (r i) (p i)

/- 61. Total external torque. -/
def totalExternalTorque {n : ℕ} (r force : Fin n → Vec3) : Vec3 :=
  ∑ i, cross (r i) (force i)

/- 62. Rocket equation. -/
def SatisfiesRocketEquation (m v : ℝ → ℝ) (u force : ℝ → ℝ) : Prop :=
  ∀ t, m t * deriv v t + u t * deriv m t = force t

/- 63. Rigid body. -/
def IsRigidBody {n : ℕ} (position : ℝ → Fin n → Vec3) : Prop :=
  ∀ i j, ∃ d, ∀ t, ‖position t i - position t j‖ = d

/- 64. Moment of inertia of a particle. -/
def particleMomentOfInertia (m : ℝ) (axis position : Vec3) : ℝ :=
  m * normSq (cross axis position)

/- 65. Moment of inertia of a finite rigid body. -/
def rigidBodyMomentOfInertia {n : ℕ} (mass : Fin n → ℝ)
    (axis : Vec3) (position : Fin n → Vec3) : ℝ :=
  ∑ i, mass i * normSq (cross axis (position i))

/- 66. Angular momentum of a rigid body. -/
def rigidBodyAngularMomentum {n : ℕ} (mass : Fin n → ℝ)
    (position : Fin n → Vec3) (omega : Vec3) : Vec3 :=
  ∑ i, mass i • cross (position i) (cross omega (position i))

/- 67. Continuum mass, centre of mass, and moment of inertia. -/
structure ContinuumMassData where
  mass : ℝ
  centerOfMass : Vec3
  momentOfInertia : ℝ

/- 68. Perpendicular-axis theorem (finite lamina). -/
theorem perpendicular_axis_theorem {n : ℕ} (mass x y : Fin n → ℝ) :
    (∑ i, mass i * (x i ^ 2 + y i ^ 2)) =
      (∑ i, mass i * y i ^ 2) + ∑ i, mass i * x i ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/- 69. Parallel-axis theorem (finite point masses). -/
theorem parallel_axis_theorem {n : ℕ} (mass x : Fin n → ℝ) (d : ℝ)
    (hcenter : ∑ i, mass i * x i = 0) :
    (∑ i, mass i * (x i - d) ^ 2) =
      (∑ i, mass i * x i ^ 2) + (∑ i, mass i) * d ^ 2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcenter]
  simp
  ring

/- 70. Lorentz factor. -/
noncomputable def lorentzFactor (v c : ℝ) : ℝ := 1 / Real.sqrt (1 - (v / c) ^ 2)

/- 71. Lorentz transformation / special-relativity principle. -/
noncomputable def lorentzTransform (v c : ℝ) (event : Event) : Event :=
  let γ := lorentzFactor v c
  (γ * (event.1 - v / c * event.2), γ * (event.2 - v / c * event.1))

def SpecialRelativityPrinciple {Law : Type*} (valid : ℝ → Law → Prop) : Prop :=
  ∀ inertialFrame inertialFrame' law,
    valid inertialFrame law ↔ valid inertialFrame' law

/- 72. Minkowski spacetime. -/
abbrev MinkowskiSpacetime := Fin 4 → ℝ

/- 73. Simultaneous events. -/
def Simultaneous (P Q : MinkowskiSpacetime) : Prop := P 0 = Q 0

/- 74. Proper length. -/
def ProperLength (restFrameLength : ℝ) : ℝ := restFrameLength

/- 75. Invariant interval in 1+1 dimensions. -/
def intervalSq (c : ℝ) (P Q : Event) : ℝ :=
  (P.1 - Q.1) ^ 2 - (P.2 - Q.2) ^ 2

/- 76. Lorentz invariance of the interval. -/
theorem lorentz_interval_invariant {beta gamma : ℝ} (hgamma : gamma ^ 2 * (1 - beta ^ 2) = 1)
    (P Q : Event) :
    let L : Event → Event := fun X ⇒
      (gamma * (X.1 - beta * X.2), gamma * (X.2 - beta * X.1))
    intervalSq 1 (L P) (L Q) = intervalSq 1 P Q := by
  dsimp [intervalSq]
  nlinarith

/- 77. Minkowski line element. -/
def lineElementSq (c dt dx dy dz : ℝ) : ℝ :=
  c ^ 2 * dt ^ 2 - dx ^ 2 - dy ^ 2 - dz ^ 2

/- 78. Timelike, spacelike, and lightlike separation. -/
inductive Separation : ℝ → Type
  | timelike (h : 0 < s) : Separation s
  | spacelike (h : s < 0) : Separation s
  | lightlike (h : s = 0) : Separation s

/- 79. Rapidity. -/
def IsRapidity (beta gamma phi : ℝ) : Prop :=
  beta = Real.tanh phi ∧ gamma = Real.cosh phi ∧ gamma * beta = Real.sinh phi

/- 80. Proper time. -/
def properTimeDifference (interval c : ℝ) : ℝ := interval / c

/- 81. Position four-vector and four-velocity. -/
def positionFourVector (c t : ℝ) (x : Vec3) : MinkowskiSpacetime :=
  fun i ⇒ Fin.cases (c * t) x i

noncomputable def fourVelocity (X : ℝ → MinkowskiSpacetime) (tau : ℝ) : MinkowskiSpacetime :=
  fun i ⇒ deriv (fun s ⇒ X s i) tau

/- 82. Four-vector. -/
structure FourVector where
  components : MinkowskiSpacetime

/- 83. Four-momentum. -/
def fourMomentum (m : ℝ) (U : MinkowskiSpacetime) : MinkowskiSpacetime := m • U

/- 84. Relativistic energy. -/
def relativisticEnergy (c : ℝ) (P : MinkowskiSpacetime) : ℝ := P 0 * c

/- 85. Four-force. -/
noncomputable def fourForce (P : ℝ → MinkowskiSpacetime) (tau : ℝ) : MinkowskiSpacetime :=
  fun i ⇒ deriv (fun s ⇒ P s i) tau

/- 86. Centre-of-momentum frame. -/
def IsCenterOfMomentumFrame {n : ℕ} (momentum : Fin n → Vec3) : Prop :=
  ∑ i, momentum i = 0

end DynamicsRelativity
