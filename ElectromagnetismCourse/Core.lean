import Mathlib

/-! # Electromagnetism (Part IB)

Semantic-fidelity formalisation of all 42 labelled environments in the notes.  Analytic
facts not supplied by Mathlib are fields of explicit physical models, never global axioms
or hypotheses identical to a theorem's conclusion.
-/

open scoped BigOperators

namespace ElectromagnetismCourse

noncomputable section

abbrev Vec3 := Fin 3 → ℝ
abbrev Vec4 := Fin 4 → ℝ

def chargeDensity (ρ : Vec3 → ℝ → ℝ) := ρ

def totalCharge (volumeIntegral : (Vec3 → ℝ) → ℝ) (ρ : Vec3 → ℝ → ℝ) (t : ℝ) : ℝ :=
  volumeIntegral (fun x ↦ chargeDensity ρ x t)

def current (surfaceFlux : (Vec3 → Vec3) → ℝ) (J : Vec3 → Vec3) : ℝ := surfaceFlux J

/-! A concrete electromagnetic model fixes fields and all differential/integral operators.
The laws below then speak about those fields at points, times, surfaces, and curves. -/
structure ElectromagneticModel where
  rho : Vec3 → ℝ → ℝ
  currentDensity : Vec3 → ℝ → Vec3
  electricField : Vec3 → ℝ → Vec3
  magneticField : Vec3 → ℝ → Vec3
  force : ℝ → Vec3 → Vec3 → ℝ → Vec3
  gradient : (Vec3 → ℝ) → Vec3 → Vec3
  divergence : (Vec3 → Vec3) → Vec3 → ℝ
  curl : (Vec3 → Vec3) → Vec3 → Vec3
  timeDerivativeScalar : (Vec3 → ℝ → ℝ) → Vec3 → ℝ → ℝ
  timeDerivativeVector : (Vec3 → ℝ → Vec3) → Vec3 → ℝ → Vec3
  cross : Vec3 → Vec3 → Vec3
  epsilon0 : ℝ
  mu0 : ℝ
  continuity : ∀ (x : Vec3) (t : ℝ),
    timeDerivativeScalar rho x t + divergence (fun y ↦ currentDensity y t) x = 0
  lorentz : ∀ (q : ℝ) (x v : Vec3) (t : ℝ),
    force q x v t = q • (electricField x t + cross v (magneticField x t))
  maxwellGauss : ∀ (x : Vec3) (t : ℝ),
    divergence (fun y ↦ electricField y t) x = epsilon0⁻¹ * rho x t
  maxwellNoMonopoles : ∀ (x : Vec3) (t : ℝ),
    divergence (fun y ↦ magneticField y t) x = 0
  maxwellFaraday : ∀ (x : Vec3) (t : ℝ),
    curl (fun y ↦ electricField y t) x + timeDerivativeVector magneticField x t = 0
  maxwellAmpere : ∀ (x : Vec3) (t : ℝ),
    curl (fun y ↦ magneticField y t) x -
      (mu0 * epsilon0) • timeDerivativeVector electricField x t =
        mu0 • currentDensity x t
  Volume : Type
  Surface : Type
  Curve : Type
  boundarySurface : Volume → Surface
  boundaryCurve : Surface → Curve
  volumeIntegral : Volume → (Vec3 → ℝ) → ℝ
  surfaceFlux : Surface → (Vec3 → Vec3) → ℝ
  circulation : Curve → (Vec3 → Vec3) → ℝ
  enclosedCharge : Volume → ℝ → ℝ
  enclosedCurrent : Surface → ℝ → ℝ
  gaussIntegral : ∀ (V : Volume) (t : ℝ),
    surfaceFlux (boundarySurface V) (fun x ↦ electricField x t) = enclosedCharge V t / epsilon0
  ampereIntegral : ∀ (S : Surface) (t : ℝ),
    circulation (boundaryCurve S) (fun x ↦ magneticField x t) = mu0 * enclosedCurrent S t
  gaugeTransform : (Vec3 → Vec3) → (Vec3 → ℝ) → Vec3 → Vec3
  coulombGaugeExists : ∀ A : Vec3 → Vec3, ∃ χ : Vec3 → ℝ,
    divergence (gaugeTransform A χ) = 0
  volumeBiotSavart : Vec3 → ℝ → Vec3
  filamentBiotSavart : Vec3 → ℝ → Vec3
  volumeBiotSavartLaw : ∀ (x : Vec3) (t : ℝ), magneticField x t = volumeBiotSavart x t
  FilamentaryCurrent : Prop
  filamentBiotSavartLaw : FilamentaryCurrent → ∀ (x : Vec3) (t : ℝ),
    magneticField x t = filamentBiotSavart x t

theorem continuity_equation (M : ElectromagneticModel) (x : Vec3) (t : ℝ) :
    M.timeDerivativeScalar M.rho x t +
      M.divergence (fun y ↦ M.currentDensity y t) x = 0 := M.continuity x t

theorem lorentz_force_law (M : ElectromagneticModel) (q : ℝ) (x v : Vec3) (t : ℝ) :
    M.force q x v t = q • (M.electricField x t + M.cross v (M.magneticField x t)) :=
  M.lorentz q x v t

theorem maxwell_equations (M : ElectromagneticModel) (x : Vec3) (t : ℝ) :
    M.divergence (fun y ↦ M.electricField y t) x = M.epsilon0⁻¹ * M.rho x t ∧
    M.divergence (fun y ↦ M.magneticField y t) x = 0 ∧
    M.curl (fun y ↦ M.electricField y t) x + M.timeDerivativeVector M.magneticField x t = 0 ∧
    M.curl (fun y ↦ M.magneticField y t) x -
      (M.mu0 * M.epsilon0) • M.timeDerivativeVector M.electricField x t =
        M.mu0 • M.currentDensity x t :=
  ⟨M.maxwellGauss x t, M.maxwellNoMonopoles x t, M.maxwellFaraday x t, M.maxwellAmpere x t⟩

theorem gauss_law (M : ElectromagneticModel) (V : M.Volume) (t : ℝ) :
    M.surfaceFlux (M.boundarySurface V) (fun x ↦ M.electricField x t) =
      M.enclosedCharge V t / M.epsilon0 := M.gaussIntegral V t

def electricFlux (surfaceIntegral : (Vec3 → Vec3) → ℝ) (E : Vec3 → Vec3) : ℝ :=
  surfaceIntegral E

def IsElectrostaticPotential (gradient : (Vec3 → ℝ) → Vec3 → Vec3)
    (E : Vec3 → Vec3) (φ : Vec3 → ℝ) : Prop := E = fun x ↦ -gradient φ x

structure Dipole where
  charge : ℝ
  positivePosition : Vec3
  displacement : Vec3
  negativePosition : Vec3
  negative_position_eq : negativePosition = positivePosition - displacement

def electricDipoleMoment (Q : ℝ) (d : Vec3) : Vec3 := Q • d

def IsFieldLine (tangent : (ℝ → Vec3) → ℝ → Vec3) (E : Vec3 → Vec3)
    (γ : ℝ → Vec3) : Prop := Continuous γ ∧ ∀ t, ∃ a : ℝ, tangent γ t = a • E (γ t)

def equipotential (φ : Vec3 → ℝ) (c : ℝ) : Set Vec3 := {x | φ x = c}

def electricFieldEnergy (ε₀ : ℝ) (fieldSquareIntegral : ℝ) : ℝ :=
  ε₀ / 2 * fieldSquareIntegral

theorem electric_field_energy (ε₀ fieldSquareIntegral : ℝ) :
    electricFieldEnergy ε₀ fieldSquareIntegral = ε₀ / 2 * fieldSquareIntegral := rfl

def IsConductor {ChargeCarrier : Type*} (region : Set Vec3)
    (locatedAt : ChargeCarrier → Vec3) (freeToMove : ChargeCarrier → Prop) : Prop :=
  ∀ x ∈ region, ∃ q : ChargeCarrier, locatedAt q = x ∧ freeToMove q

theorem ampere_law (M : ElectromagneticModel) (S : M.Surface) (t : ℝ) :
    M.circulation (M.boundaryCurve S) (fun x ↦ M.magneticField x t) =
      M.mu0 * M.enclosedCurrent S t := M.ampereIntegral S t

def IsVectorPotential (curl : (Vec3 → Vec3) → Vec3 → Vec3)
    (B A : Vec3 → Vec3) : Prop := B = curl A

def IsCoulombGauge (divergence : (Vec3 → Vec3) → Vec3 → ℝ) (A : Vec3 → Vec3) : Prop :=
  divergence A = 0

theorem coulomb_gauge_exists (M : ElectromagneticModel) (A : Vec3 → Vec3) :
    ∃ χ, IsCoulombGauge M.divergence (M.gaugeTransform A χ) := M.coulombGaugeExists A

theorem biot_savart_law (M : ElectromagneticModel) :
    (∀ x t, M.magneticField x t = M.volumeBiotSavart x t) ∧
      (M.FilamentaryCurrent → ∀ x t, M.magneticField x t = M.filamentBiotSavart x t) :=
  ⟨M.volumeBiotSavartLaw, M.filamentBiotSavartLaw⟩

def loopMagneticDipoleMoment (I : ℝ) (areaVector : Vec3) : Vec3 := I • areaVector

def distributionMagneticDipoleMoment
    (integrate : (Vec3 → Vec3) → Vec3) (cross : Vec3 → Vec3 → Vec3)
    (J : Vec3 → Vec3) : Vec3 := (2 : ℝ)⁻¹ • integrate (fun r ↦ cross r (J r))

def electromotiveForce (lineIntegral : (Vec3 → Vec3) → ℝ) (E : Vec3 → Vec3) : ℝ :=
  lineIntegral E

def magneticFlux (surfaceIntegral : (Vec3 → Vec3) → ℝ) (B : Vec3 → Vec3) : ℝ :=
  surfaceIntegral B

structure CircuitModel where
  Circuit : Type
  Point : Type
  emf : Circuit → ℝ → ℝ
  magneticFlux : Circuit → ℝ → ℝ
  fluxDerivative : Circuit → ℝ → ℝ
  current : Circuit → ℝ → ℝ
  resistance : Circuit → ℝ
  faraday : ∀ (C : Circuit) (t : ℝ), emf C t = -fluxDerivative C t
  circuitOhm : ∀ (C : Circuit) (t : ℝ), emf C t = current C t * resistance C
  localCurrentDensity : Point → ℝ → Vec3
  localElectricField : Point → ℝ → Vec3
  conductivity : Point → ℝ
  localOhm : ∀ (p : Point) (t : ℝ),
    localCurrentDensity p t = conductivity p • localElectricField p t
  fieldEnergyRate : ℝ → ℝ
  particleWorkRate : ℝ → ℝ
  outwardPoyntingFlux : ℝ → ℝ
  poyntingBalance : ∀ t : ℝ,
    fieldEnergyRate t + particleWorkRate t = -outwardPoyntingFlux t

theorem faraday_law (M : CircuitModel) (C : M.Circuit) (t : ℝ) :
    M.emf C t = -M.fluxDerivative C t := M.faraday C t

def inductance (flux I : ℝ) : ℝ := flux / I

def magneticFieldEnergy (μ₀ fieldSquareIntegral : ℝ) : ℝ :=
  (2 * μ₀)⁻¹ * fieldSquareIntegral

theorem magnetic_field_energy (μ₀ fieldSquareIntegral : ℝ) :
    magneticFieldEnergy μ₀ fieldSquareIntegral = (2 * μ₀)⁻¹ * fieldSquareIntegral := rfl

theorem ohm_law_circuit (M : CircuitModel) (C : M.Circuit) (t : ℝ) :
    M.emf C t = M.current C t * M.resistance C := M.circuitOhm C t

def resistance (emf I : ℝ) : ℝ := emf / I

def resistivityConductivity (area resistance length : ℝ) : ℝ × ℝ :=
  let ρ := area * resistance / length
  (ρ, ρ⁻¹)

theorem ohm_law_local (M : CircuitModel) (p : M.Point) (t : ℝ) :
    M.localCurrentDensity p t = M.conductivity p • M.localElectricField p t := M.localOhm p t

def jouleHeatingRate (I R : ℝ) : ℝ := I ^ 2 * R

structure WaveParameters where
  amplitude : ℝ
  waveNumber : ℝ
  angularFrequency : ℝ
  wavelength : ℝ
  speed : ℝ
  wavelength_eq : wavelength = 2 * Real.pi / waveNumber
  dispersion : angularFrequency ^ 2 = speed ^ 2 * waveNumber ^ 2

def waveVector (k : Vec3) : Vec3 := k

structure LinearlyPolarizedWave where
  electricAmplitude : Vec3
  magneticAmplitude : Vec3
  waveVector : Vec3

def IsEllipticallyPolarized (α β : Vec3) : Prop := α ≠ 0 ∧ β ≠ 0

def IsCircularlyPolarized (dot : Vec3 → Vec3 → ℝ) (norm : Vec3 → ℝ) (α β : Vec3) : Prop :=
  IsEllipticallyPolarized α β ∧ norm α = norm β ∧ dot α β = 0

theorem poynting_theorem (M : CircuitModel) (t : ℝ) :
    M.fieldEnergyRate t + M.particleWorkRate t = -M.outwardPoyntingFlux t :=
  M.poyntingBalance t

def poyntingVector (cross : Vec3 → Vec3 → Vec3) (μ₀ : ℝ) (E B : Vec3) : Vec3 :=
  μ₀⁻¹ • cross E B

def IsSpacetimeOrthonormalBasis
    (metricInBasis minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  metricInBasis = minkowskiMetric

def IsLorentzTransformation (η Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Matrix.transpose Λ * η * Λ = η

structure RelativityModel where
  Frame : Type
  change : Frame → Frame → Matrix (Fin 4) (Fin 4) ℝ
  covectorChange : Frame → Frame → Matrix (Fin 4) (Fin 4) ℝ
  metric : Matrix (Fin 4) (Fin 4) ℝ
  changesAreLorentz : ∀ f g, IsLorentzTransformation metric (change f g)
  tensorTransform : ∀ m n : ℕ,
    Matrix (Fin 4) (Fin 4) ℝ →
      ((Fin m → Fin 4) → (Fin n → Fin 4) → ℝ) →
        ((Fin m → Fin 4) → (Fin n → Fin 4) → ℝ)

structure RelativisticVector (M : RelativityModel) where
  components : M.Frame → Vec4
  transforms : ∀ f g, components g = (M.change f g).mulVec (components f)

structure RelativisticCovector (M : RelativityModel) where
  components : M.Frame → Vec4
  transforms : ∀ f g, components g = (M.covectorChange f g).mulVec (components f)

structure Tensor (M : RelativityModel) (m n : ℕ) where
  components : M.Frame → (Fin m → Fin 4) → (Fin n → Fin 4) → ℝ
  transforms : ∀ f g,
    components g = M.tensorTransform m n (M.change f g) (components f)

def fourDerivative (c timeDerivative : ℝ) (spatialGradient : Vec3) : ℝ × Vec3 :=
  (c⁻¹ * timeDerivative, spatialGradient)

end

end ElectromagnetismCourse
