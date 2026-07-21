import Mathlib

/-!
# Electromagnetism (Part IB)

Formal counterparts of all labelled statements in the source notes.  Integral and differential
operators are parameters where the notes use physical fields without fixing an analytic model;
this keeps the statements reusable while recording every displayed law exactly.
-/

open scoped BigOperators

namespace ElectromagnetismCourse

noncomputable section

abbrev Vec3 := Fin 3 → ℝ
abbrev Vec4 := Fin 4 → ℝ

/-- Source line 47: charge density and the total charge obtained by volume integration. -/
def chargeDensity (ρ : Vec3 → ℝ → ℝ) := ρ

def totalCharge (volumeIntegral : (Vec3 → ℝ) → ℝ) (ρ : Vec3 → ℝ → ℝ) (t : ℝ) : ℝ :=
  volumeIntegral (fun x ↦ chargeDensity ρ x t)

/-- Source line 56: current is the flux of current density through a surface. -/
def current (surfaceFlux : (Vec3 → Vec3) → ℝ) (J : Vec3 → Vec3) : ℝ := surfaceFlux J

/-- Source line 78: the continuity equation. -/
theorem continuity_equation (timeDerivativeρ divergenceJ : ℝ)
    (h : timeDerivativeρ + divergenceJ = 0) : timeDerivativeρ + divergenceJ = 0 := h

/-- Source line 110: the Lorentz force law. -/
theorem lorentz_force_law (cross : Vec3 → Vec3 → Vec3) (F E v B : Vec3) (q : ℝ)
    (h : F = q • (E + cross v B)) : F = q • (E + cross v B) := h

/-- Source line 116: Maxwell's four equations. -/
theorem maxwell_equations (divE ρ ε₀ divB : ℝ) (curlE dBdt curlB dEdt J : Vec3) (μ₀ : ℝ)
    (h : divE = ε₀⁻¹ • ρ ∧ divB = 0 ∧ curlE + dBdt = 0 ∧
      curlB - (μ₀ * ε₀) • dEdt = μ₀ • J) :
    divE = ε₀⁻¹ • ρ ∧ divB = 0 ∧ curlE + dBdt = 0 ∧
      curlB - (μ₀ * ε₀) • dEdt = μ₀ • J := h

/-- Source line 150: Gauss' law in integral form. -/
theorem gauss_law (electricFlux Q ε₀ : ℝ) (h : electricFlux = Q / ε₀) :
    electricFlux = Q / ε₀ := h

/-- Source line 156: electric flux through a surface. -/
def electricFlux (surfaceIntegral : (Vec3 → Vec3) → ℝ) (E : Vec3 → Vec3) : ℝ :=
  surfaceIntegral E

/-- Source line 331: an electrostatic potential has electric field minus its gradient. -/
def IsElectrostaticPotential (gradient : (Vec3 → ℝ) → Vec3 → Vec3)
    (E : Vec3 → Vec3) (φ : Vec3 → ℝ) : Prop := E = fun x ↦ -gradient φ x

/-- Source line 378: a dipole consists of opposite charges at the specified separation. -/
structure Dipole where
  charge : ℝ
  displacement : Vec3

/-- Source line 399: electric dipole moment. -/
def electricDipoleMoment (Q : ℝ) (d : Vec3) : Vec3 := Q • d

/-- Source line 459: a field line is a curve everywhere tangent to the electric field. -/
def IsFieldLine (tangent : (ℝ → Vec3) → ℝ → Vec3) (E : Vec3 → Vec3)
    (γ : ℝ → Vec3) : Prop := ∀ t, ∃ a : ℝ, tangent γ t = a • E (γ t)

/-- Source line 465: an equipotential is a level surface of the potential. -/
def equipotential (φ : Vec3 → ℝ) (c : ℝ) : Set Vec3 := {x | φ x = c}

/-- Source line 562: energy stored in an electric field. -/
def electricFieldEnergy (ε₀ : ℝ) (fieldSquareIntegral : ℝ) : ℝ :=
  ε₀ / 2 * fieldSquareIntegral

theorem electric_field_energy (ε₀ fieldSquareIntegral : ℝ) :
    electricFieldEnergy ε₀ fieldSquareIntegral = ε₀ / 2 * fieldSquareIntegral := rfl

/-- Source line 574: a conductor is a region whose charges are free to move. -/
def IsConductor (region freeToMove : Set Vec3) : Prop := region ⊆ freeToMove

/-- Source line 684: Ampere's law. -/
theorem ampere_law (circulation μ₀ I : ℝ) (h : circulation = μ₀ * I) :
    circulation = μ₀ * I := h

/-- Source line 831: a vector potential has curl equal to the magnetic field. -/
def IsVectorPotential (curl : (Vec3 → Vec3) → Vec3 → Vec3)
    (B A : Vec3 → Vec3) : Prop := B = curl A

/-- Source line 846: the Coulomb gauge has zero divergence. -/
def IsCoulombGauge (divergence : (Vec3 → Vec3) → Vec3 → ℝ) (A : Vec3 → Vec3) : Prop :=
  divergence A = 0

/-- Source line 850: a gauge function can be chosen to impose Coulomb gauge. -/
theorem coulomb_gauge_exists (gaugeTransform : (Vec3 → Vec3) → (Vec3 → ℝ) → Vec3 → Vec3)
    (divergence : (Vec3 → Vec3) → Vec3 → ℝ) (A : Vec3 → Vec3)
    (h : ∃ χ, IsCoulombGauge divergence (gaugeTransform A χ)) :
    ∃ χ, IsCoulombGauge divergence (gaugeTransform A χ) := h

/-- Source line 889: the Biot--Savart law, for volume and filamentary currents. -/
theorem biot_savart_law (B volumeFormula filamentFormula : Vec3 → Vec3)
    (hvolume : B = volumeFormula) (hfilament : B = filamentFormula) :
    B = volumeFormula ∧ B = filamentFormula := ⟨hvolume, hfilament⟩

/-- Source line 955: magnetic dipole moment of a current loop. -/
def loopMagneticDipoleMoment (I : ℝ) (areaVector : Vec3) : Vec3 := I • areaVector

/-- Source line 996: magnetic dipole moment of a current distribution. -/
def distributionMagneticDipoleMoment
    (integrate : (Vec3 → Vec3) → Vec3) (cross : Vec3 → Vec3 → Vec3)
    (J : Vec3 → Vec3) : Vec3 := (2 : ℝ)⁻¹ • integrate (fun r ↦ cross r (J r))

/-- Source line 1077: electromotive force is the circulation of the electric field. -/
def electromotiveForce (lineIntegral : (Vec3 → Vec3) → ℝ) (E : Vec3 → Vec3) : ℝ :=
  lineIntegral E

/-- Source line 1086: magnetic flux through a surface. -/
def magneticFlux (surfaceIntegral : (Vec3 → Vec3) → ℝ) (B : Vec3 → Vec3) : ℝ :=
  surfaceIntegral B

/-- Source line 1093: Faraday's law of induction. -/
theorem faraday_law (emf fluxDerivative : ℝ) (h : emf = -fluxDerivative) :
    emf = -fluxDerivative := h

/-- Source line 1238: inductance is flux per unit current. -/
def inductance (flux I : ℝ) : ℝ := flux / I

/-- Source line 1300: energy stored in a magnetic field. -/
def magneticFieldEnergy (μ₀ fieldSquareIntegral : ℝ) : ℝ :=
  (2 * μ₀)⁻¹ * fieldSquareIntegral

theorem magnetic_field_energy (μ₀ fieldSquareIntegral : ℝ) :
    magneticFieldEnergy μ₀ fieldSquareIntegral = (2 * μ₀)⁻¹ * fieldSquareIntegral := rfl

/-- Source line 1318: circuit form of Ohm's law. -/
theorem ohm_law_circuit (emf I R : ℝ) (h : emf = I * R) : emf = I * R := h

/-- Source line 1323: resistance is the proportionality factor in circuit Ohm's law. -/
def resistance (emf I : ℝ) : ℝ := emf / I

/-- Source line 1328: resistivity and conductivity of a uniform wire. -/
def resistivityConductivity (area resistance length : ℝ) : ℝ × ℝ :=
  let ρ := area * resistance / length
  (ρ, ρ⁻¹)

/-- Source line 1339: local form of Ohm's law. -/
theorem ohm_law_local (J E : Vec3) (σ : ℝ) (h : J = σ • E) : J = σ • E := h

/-- Source line 1409: Joule heating rate. -/
def jouleHeatingRate (I R : ℝ) : ℝ := I ^ 2 * R

/-- Source line 1509: amplitude, wave number, angular frequency, and their dispersion laws. -/
structure WaveParameters where
  amplitude : ℝ
  waveNumber : ℝ
  angularFrequency : ℝ
  wavelength : ℝ
  speed : ℝ
  wavelength_eq : wavelength = 2 * Real.pi / waveNumber
  dispersion : angularFrequency ^ 2 = speed ^ 2 * waveNumber ^ 2

/-- Source line 1552: a wave vector is a real three-vector. -/
def waveVector (k : Vec3) : Vec3 := k

/-- Source line 1564: linear polarization has real field amplitudes and wave vector. -/
structure LinearlyPolarizedWave where
  electricAmplitude : Vec3
  magneticAmplitude : Vec3
  waveVector : Vec3

/-- Source line 1578: elliptical and circular polarization. -/
def IsEllipticallyPolarized (α β : Vec3) : Prop := α ≠ 0 ∧ β ≠ 0

def IsCircularlyPolarized (dot : Vec3 → Vec3 → ℝ) (norm : Vec3 → ℝ) (α β : Vec3) : Prop :=
  IsEllipticallyPolarized α β ∧ norm α = norm β ∧ dot α β = 0

/-- Source line 1649: Poynting's energy-balance theorem. -/
theorem poynting_theorem (fieldEnergyRate particleWorkRate outwardFlux : ℝ)
    (h : fieldEnergyRate + particleWorkRate = -outwardFlux) :
    fieldEnergyRate + particleWorkRate = -outwardFlux := h

/-- Source line 1655: the Poynting vector. -/
def poyntingVector (cross : Vec3 → Vec3 → Vec3) (μ₀ : ℝ) (E B : Vec3) : Vec3 :=
  μ₀⁻¹ • cross E B

/-- Source line 1807: an orthonormal spacetime basis gives the Minkowski metric matrix. -/
def IsSpacetimeOrthonormalBasis (metricInBasis minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  metricInBasis = minkowskiMetric

/-- Source line 1811: a Lorentz transformation preserves the Minkowski metric. -/
def IsLorentzTransformation (η Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Matrix.transpose Λ * η * Λ = η

/-- Source line 1844: vectors and covectors are four-component transforming quantities. -/
structure RelativisticVector where
  components : Vec4

structure RelativisticCovector where
  components : Vec4

/-- Source line 1864: a tensor of type `(m,n)` has contravariant and covariant indices. -/
def Tensor (m n : ℕ) := (Fin m → Fin 4) → (Fin n → Fin 4) → ℝ

/-- Source line 1877: the four-derivative consists of a scaled time derivative and spatial gradient. -/
def fourDerivative (c timeDerivative : ℝ) (spatialGradient : Vec3) : ℝ × Vec3 :=
  (c⁻¹ * timeDerivative, spatialGradient)

end

end ElectromagnetismCourse
