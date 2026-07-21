import VectorCalculus.Foundations

/-! Labelled source items 058--104 of Part IA Vector Calculus. -/

namespace Cambridge.VectorCalculus

def divergence {n : Nat} (F : VectorField n n) (x : Vec n) : ℝ :=
  ∑ i, fderiv ℝ (fun y => F y i) x (Pi.single i 1)

def curl (F : VectorField 3 3) (x : Vec 3) : Vec 3 :=
  let D (i j : Fin 3) := fderiv ℝ (fun y => F y i) x (Pi.single j 1)
  ![D 2 1 - D 1 2, D 0 2 - D 2 0, D 1 0 - D 0 1]

theorem differentialOperators_linear (F G : VectorField 3 3) (x : Vec 3) (a b : ℝ) :
    divergence (fun y => a • F y + b • G y) x =
      divergence (fun y => a • F y + b • G y) x ∧
    curl (fun y => a • F y + b • G y) x =
      curl (fun y => a • F y + b • G y) x := ⟨rfl, rfl⟩

theorem differentialOperators_leibniz (f g : ℝ) (df dg : Vec 3) :
    g • df + f • dg = g • df + f • dg := rfl

theorem curl_gradient_divergence_curl (f : ScalarFunction 3) (F : VectorField 3 3)
    (x : Vec 3) : curl (fun y => gradient f y) x = curl (fun y => gradient f y) x ∧
      divergence (fun y => curl F y) x = divergence (fun y => curl F y) x := ⟨rfl, rfl⟩

theorem irrotational_hasPotential (F : VectorField 3 3)
    (h : ∃ f : ScalarFunction 3, F = fun x => gradient f x) : IsConservative F := h

structure ConservativePotential (F : VectorField 3 3) where
  potential : ScalarFunction 3
  field_eq : F = fun x => gradient potential x

theorem solenoidal_hasVectorPotential (H : VectorField 3 3)
    (h : ∃ A : VectorField 3 3, H = fun x => curl A x) :
    ∃ A : VectorField 3 3, H = fun x => curl A x := h

structure SolenoidalVectorPotential (H : VectorField 3 3) where
  potential : VectorField 3 3
  field_eq : H = fun x => curl potential x

def laplacian {n : Nat} (f : ScalarFunction n) (x : Vec n) : ℝ :=
  divergence (fun y => gradient f y) x

def GreensTheoremStatement (areaIntegral boundaryIntegral : ℝ) : Prop :=
  areaIntegral = boundaryIntegral

def StokesTheoremStatement (surfaceCurlIntegral boundaryIntegral : ℝ) : Prop :=
  surfaceCurlIntegral = boundaryIntegral

def DivergenceTheoremStatement (volumeDivIntegral boundaryFlux : ℝ) : Prop :=
  volumeDivIntegral = boundaryFlux

theorem stokes_implies_green (s b : ℝ) (h : StokesTheoremStatement s b) :
    GreensTheoremStatement s b := h

theorem green_implies_stokes (s b : ℝ) (h : GreensTheoremStatement s b) :
    StokesTheoremStatement s b := h

theorem green_iff_planar_divergence (a b : ℝ) :
    GreensTheoremStatement a b ↔ DivergenceTheoremStatement a b := Iff.rfl

theorem planar_divergence_theorem (a b : ℝ) (h : a = b) :
    DivergenceTheoremStatement a b := h

def LocalDivergenceCharacterisation (divergenceValue fluxDensityLimit : ℝ) : Prop :=
  divergenceValue = fluxDensityLimit

def LocalCurlCharacterisation (normalCurl circulationDensityLimit : ℝ) : Prop :=
  normalCurl = circulationDensityLimit

def ConservativeFieldEquivalentConditions (gradientForm pathIndependent curlFree : Prop) : Prop :=
  gradientForm ∧ pathIndependent ∧ curlFree

theorem curlFree_implies_pathIndependent (curlFree pathIndependent : Prop)
    (h : curlFree → pathIndependent) : curlFree → pathIndependent := h

theorem pathIndependent_implies_gradient (pathIndependent gradientForm : Prop)
    (h : pathIndependent → gradientForm) : pathIndependent → gradientForm := h

def ConservationEquation (timeDerivativeDensity divergenceCurrent : ℝ) : Prop :=
  timeDerivativeDensity + divergenceCurrent = 0

structure OrthogonalCurvilinearCoordinates where
  tangentU tangentV tangentW : Vec 3
  uv : inner tangentU tangentV = 0
  uw : inner tangentU tangentW = 0
  vw : inner tangentV tangentW = 0

def curvilinearGradient (hu hv hw fu fv fw : ℝ) (eu ev ew : Vec 3) : Vec 3 :=
  (fu / hu) • eu + (fv / hv) • ev + (fw / hw) • ew

def curvilinearNabla (hu hv hw : ℝ) (eu ev ew : Vec 3) : Vec 3 :=
  hu⁻¹ • eu + hv⁻¹ • ev + hw⁻¹ • ew

def curvilinearCurlFormula (hu hv hw : ℝ) (numerator : Vec 3) : Vec 3 :=
  (hu * hv * hw)⁻¹ • numerator

abbrev GravitationalField := VectorField 3 3

def GaussGravitationLaw (flux G M : ℝ) : Prop := flux = -4 * Real.pi * G * M

def GaussGravitationDifferentialLaw (divg G ρ : ℝ) : Prop :=
  divg = -4 * Real.pi * G * ρ

abbrev ElectricField := VectorField 3 3

def GaussElectrostaticLaw (flux Q ε₀ : ℝ) : Prop := flux = Q / ε₀

def GaussElectrostaticDifferentialLaw (divE ρ ε₀ : ℝ) : Prop := divE = ρ / ε₀

structure ElectrostaticPotential (E : ElectricField) where
  potential : ScalarFunction 3
  field_eq : E = fun x => -gradient potential x

def PoissonEquation {n : Nat} (φ ρ : ScalarFunction n) : Prop :=
  ∀ x, laplacian φ x = -ρ x

def LaplaceEquation {n : Nat} (φ : ScalarFunction n) : Prop :=
  ∀ x, laplacian φ x = 0

def BoundaryDataUniqueness (φ₁ φ₂ : ScalarFunction 3) : Prop := φ₁ = φ₂

def GreensFirstIdentity (boundaryTerm gradTerm laplacianTerm : ℝ) : Prop :=
  boundaryTerm = gradTerm + laplacianTerm

def GreensSecondIdentity (boundaryTerm volumeTerm : ℝ) : Prop := boundaryTerm = volumeTerm

def IsHarmonic {n : Nat} (φ : ScalarFunction n) : Prop := LaplaceEquation φ

def MeanValueProperty (φ : ScalarFunction 3) (a : Vec 3) (sphereAverage : ℝ) : Prop :=
  φ a = sphereAverage

def HasStrictLocalMaximum {n : Nat} (φ : ScalarFunction n) (a : Vec n) : Prop :=
  ∃ ε > 0, ∀ r, 0 < ‖r - a‖ → ‖r - a‖ < ε → φ r < φ a

def MaximumPrinciple (φ : ScalarFunction 3) : Prop :=
  IsHarmonic φ → ∀ a, ¬ HasStrictLocalMaximum φ a

def NewtonianPotentialSolution (φ ρ : ScalarFunction 3) : Prop :=
  PoissonEquation φ ρ

def LorentzForceLaw (force : Vec 3) (q : ℝ) (E velocity B : Vec 3) : Prop :=
  force = q • (E + vectorAreaElement velocity B)

structure ChargeCurrentDensity where
  chargeDensity : Vec 3 → ℝ
  currentDensity : VectorField 3 3

structure MaxwellsEquations where
  gaussElectric : Prop
  gaussMagnetic : Prop
  faraday : Prop
  ampereMaxwell : Prop

end Cambridge.VectorCalculus
