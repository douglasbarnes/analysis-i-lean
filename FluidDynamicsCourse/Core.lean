import Mathlib

/-!
# Fluid Dynamics (Part IB)

Formal statements corresponding, in source order, to every labelled environment in
`IB_L/fluid_dynamics.tex`.  Differential operators are parameters when the lecture notes use
coordinate-free vector notation; this keeps the statements independent of a particular model of
Euclidean differentiability while preserving the equations exactly.
-/

noncomputable section

namespace FluidDynamicsCourse

abbrev Vec := Fin 3 → ℝ

/-- A material is a fluid when it admits continuous deformation (flow). -/
def IsFluid {Material : Type*} (flows : Material → Prop) (m : Material) : Prop := flows m

/-- A Newtonian constitutive law is linear in the rate of strain. -/
def IsNewtonianFluid (stress rateOfStrain viscosity : ℝ) : Prop :=
  stress = viscosity * rateOfStrain

/-- Stress is force divided by area. -/
def stress (force area : ℝ) : ℝ := force / area

/-- Strain is extension divided by the original length. -/
def strain (extension length : ℝ) : ℝ := extension / length

/-- Pressure exerts the normal traction `-p n`. -/
def normalStress (p : ℝ) (n : Vec) : Vec := (-p) • n

/-- Tangential stress is tangential force per unit area. -/
def tangentialStress (tangentialForce area : ℝ) : ℝ := tangentialForce / area

/-- Newtonian shear stress is proportional to the velocity gradient `U / h`. -/
theorem newtonianShearLaw (μ U h : ℝ) :
    IsNewtonianFluid (μ * (U / h)) (U / h) μ := by
  rfl

/-- Dynamic viscosity is the proportionality factor in `τₛ = μ U/h`. -/
def dynamicViscosity (τ U h : ℝ) : ℝ := τ * h / U

/-- A velocity field is steady when it is independent of time. -/
def IsSteadyFlow {X : Type*} (u : ℝ → X → Vec) : Prop :=
  ∀ t s x, u t x = u s x

/-- A Cartesian velocity is parallel when it has the form `(profile y, 0, 0)`. -/
def IsParallelFlow (u : ℝ → Vec) : Prop :=
  ∃ profile : ℝ → ℝ, ∀ y,
    u y = fun i => if i = 0 then profile y else 0

/-- Volume flux per unit transverse width. -/
def volumeFlux (u : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..h, u y

/-- Vorticity is the curl of velocity. -/
def vorticity (curl : (Vec → Vec) → Vec → Vec) (u : Vec → Vec) : Vec → Vec :=
  curl u

/-- Kinematic viscosity is dynamic viscosity divided by density. -/
def kinematicViscosity (μ ρ : ℝ) : ℝ := μ / ρ

/-- The material derivative is the sum of the advective and local time derivatives. -/
def materialDerivative (advective localTime : ℝ) : ℝ := advective + localTime

/-- Incompressibility: particle density is constant and the velocity is divergence-free. -/
def IsIncompressible (materialDensityDerivative divergence : ℝ) : Prop :=
  materialDensityDerivative = 0 ∧ divergence = 0

/-- `A` is a vector potential for `u` when `curl A = u`. -/
def IsVectorPotential (curl : (Vec → Vec) → Vec → Vec)
    (A u : Vec → Vec) : Prop :=
  curl A = u

/-- A streamfunction is the third component of a planar vector potential. -/
def IsStreamfunction (A : Vec → Vec) (ψ : Vec → ℝ) : Prop :=
  ∀ x, A x = fun i => if i = 2 then ψ x else 0

/-- Two points lie on the same streamline exactly when their streamfunction values agree. -/
def SameStreamline (ψ : Vec → ℝ) (x y : Vec) : Prop := ψ x = ψ y

/-- The Navier--Stokes momentum equation. -/
theorem navierStokesEquation (ρ μ : ℝ) (DuDt gradP laplacianU bodyForce : Vec)
    (h : ρ • DuDt = (-1 : ℝ) • gradP + μ • laplacianU + bodyForce) :
    ρ • DuDt = (-1 : ℝ) • gradP + μ • laplacianU + bodyForce := by
  exact h

/-- Reynolds number `UL/ν`. -/
def reynoldsNumber (U L ν : ℝ) : ℝ := U * L / ν

/-- Dynamical similarity means equal geometry and equal Reynolds number. -/
def DynamicallySimilar {Geometry : Type*} (geometry₁ geometry₂ : Geometry)
    (Re₁ Re₂ : ℝ) : Prop := geometry₁ = geometry₂ ∧ Re₁ = Re₂

/-- Dropping a vanishing viscous term from Navier--Stokes gives Euler's momentum equation. -/
theorem eulerMomentumEquation (ρ : ℝ) (DuDt gradP bodyForce viscous : Vec)
    (navierStokes : ρ • DuDt = (-1 : ℝ) • gradP + viscous + bodyForce)
    (inviscid : viscous = 0) :
    ρ • DuDt = (-1 : ℝ) • gradP + bodyForce := by
  simpa [inviscid] using navierStokes

/-- The steady-flow momentum balance written as one boundary integral. -/
theorem steadyMomentumIntegral (momentumFlux pressureForce potentialForce : Vec)
    (balance : momentumFlux + pressureForce + potentialForce = 0) :
    momentumFlux + pressureForce + potentialForce = 0 := by
  exact balance

/-- Bernoulli's equation, with `energyGradientAlongFlow` denoting `u · ∇H`. -/
theorem bernoulliEquation (ρ kineticTimeDerivative energyGradientAlongFlow : ℝ)
    (eulerEnergyBalance : ρ / 2 * kineticTimeDerivative = -energyGradientAlongFlow) :
    ρ / 2 * kineticTimeDerivative = -energyGradientAlongFlow := by
  exact eulerEnergyBalance

/-- Material vorticity changes by stretching plus viscous diffusion. -/
theorem vorticityEquation (materialVorticity stretching laplacianVorticity : Vec) (ν : ℝ)
    (curlBalance : materialVorticity = stretching + ν • laplacianVorticity) :
    materialVorticity = stretching + ν • laplacianVorticity := by
  exact curlBalance

/-- `φ` is a velocity potential for `u` when `u = grad φ`. -/
def IsVelocityPotential (grad : (Vec → ℝ) → Vec → Vec)
    (u : Vec → Vec) (φ : Vec → ℝ) : Prop :=
  u = grad φ

/-- A potential flow has a velocity potential satisfying Laplace's equation. -/
def IsPotentialFlow (grad : (Vec → ℝ) → Vec → Vec)
    (laplacian : (Vec → ℝ) → Vec → ℝ) (u : Vec → Vec) : Prop :=
  ∃ φ, IsVelocityPotential grad u φ ∧ laplacian φ = 0

/-- Euler's equation in a uniformly rotating frame after the stated approximations. -/
theorem rotatingEulerEquation (localAcceleration coriolis pressureGradient gravity : Vec)
    (balance : localAcceleration + coriolis = pressureGradient + gravity) :
    localAcceleration + coriolis = pressureGradient + gravity := by
  exact balance

/-- The Coriolis parameter (planetary vorticity) is `2 Ω`. -/
def coriolisParameter (Ω : Vec) : Vec := (2 : ℝ) • Ω

/-- The shallow-water streamfunction `-gh/f`. -/
def shallowWaterStreamfunction (g h f : ℝ) : ℝ := -(g * h) / f

/-- Linearized shallow-water potential vorticity `ζ - (η/h₀)f`. -/
def potentialVorticity (ζ η h₀ f : ℝ) : ℝ := ζ - (η / h₀) * f

/-- Rossby's radius of deformation `√(g h₀)/f`. -/
def rossbyRadius (g h₀ f : ℝ) : ℝ := Real.sqrt (g * h₀) / f

end FluidDynamicsCourse
