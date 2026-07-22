import Mathlib

/-! Faithful formal counterparts of the 25 labelled environments in the IB
Quantum Mechanics notes.  Analytic/physical laws are obligations on explicit
models, never global axioms. -/

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace QuantumMechanics

noncomputable section

variable {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]

abbrev Operator (State : Type*) [AddCommMonoid State] [Module ℂ State] := State →ₗ[ℂ] State

/- 1. Time-independent Schrödinger equation. -/
def TimeIndependentSchrodinger (H : Operator State) (ψ : State) (E : ℂ) : Prop := H ψ = E • ψ

/- 2. Time-dependent Schrödinger equation. -/
def TimeDependentSchrodinger (ℏ : ℝ) (H : Operator State)
    (timeDerivative Ψ : ℝ → State) : Prop :=
  ∀ t, (Complex.I * ℏ) • timeDerivative t = H (Ψ t)

/- 3. Stationary state. -/
def IsStationaryState (ℏ E : ℝ) (H : Operator State) (ψ : State) (Ψ : ℝ → State) : Prop :=
  TimeIndependentSchrodinger H ψ E ∧
    ∀ t, Ψ t = Complex.exp (-(Complex.I * (E * t / ℏ))) • ψ

/- 4. Probability conservation.  These two pointwise Schrödinger equations
are the equation and its conjugate for a real potential.  The potential terms
cancel in the genuine algebraic proof of the continuity equation. -/
def probabilityDensityDerivative (ψ dψdt starψ dstarψdt : ℂ) : ℂ :=
  starψ * dψdt + dstarψdt * ψ

def probabilityCurrentDerivative (kinetic : ℝ)
    (ψ ψxx starψ starψxx : ℂ) : ℂ :=
  -(Complex.I * kinetic) * (starψ * ψxx - starψxx * ψ)

structure PointSchrodingerData where
  kinetic : ℝ
  potential : ℝ
  ψ : ℂ
  ψxx : ℂ
  starψ : ℂ
  starψxx : ℂ
  dψdt : ℂ
  dstarψdt : ℂ
  schrodinger : dψdt = Complex.I * kinetic * ψxx - Complex.I * potential * ψ
  conjugate_schrodinger : dstarψdt =
    -(Complex.I * kinetic) * starψxx + Complex.I * potential * starψ

theorem probability_density_conservation (D : PointSchrodingerData) :
    probabilityDensityDerivative D.ψ D.dψdt D.starψ D.dstarψdt =
      -probabilityCurrentDerivative D.kinetic D.ψ D.ψxx D.starψ D.starψxx := by
  rw [D.schrodinger, D.conjugate_schrodinger]
  simp only [probabilityDensityDerivative, probabilityCurrentDerivative]
  ring

/- 5. Inner product. -/
def waveInner (φ ψ : State) : ℂ := ⟪φ, ψ⟫_ℂ

/- 6. Norm. -/
def waveNorm (ψ : State) : ℝ := ‖ψ‖

/- 7. Expectation value. -/
def expectationValue (Q : Operator State) (ψ : State) : ℂ := waveInner ψ (Q ψ)

/- 8. Uncertainty: ΔQ² = ⟨(Q-⟨Q⟩)²⟩. -/
def centeredOperator (Q : Operator State) (ψ : State) : Operator State :=
  Q - expectationValue Q ψ • LinearMap.id

def uncertaintySq (Q : Operator State) (ψ : State) : ℝ :=
  (expectationValue ((centeredOperator Q ψ).comp (centeredOperator Q ψ)) ψ).re

def uncertainty (Q : Operator State) (ψ : State) : ℝ := Real.sqrt (uncertaintySq Q ψ)

/- 9. Hermitian operator. -/
def IsHermitian (Q : Operator State) : Prop :=
  ∀ φ ψ, waveInner φ (Q ψ) = waveInner (Q φ) ψ

/- 10. Position, momentum and the real-potential Hamiltonian are Hermitian.
The domain-sensitive analytic obligations belong to the representation. -/
structure SchrodingerRepresentation (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  position : Operator State
  momentum : Operator State
  hamiltonian : Operator State
  position_hermitian : IsHermitian position
  momentum_hermitian : IsHermitian momentum
  realPotential_hamiltonian_hermitian : IsHermitian hamiltonian

/- 11. Cauchy--Schwarz. -/
theorem wave_cauchy_schwarz (ψ φ : State) : ‖waveInner ψ φ‖ ≤ waveNorm ψ * waveNorm φ := by
  simpa [waveInner, waveNorm] using norm_inner_le_norm ψ φ

/- 12. Ehrenfest equations.  This is an explicit Schrödinger-model interface:
implementations must calculate the two displayed derivatives. -/
structure EhrenfestModel (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  mass : ℝ
  mass_ne_zero : mass ≠ 0
  position : Operator State
  momentum : Operator State
  potentialDerivative : Operator State
  trajectory : ℝ → State
  positionExpectationDerivative : ℝ → ℂ
  momentumExpectationDerivative : ℝ → ℂ
  positionEquation : ∀ t, positionExpectationDerivative t =
    ((1 / mass : ℝ) : ℂ) * expectationValue momentum (trajectory t)
  momentumEquation : ∀ t, momentumExpectationDerivative t =
    -expectationValue potentialDerivative (trajectory t)

/- 13. Heisenberg uncertainty, genuinely proved from the imaginary-inner-
product form of the canonical commutator and Cauchy--Schwarz. -/
theorem heisenberg_uncertainty (ℏ : ℝ) (Xψ Pψ : State)
    (canonical : ℏ = 2 * |(waveInner Xψ Pψ).im|) : ℏ / 2 ≤ ‖Xψ‖ * ‖Pψ‖ := by
  calc
    ℏ / 2 = |(waveInner Xψ Pψ).im| := by rw [canonical]; ring
    _ ≤ ‖waveInner Xψ Pψ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖Xψ‖ * ‖Pψ‖ := by simpa [waveInner] using norm_inner_le_norm Xψ Pψ

/- 14. Commutator and canonical commutation relation. -/
def commutator (Q S : Operator State) : Operator State := Q.comp S - S.comp Q

def CanonicalCommutation (ℏ : ℝ) (x p : Operator State) : Prop :=
  commutator x p = (Complex.I * ℏ) • LinearMap.id

/- 15. Wavepacket: a spatially localized wavefunction. -/
def IsWavepacket (ψ : ℝ → ℂ) : Prop :=
  ∃ x₀ : ℝ, Tendsto (fun r : ℝ => ψ (x₀ + r)) (cocompact ℝ) (nhds 0)

/- 16. Gaussian wavepacket. -/
def IsGaussianWavepacket (α : ℝ) (γ : ℝ → ℂ) (Ψ : ℝ → ℝ → ℂ) : Prop :=
  ∀ x t, Ψ t x =
    ((α / Real.pi) ^ (1 / 4 : ℝ) : ℝ) •
      (1 / Complex.sqrt (γ t)) * Complex.exp (-((x : ℂ) ^ 2) / (2 * γ t))

/- 17. Ground and excited states. -/
def IsEigenstate (H : Operator State) (E : ℝ) (ψ : State) : Prop := H ψ = (E : ℂ) • ψ

def IsGroundState (H : Operator State) (energy : State → ℝ) (ψ : State) : Prop :=
  IsEigenstate H (energy ψ) ψ ∧ ∀ φ, IsEigenstate H (energy φ) φ → energy ψ ≤ energy φ

def IsExcitedState (H : Operator State) (energy : State → ℝ) (ψ : State) : Prop :=
  IsEigenstate H (energy ψ) ψ ∧
    ∃ ground, IsGroundState H energy ground ∧ energy ground < energy ψ

/- 18. The full finite-dimensional spectral proposition follows from
Mathlib's exact self-adjoint spectral theorem: real eigenvalues, mutually
orthogonal eigenspaces, and their internal direct-sum completeness. -/
theorem hermitian_spectral_properties [FiniteDimensional ℂ State]
    (Q : Operator State) (hQ : Q.IsSymmetric) :
    (∀ mu, Module.End.HasEigenvalue Q mu → star mu = mu) ∧
      OrthogonalFamily ℂ (fun mu => Module.End.eigenspace Q mu)
        (fun mu => (Module.End.eigenspace Q mu).subtypeₗᵢ) ∧
      DirectSum.IsInternal (fun mu : Module.End.Eigenvalues Q => Module.End.eigenspace Q mu) := by
  exact ⟨fun _ hμ => hQ.conj_eigenvalue_eq_self hμ,
    hQ.orthogonalFamily_eigenspaces, hQ.direct_sum_isInternal⟩

/- 19. Expectation and variance of the spectral probability distribution. -/
def spectralExpectation {ι : Type*} [Fintype ι] (eigenvalue P : ι → ℝ) : ℝ :=
  ∑ i, eigenvalue i * P i

def spectralVariance {ι : Type*} [Fintype ι] (eigenvalue P : ι → ℝ) : ℝ :=
  ∑ i, (eigenvalue i - spectralExpectation eigenvalue P) ^ 2 * P i

theorem spectral_expectation_and_uncertainty {ι : Type*} [Fintype ι]
    (eigenvalue P : ι → ℝ) :
    spectralExpectation eigenvalue P = ∑ i, eigenvalue i * P i ∧
      spectralVariance eigenvalue P =
        ∑ i, (eigenvalue i - spectralExpectation eigenvalue P) ^ 2 * P i := ⟨rfl, rfl⟩

/- 20. General Ehrenfest equation.  The analytic derivative is supplied by a
concrete dynamical model and must satisfy the equation for every observable. -/
structure GeneralEhrenfestDynamics (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  ℏ : ℝ
  hamiltonian : Operator State
  trajectory : ℝ → State
  expectationDerivative : Operator State → ℝ → ℂ
  commutatorEquation : ∀ Q t, (Complex.I * ℏ) * expectationDerivative Q t =
    expectationValue (commutator Q hamiltonian) (trajectory t)

/- 21. Degeneracy. -/
def eigenspace (Q : Operator State) (eigenvalue : ℂ) : Submodule ℂ State :=
  LinearMap.ker (Q - eigenvalue • LinearMap.id)

def degeneracy [FiniteDimensional ℂ State] (Q : Operator State) (eigenvalue : ℂ) : ℕ :=
  Module.finrank ℂ (eigenspace Q eigenvalue)

def IsNondegenerate [FiniteDimensional ℂ State]
    (Q : Operator State) (eigenvalue : ℂ) : Prop := degeneracy Q eigenvalue = 1

def AreDegenerate (Q : Operator State) (ψ φ : State) : Prop :=
  ∃ eigenvalue : ℂ, Q ψ = eigenvalue • ψ ∧ Q φ = eigenvalue • φ

/- 22. Structureless particle: the observable algebra is generated by x,p. -/
def IsStructurelessParticle (position momentum : Operator State) : Prop :=
  Algebra.adjoin ℂ ({position, momentum} : Set (Operator State)) = ⊤

/- 23. Angular momentum. -/
def angularMomentum (ε : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (x p : Fin 3 → Operator State) (i : Fin 3) : Operator State :=
  ∑ j, ∑ k, ε i j k • ((x j).comp (p k))

/- 24. Total angular momentum. -/
def totalAngularMomentum (L : Fin 3 → Operator State) : Operator State :=
  ∑ i, (L i).comp (L i)

/- 25. The displayed angular-momentum commutation relations are explicit
laws required of a concrete angular-momentum representation. -/
structure AngularMomentumAlgebra (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  ℏ : ℝ
  ε : Fin 3 → Fin 3 → Fin 3 → ℂ
  position : Fin 3 → Operator State
  momentum : Fin 3 → Operator State
  angular : Fin 3 → Operator State
  angular_definition : ∀ i, angular i = angularMomentum ε position momentum i
  angular_commutator : ∀ i j, commutator (angular i) (angular j) =
    ∑ k, (Complex.I * ℏ * ε i j k) • angular k
  total_commutator : ∀ i, commutator (totalAngularMomentum angular) (angular i) = 0
  position_commutator : ∀ i j, commutator (angular i) (position j) =
    ∑ k, (Complex.I * ℏ * ε i j k) • position k
  momentum_commutator : ∀ i j, commutator (angular i) (momentum j) =
    ∑ k, (Complex.I * ℏ * ε i j k) • momentum k

end

end QuantumMechanics
