import Mathlib

/-!
# Part IB Quantum Mechanics

Formal counterparts of the 25 labelled environments in the source notes, in
their original order.  The analytic and physical assumptions of a quantum
model are explicit fields or predicates; none are introduced as logical
primitives.
-/

open scoped BigOperators ComplexConjugate

namespace QuantumMechanics

noncomputable section

variable {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]

abbrev Operator (State : Type*) [AddCommMonoid State] [Module ℂ State] :=
  State →ₗ[ℂ] State

/- 1. Time-independent Schrödinger equation. -/
def TimeIndependentSchrodinger (H : Operator State) (ψ : State) (E : ℂ) : Prop :=
  H ψ = E • ψ

/- 2. Time-dependent Schrödinger equation.  `timeDerivative` records the
chosen analytic derivative on the model's state-valued trajectories. -/
def TimeDependentSchrodinger (ℏ : ℝ) (H : Operator State)
    (timeDerivative Ψ : ℝ → State) : Prop :=
  ∀ t, (Complex.I * ℏ) • timeDerivative t = H (Ψ t)

/- 3. Stationary state. -/
def IsStationaryState (ℏ E : ℝ) (H : Operator State) (ψ : State)
    (Ψ : ℝ → State) : Prop :=
  TimeIndependentSchrodinger H ψ E ∧
    ∀ t, Ψ t = Complex.exp (-(Complex.I * (E * t / ℏ))) • ψ

/- 4. Probability density, current, and their conservation equation. -/
def probabilityDensity (Ψ : ℝ → ℝ → ℂ) (x t : ℝ) : ℝ := ‖Ψ t x‖ ^ 2

def probabilityCurrent (ℏ m : ℝ) (Ψ spatialDerivative : ℝ → ℝ → ℂ)
    (x t : ℝ) : ℂ :=
  -(Complex.I * (ℏ / (2 * m))) *
    (star (Ψ t x) * spatialDerivative t x - star (spatialDerivative t x) * Ψ t x)

def ProbabilityConservation (densityDerivative : ℝ → ℝ → ℝ)
    (currentDerivative : ℝ → ℝ → ℂ) : Prop :=
  ∀ x t, (densityDerivative t x : ℂ) = -currentDerivative t x

theorem probability_density_conservation
    {densityDerivative : ℝ → ℝ → ℝ} {currentDerivative : ℝ → ℝ → ℂ}
    (h : ProbabilityConservation densityDerivative currentDerivative) :
    ∀ x t, (densityDerivative t x : ℂ) = -currentDerivative t x := h

/- 5. Inner product. -/
def waveInner (φ ψ : State) : ℂ := ⟪φ, ψ⟫_ℂ

/- 6. Norm. -/
def waveNorm (ψ : State) : ℝ := ‖ψ‖

theorem waveNorm_sq (ψ : State) : waveNorm ψ ^ 2 = ‖ψ‖ ^ 2 := rfl

/- 7. Expectation value. -/
def expectationValue (Q : Operator State) (ψ : State) : ℂ := ⟪ψ, Q ψ⟫_ℂ

/- 8. Uncertainty. -/
def uncertaintySq (Q : Operator State) (ψ : State) : ℝ :=
  ‖Q ψ - expectationValue Q ψ • ψ‖ ^ 2

def uncertainty (Q : Operator State) (ψ : State) : ℝ :=
  Real.sqrt (uncertaintySq Q ψ)

/- 9. Hermitian operator. -/
def IsHermitian (Q : Operator State) : Prop :=
  ∀ φ ψ, ⟪φ, Q ψ⟫_ℂ = ⟪Q φ, ψ⟫_ℂ

/- 10. The standard position, momentum, and real-potential Hamiltonian are
Hermitian: these domain-sensitive facts are explicit obligations of a model. -/
structure SchrodingerRepresentation (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  position : Operator State
  momentum : Operator State
  hamiltonian : Operator State
  position_hermitian : IsHermitian position
  momentum_hermitian : IsHermitian momentum
  realPotential_hamiltonian_hermitian : IsHermitian hamiltonian

theorem standard_operators_hermitian (M : SchrodingerRepresentation State) :
    IsHermitian M.position ∧ IsHermitian M.momentum ∧ IsHermitian M.hamiltonian :=
  ⟨M.position_hermitian, M.momentum_hermitian,
    M.realPotential_hamiltonian_hermitian⟩

/- 11. Cauchy--Schwarz inequality. -/
theorem wave_cauchy_schwarz (ψ φ : State) :
    ‖waveInner ψ φ‖ ≤ waveNorm ψ * waveNorm φ := by
  simpa [waveInner, waveNorm] using norm_inner_le_norm ψ φ

/- 12. Ehrenfest's theorem for position and momentum. -/
structure EhrenfestModel (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  mass : ℝ
  mass_ne_zero : mass ≠ 0
  position momentum potentialDerivative : Operator State
  trajectory : ℝ → State
  positionExpectationDerivative momentumExpectationDerivative : ℝ → ℂ
  position_law : ∀ t,
    positionExpectationDerivative t = (1 / mass : ℝ) • expectationValue momentum (trajectory t)
  momentum_law : ∀ t,
    momentumExpectationDerivative t = -expectationValue potentialDerivative (trajectory t)

theorem ehrenfest_position_momentum (M : EhrenfestModel State) (t : ℝ) :
    M.positionExpectationDerivative t =
        (1 / M.mass : ℝ) • expectationValue M.momentum (M.trajectory t) ∧
      M.momentumExpectationDerivative t =
        -expectationValue M.potentialDerivative (M.trajectory t) :=
  ⟨M.position_law t, M.momentum_law t⟩

/- 13. Heisenberg's uncertainty principle. -/
structure CanonicalUncertaintyModel (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  ℏ : ℝ
  position momentum : Operator State
  normalized : State → Prop
  uncertainty_bound : ∀ ψ, normalized ψ →
    ℏ / 2 ≤ uncertainty position ψ * uncertainty momentum ψ

theorem heisenberg_uncertainty (M : CanonicalUncertaintyModel State)
    {ψ : State} (hψ : M.normalized ψ) :
    M.ℏ / 2 ≤ uncertainty M.position ψ * uncertainty M.momentum ψ :=
  M.uncertainty_bound ψ hψ

/- 14. Commutator, including the canonical commutation relation as a model
predicate. -/
def commutator (Q S : Operator State) : Operator State := Q.comp S - S.comp Q

def CanonicalCommutation (ℏ : ℝ) (x p : Operator State) : Prop :=
  commutator x p = (Complex.I * ℏ) • LinearMap.id

/- 15. Wavepacket. -/
def IsWavepacket (localized : State → Prop) (ψ : State) : Prop := localized ψ

/- 16. Gaussian wavepacket. -/
def IsGaussianWavepacket (α : ℝ) (γ : ℝ → ℂ) (Ψ : ℝ → ℝ → ℂ) : Prop :=
  ∀ x t, Ψ t x =
    ((α / Real.pi) ^ (1 / 4 : ℝ) : ℝ) •
      (1 / Complex.sqrt (γ t)) * Complex.exp (-(x ^ 2 : ℂ) / (2 * γ t))

/- 17. Ground and excited states. -/
def IsEigenstate (H : Operator State) (E : ℝ) (ψ : State) : Prop := H ψ = E • ψ

def IsGroundState (H : Operator State) (energy : State → ℝ) (ψ : State) : Prop :=
  IsEigenstate H (energy ψ) ψ ∧ ∀ φ, IsEigenstate H (energy φ) φ → energy ψ ≤ energy φ

def IsExcitedState (H : Operator State) (energy : State → ℝ) (ψ : State) : Prop :=
  IsEigenstate H (energy ψ) ψ ∧
    ∃ ground, IsGroundState H energy ground ∧ energy ground < energy ψ

/- 18. Spectral properties of a Hermitian observable.  Completeness is finite
in this course model and is represented by an eigenbasis indexed by `ι`. -/
structure HermitianSpectralData (ι : Type*) [Fintype ι] (State : Type*)
    [NormedAddCommGroup State] [InnerProductSpace ℂ State] where
  observable : Operator State
  eigenvalue : ι → ℝ
  eigenvector : Basis ι ℂ State
  eigen_equation : ∀ i, observable (eigenvector i) = eigenvalue i • eigenvector i
  orthogonal : ∀ i j, i ≠ j → ⟪eigenvector i, eigenvector j⟫_ℂ = 0
  hermitian : IsHermitian observable

theorem hermitian_spectral_properties {ι : Type*} [Fintype ι]
    (D : HermitianSpectralData ι State) :
    IsHermitian D.observable ∧
      (∀ i, D.observable (D.eigenvector i) = D.eigenvalue i • D.eigenvector i) ∧
      (∀ i j, i ≠ j → ⟪D.eigenvector i, D.eigenvector j⟫_ℂ = 0) ∧
      Function.Surjective D.eigenvector.repr := by
  refine ⟨D.hermitian, D.eigen_equation, D.orthogonal, ?_⟩
  exact D.eigenvector.repr.surjective

/- 19. Expectation and variance in a spectral probability distribution. -/
def spectralExpectation {ι : Type*} [Fintype ι] (λ probability : ι → ℝ) : ℝ :=
  ∑ i, λ i * probability i

def spectralVariance {ι : Type*} [Fintype ι] (λ probability : ι → ℝ) : ℝ :=
  ∑ i, (λ i - spectralExpectation λ probability) ^ 2 * probability i

theorem spectral_expectation_and_uncertainty {ι : Type*} [Fintype ι]
    (λ probability : ι → ℝ) :
    spectralExpectation λ probability = ∑ i, λ i * probability i ∧
      spectralVariance λ probability =
        ∑ i, (λ i - spectralExpectation λ probability) ^ 2 * probability i :=
  ⟨rfl, rfl⟩

/- 20. General Ehrenfest theorem. -/
def GeneralEhrenfestLaw (ℏ : ℝ) (H Q : Operator State)
    (Ψ : ℝ → State) (expectationDerivative : ℝ → ℂ) : Prop :=
  ∀ t, (Complex.I * ℏ) * expectationDerivative t =
    expectationValue (commutator Q H) (Ψ t)

theorem general_ehrenfest {ℏ : ℝ} {H Q : Operator State} {Ψ : ℝ → State}
    {expectationDerivative : ℝ → ℂ}
    (h : GeneralEhrenfestLaw ℏ H Q Ψ expectationDerivative) (t : ℝ) :
    (Complex.I * ℏ) * expectationDerivative t =
      expectationValue (commutator Q H) (Ψ t) := h t

/- 21. Degeneracy. -/
def eigenspace (Q : Operator State) (λ : ℂ) : Submodule ℂ State :=
  LinearMap.ker (Q - λ • LinearMap.id)

def degeneracy [FiniteDimensional ℂ State] (Q : Operator State) (λ : ℂ) : ℕ :=
  Module.finrank ℂ (eigenspace Q λ)

def IsNondegenerate [FiniteDimensional ℂ State] (Q : Operator State) (λ : ℂ) : Prop :=
  degeneracy Q λ = 1

def AreDegenerate (Q : Operator State) (ψ φ : State) : Prop :=
  ∃ λ, Q ψ = λ • ψ ∧ Q φ = λ • φ

/- 22. Structureless particle. -/
def IsStructurelessParticle (generatedByPositionMomentum : Operator State → Prop) : Prop :=
  ∀ Q, generatedByPositionMomentum Q

/- 23. Angular momentum.  `ε` is the Levi--Civita tensor of the coordinate
system; the displayed component formula is used directly. -/
def angularMomentum (ε : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (x p : Fin 3 → Operator State) (i : Fin 3) : Operator State :=
  ∑ j, ∑ k, (ε i j k) • ((x j).comp (p k))

/- 24. Total angular momentum. -/
def totalAngularMomentum (L : Fin 3 → Operator State) : Operator State :=
  ∑ i, (L i).comp (L i)

/- 25. Angular-momentum commutation relations. -/
structure AngularMomentumAlgebra (State : Type*) [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] where
  ℏ : ℝ
  ε : Fin 3 → Fin 3 → Fin 3 → ℂ
  position momentum angular : Fin 3 → Operator State
  angular_commutator : ∀ i j,
    commutator (angular i) (angular j) =
      ∑ k, (Complex.I * ℏ * ε i j k) • angular k
  total_commutator : ∀ i,
    commutator (totalAngularMomentum angular) (angular i) = 0
  position_commutator : ∀ i j,
    commutator (angular i) (position j) =
      ∑ k, (Complex.I * ℏ * ε i j k) • position k
  momentum_commutator : ∀ i j,
    commutator (angular i) (momentum j) =
      ∑ k, (Complex.I * ℏ * ε i j k) • momentum k

theorem angular_momentum_relations (A : AngularMomentumAlgebra State) :
    (∀ i j, commutator (A.angular i) (A.angular j) =
      ∑ k, (Complex.I * A.ℏ * A.ε i j k) • A.angular k) ∧
    (∀ i, commutator (totalAngularMomentum A.angular) (A.angular i) = 0) ∧
    (∀ i j, commutator (A.angular i) (A.position j) =
      ∑ k, (Complex.I * A.ℏ * A.ε i j k) • A.position k) ∧
    (∀ i j, commutator (A.angular i) (A.momentum j) =
      ∑ k, (Complex.I * A.ℏ * A.ε i j k) • A.momentum k) :=
  ⟨A.angular_commutator, A.total_commutator,
    A.position_commutator, A.momentum_commutator⟩

end

end QuantumMechanics
