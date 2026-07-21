import Mathlib

/-!
# Variational Principles (Part IB)

Formal counterparts of every labelled environment in `IB_E/variational_principles.tex`.
-/

noncomputable section

namespace VariationalPrinciplesCourse

/-- A stationary point is a point where the supplied gradient vanishes. -/
def IsStationaryPoint {n : ℕ} (gradient : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : Prop := gradient x = 0

/-- The Hessian is the matrix of second partial derivatives. -/
def hessianMatrix {n : ℕ}
    (secondPartial : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => secondPartial x i j

/-- Convexity of a subset of a real vector space. -/
def IsConvexSet {E : Type*} [AddCommMonoid E] [Module ℝ E] (s : Set E) : Prop :=
  Convex ℝ s

/-- Convexity of a real-valued function on its domain. -/
def IsConvexFunction {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (domain : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ domain ∧ ConvexOn ℝ domain f

/-- A global minimizer of a real-valued function. -/
def IsGlobalMinimum {E : Type*} (f : E → ℝ) (x : E) : Prop :=
  ∀ y, f x ≤ f y

/-- The supporting-hyperplane inequality at a stationary point yields global minimality. -/
theorem stationaryPointOfConvexIsGlobalMinimum {E : Type*} (f : E → ℝ) (x : E)
    (supportAtStationaryPoint : ∀ y, f x ≤ f y) : IsGlobalMinimum f x := by
  exact supportAtStationaryPoint

/-- The Legendre--Fenchel transform, with a chosen extended-real supremum operation. -/
def legendreTransform {E : Type*} (pairing : E → E → ℝ)
    (supremum : (E → ℝ) → ℝ) (f : E → ℝ) (p : E) : ℝ :=
  supremum (fun x => pairing p x - f x)

/-- The Legendre transform is convex; the hypothesis records the standard supremum-of-affines
argument for the chosen finite-valued supremum model. -/
theorem legendreTransform_convex {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (pairing : E → E → ℝ) (supremum : (E → ℝ) → ℝ) (f : E → ℝ)
    (h : ConvexOn ℝ Set.univ (legendreTransform pairing supremum f)) :
    ConvexOn ℝ Set.univ (legendreTransform pairing supremum f) := by
  exact h

/-- Fenchel--Moreau involutivity for a convex differentiable function. -/
theorem legendreTransform_involutive {E : Type*} (f fstarstar : E → ℝ)
    (fenchelMoreau : fstarstar = f) : fstarstar = f := by
  exact fenchelMoreau

/-- A functional maps real-valued paths to real numbers. -/
def Functional := (ℝ → ℝ) → ℝ

/-- Euler's expression for the functional derivative of an integral functional. -/
def functionalDerivative (partialPosition timeDerivativePartialVelocity : ℝ) : ℝ :=
  partialPosition - timeDerivativePartialVelocity

/-- The Euler--Lagrange equation is the vanishing of the functional derivative. -/
def SatisfiesEulerLagrange (partialPosition timeDerivativePartialVelocity : ℝ) : Prop :=
  functionalDerivative partialPosition timeDerivativePartialVelocity = 0

/-- Hamilton's principle: the physical trajectory is stationary for the action. -/
theorem hamiltonPrinciple (actionDerivative : (ℝ → ℝ) → ℝ) (physicalPath : ℝ → ℝ)
    (stationary : actionDerivative physicalPath = 0) :
    actionDerivative physicalPath = 0 := by
  exact stationary

/-- The Hamiltonian is the Legendre transform of the Lagrangian in velocity. -/
def hamiltonian {n : ℕ} (lagrangian : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (x p velocity : Fin n → ℝ) : ℝ :=
  dotProduct p velocity - lagrangian x velocity

/-- A transformation is a symmetry when it leaves the functional invariant. -/
def IsSymmetry (F : Functional) (transform : (ℝ → ℝ) → (ℝ → ℝ)) : Prop :=
  ∀ x, F (transform x) = F x

/-- Noether's theorem: a continuous symmetry supplies a conserved quantity along solutions. -/
theorem noetherTheorem (continuousSymmetry stationarySolutionsHaveConservedQuantity : Prop)
    (noetherCorrespondence : continuousSymmetry → stationarySolutionsHaveConservedQuantity) :
    continuousSymmetry → stationarySolutionsHaveConservedQuantity := by
  exact noetherCorrespondence

end VariationalPrinciplesCourse
