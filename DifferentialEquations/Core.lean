import Mathlib

/-!
# Part IA Differential Equations

Course-facing definitions and proved elementary wrappers.  Informal source
statements which are false without regularity hypotheses (notably Taylor and
L'Hopital), or which treat distributions as ordinary functions, are represented
by Mathlib's rigorous notions rather than copied literally.
-/

open Filter Matrix MeasureTheory
open scoped Topology

namespace DifferentialEquations

noncomputable section

/-! ## One-variable calculus -/

def DerivativeAt (f : ℝ → ℝ) (x d : ℝ) : Prop := HasDerivAt f d x

noncomputable def firstDerivative (f : ℝ → ℝ) : ℝ → ℝ := deriv f

noncomputable def secondDerivative (f : ℝ → ℝ) : ℝ → ℝ := deriv (deriv f)

def LittleOAt (f g : ℝ → ℝ) (x : ℝ) : Prop := f =o[𝓝 x] g

def BigOAt (f g : ℝ → ℝ) (x : ℝ) : Prop := f =O[𝓝 x] g

def AntiderivativeOf (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x

theorem derivative_first_order_approximation {f : ℝ → ℝ} {x d : ℝ}
    (h : HasDerivAt f d x) :
    (fun y => f y - f x - d * (y - x)) =o[𝓝 x] (fun y => y - x) := by
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_comm] using h.isLittleO

theorem chain_rule {F g : ℝ → ℝ} {x g' F' : ℝ}
    (hF : HasDerivAt F F' (g x)) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => F (g y)) (F' * g') x := by
  simpa [mul_comm] using hF.comp x hg

theorem product_rule {u v : ℝ → ℝ} {x u' v' : ℝ}
    (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun y => u y * v y) (u' * v x + u x * v') x := by
  simpa using hu.mul hv

def LeibnizFormulaAt (n : ℕ) (u v : ℝ → ℝ) (x : ℝ) : Prop :=
  iteratedDeriv n (fun y => u y * v y) x =
    ∑ r ∈ Finset.range (n + 1),
      (n.choose r : ℝ) * iteratedDeriv r u x * iteratedDeriv (n - r) v x

/- The source's L'Hopital statement omits the non-vanishing and derivative-ratio
conditions.  This small wrapper records the valid final limit passage used in
its argument. -/
theorem quotient_limit {f g : ℝ → ℝ} {l : Filter ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun x => f x / g x) l (𝓝 (a / b)) := by
  exact hf.div hg (by simpa using hb)

/-! ## Partial derivatives and elementary ODE vocabulary -/

def PartialDerivativeXAt (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (d : ℝ) : Prop :=
  HasDerivAt (fun x => f (x, p.2)) d p.1

def PartialDerivativeYAt (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (d : ℝ) : Prop :=
  HasDerivAt (fun y => f (p.1, y)) d p.2

noncomputable def partialX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

noncomputable def partialY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => f (p.1, y)) p.2

def Eigenfunction (f : ℝ → ℝ) (λ : ℝ) : Prop :=
  ∀ x, HasDerivAt f (λ * f x) x

theorem exp_is_eigenfunction (lam : ℝ) :
    Eigenfunction (fun x : ℝ => Real.exp (lam * x)) lam := by
  intro x
  convert (Real.hasDerivAt_exp (lam * x)).comp x
    (((hasDerivAt_id x).const_mul lam)) using 1 <;> ring

def LinearODE (a b forcing : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt y ((forcing x - b x * y x) / a x) x

def HomogeneousODE (equation : (ℝ → ℝ) → Prop) : Prop := equation 0

def ConstantCoefficientSecondOrder (a b c : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt (deriv y) (-(b * deriv y x + c * y x) / a) x

def FirstOrderODE (F : ℝ → ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt y (F x (y x)) x

def characteristicPolynomial (a b c lam : ℝ) : ℝ := a * lam ^ 2 + b * lam + c

theorem exp_solution_constantCoefficient {a b c lam : ℝ}
    (hroot : characteristicPolynomial a b c lam = 0) :
    ∀ x, a * (lam ^ 2 * Real.exp (lam * x)) +
        b * (lam * Real.exp (lam * x)) + c * Real.exp (lam * x) = 0 := by
  intro x
  calc
    a * (lam ^ 2 * Real.exp (lam * x)) + b * (lam * Real.exp (lam * x)) +
        c * Real.exp (lam * x) =
        characteristicPolynomial a b c lam * Real.exp (lam * x) := by
          simp only [characteristicPolynomial]
          ring
    _ = 0 := by rw [hroot, zero_mul]

def SeparableFirstOrder (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ p q : ℝ → ℝ, ∀ x y, F x y = p x * q y

def ExactDifferential (P Q : ℝ × ℝ → ℝ) : Prop :=
  ∃ f : ℝ × ℝ → ℝ,
    (∀ p, PartialDerivativeXAt f p (P p)) ∧
    ∀ p, PartialDerivativeYAt f p (Q p)

theorem exact_of_potential {P Q f : ℝ × ℝ → ℝ}
    (hx : ∀ p, PartialDerivativeXAt f p (P p))
    (hy : ∀ p, PartialDerivativeYAt f p (Q p)) : ExactDifferential P Q :=
  ⟨f, hx, hy⟩

def SimplyConnected (D : Set (ℝ × ℝ)) : Prop := IsSimplyConnected D

def Equilibrium (F : ℝ → ℝ) (c : ℝ) : Prop := F c = 0

def AttractingEquilibrium (flow : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ y, |y - c| < ε → Tendsto (fun t => flow t y) atTop (𝓝 c)

def AutonomousSystem (F : ℝ → ℝ) := F

/-! ## Wronskians and Abel's dichotomy -/

def wronskian (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

def IndependentSolutions (y₁ y₂ : ℝ → ℝ) : Prop :=
  ∃ x, wronskian y₁ y₂ x ≠ 0

theorem abel_dichotomy {W P : ℝ → ℝ} {C : ℝ}
    (hW : ∀ x, W x = C * Real.exp (-P x)) :
    (∀ x, W x = 0) ∨ (∀ x, W x ≠ 0) := by
  by_cases hC : C = 0
  · left
    intro x
    simp [hW x, hC]
  · right
    intro x
    rw [hW x]
    exact mul_ne_zero hC (Real.exp_ne_zero _)

def EquidimensionalSecondOrder (a b c : ℝ) (forcing y : ℝ → ℝ) : Prop :=
  ∀ x, a * x ^ 2 * deriv (deriv y) x + b * x * deriv y x + c * y x = forcing x

/-! ## Generalised functions and series points -/

def diracDelta (x : ℝ) : Measure ℝ := Measure.dirac x

def heaviside (x : ℝ) : ℝ := if x < 0 then 0 else 1

@[simp] theorem heaviside_of_neg {x : ℝ} (h : x < 0) : heaviside x = 0 := by simp [heaviside, h]

@[simp] theorem heaviside_of_nonneg {x : ℝ} (h : 0 ≤ x) : heaviside x = 1 := by
  simp [heaviside, not_lt.mpr h]

def OrdinaryPoint (p q r : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  AnalyticAt ℝ (fun x => q x / p x) x₀ ∧ AnalyticAt ℝ (fun x => r x / p x) x₀

def SingularPoint (p q r : ℝ → ℝ) (x₀ : ℝ) : Prop := ¬ OrdinaryPoint p q r x₀

def RegularSingularPoint (p q r : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  SingularPoint p q r x₀ ∧
    AnalyticAt ℝ (fun x => (x - x₀) * q x / p x) x₀ ∧
    AnalyticAt ℝ (fun x => (x - x₀) ^ 2 * r x / p x) x₀

/-! ## Several-variable calculus and the two-dimensional Hessian test -/

def directionalDerivative (f : (Fin 2 → ℝ) → ℝ) (x v : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ f x v

def gradient (f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

def hessian (f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  deriv (fun t => gradient f (Function.update x j t) i) (x j)

def quadraticForm₂ (a b c x y : ℝ) : ℝ := a * x ^ 2 + 2 * b * x * y + c * y ^ 2

def leadingPrincipalMinors₂ (a b c : ℝ) : ℝ × ℝ := (a, a * c - b ^ 2)

def PositiveDefinite₂ (a b c : ℝ) : Prop :=
  ∀ x y, (x ≠ 0 ∨ y ≠ 0) → 0 < quadraticForm₂ a b c x y

def NegativeDefinite₂ (a b c : ℝ) : Prop :=
  ∀ x y, (x ≠ 0 ∨ y ≠ 0) → quadraticForm₂ a b c x y < 0

theorem positiveDefinite₂_of_leadingMinors {a b c : ℝ} (ha : 0 < a)
    (hdet : 0 < a * c - b ^ 2) : PositiveDefinite₂ a b c := by
  intro x y hxy
  have hc : 0 < c := by nlinarith [sq_nonneg b]
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := by simpa using hxy
    simp only [quadraticForm₂, mul_zero, add_zero]
    simpa using mul_pos ha (sq_pos_of_ne_zero hx)
  · have hsquare : 0 ≤ (a * x + b * y) ^ 2 := sq_nonneg _
    have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    dsimp [quadraticForm₂]
    nlinarith

theorem positiveDefinite₂_iff_leadingMinors {a b c : ℝ} :
    PositiveDefinite₂ a b c ↔ 0 < a ∧ 0 < a * c - b ^ 2 := by
  constructor
  · intro h
    have ha : 0 < a := by
      simpa [quadraticForm₂] using h 1 0 (Or.inl one_ne_zero)
    have hv := h (-b) a (Or.inr (ne_of_gt ha))
    dsimp [quadraticForm₂] at hv
    constructor
    · exact ha
    · nlinarith
  · rintro ⟨ha, hdet⟩
    exact positiveDefinite₂_of_leadingMinors ha hdet

theorem negativeDefinite₂_of_leadingMinors {a b c : ℝ} (ha : a < 0)
    (hdet : 0 < a * c - b ^ 2) : NegativeDefinite₂ a b c := by
  intro x y hxy
  have hpos : PositiveDefinite₂ (-a) (-b) (-c) := by
    apply positiveDefinite₂_of_leadingMinors
    · linarith
    · nlinarith
  have := hpos x y hxy
  dsimp [quadraticForm₂] at this ⊢
  nlinarith

theorem negativeDefinite₂_iff_leadingMinors {a b c : ℝ} :
    NegativeDefinite₂ a b c ↔ a < 0 ∧ 0 < a * c - b ^ 2 := by
  constructor
  · intro h
    have hpos : PositiveDefinite₂ (-a) (-b) (-c) := by
      intro x y hxy
      have := h x y hxy
      dsimp [quadraticForm₂] at this ⊢
      nlinarith
    have hm := positiveDefinite₂_iff_leadingMinors.mp hpos
    constructor <;> nlinarith [hm.1, hm.2]
  · rintro ⟨ha, hdet⟩
    exact negativeDefinite₂_of_leadingMinors ha hdet

def Equilibrium₂ (F : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (x : Fin 2 → ℝ) : Prop :=
  F x = 0

end DifferentialEquations
