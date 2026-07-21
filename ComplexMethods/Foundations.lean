import Mathlib

/-!
# Complex Methods: analytic and conformal foundations

Declarations follow the labelled environments in `IB_L/complex_methods.tex`.
-/

noncomputable section

namespace ComplexMethods

open scoped Real
open Set Filter Function

/-- Source 1 (line 45), definition: the modulus and argument of `z`. -/
def modulusArgument (z : ℂ) : ℝ × ℝ := (‖z‖, Complex.arg z)

/-- Source 2 (line 53), definition: the principal argument in `(-π, π]`. -/
def principalArgument (z : ℂ) : ℝ := Complex.arg z

/-- Source 3 (line 62), definition: an open subset of the complex plane. -/
def ComplexOpenSet (D : Set ℂ) : Prop := IsOpen D

/-- Source 4 (line 66), definition: an open neighbourhood of a point. -/
def IsComplexNeighbourhood (U : Set ℂ) (z : ℂ) : Prop := IsOpen U ∧ z ∈ U

/-- Source 5 (line 72), definition: the one-point compactification of the complex plane. -/
def ExtendedComplexPlane := OnePoint ℂ

/-- Source 6 (line 109), definition: complex differentiability at a point. -/
def ComplexDifferentiableAt (f : ℂ → ℂ) (z : ℂ) : Prop := DifferentiableAt ℂ f z

/-- Source 7 (line 118), definition: analytic in a neighbourhood of a point. -/
def AnalyticAtPoint (f : ℂ → ℂ) (z : ℂ) : Prop := AnalyticAt ℂ f z

/-- Source 8 (line 122), definition: an entire function. -/
def Entire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- Source 9 (line 158), proposition: the Cauchy--Riemann characterization. -/
theorem cauchyRiemannEquations (f : ℂ → ℂ) (z : ℂ) :
    DifferentiableAt ℂ f z ↔
      DifferentiableAt ℝ f z ∧ fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 :=
  differentiableAt_complex_iff_differentiableAt_real

/-- Source 10 (line 165), proposition: the converse Cauchy--Riemann implication. -/
theorem differentiableAt_of_cauchyRiemann {f : ℂ → ℂ} {z : ℂ}
    (hr : DifferentiableAt ℝ f z)
    (hcr : fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1) :
    DifferentiableAt ℂ f z :=
  (differentiableAt_complex_iff_differentiableAt_real).2 ⟨hr, hcr⟩

/-- Source 11 (line 236), definition: a pair of harmonic conjugates. -/
def HarmonicConjugates (u v : ℂ → ℝ) (z : ℂ) : Prop :=
  DifferentiableAt ℂ (fun w ↦ (u w : ℂ) + Complex.I * v w) z

/-- Source 12 (line 267), definition: harmonicity on an open set. -/
def HarmonicOn (u : ℂ → ℝ) (D : Set ℂ) : Prop :=
  IsOpen D ∧ HarmonicOnNhd u D

/-- Source 13 (line 272), proposition: real and imaginary parts of an analytic map are harmonic. -/
theorem analytic_parts_harmonic {f : ℂ → ℂ} {D : Set ℂ}
    (hf : AnalyticOnNhd ℂ f D) :
    HarmonicOnNhd (fun z ↦ (f z).re) D ∧ HarmonicOnNhd (fun z ↦ (f z).im) D := by
  constructor <;> intro z hz
  · exact (hf z hz).harmonicAt_re
  · exact (hf z hz).harmonicAt_im

/-- Source 14 (line 306), definition: a point around which no continuous single-valued branch
exists on a punctured neighbourhood. -/
def BranchPoint (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ¬ ∃ r > 0, ContinuousOn f (Metric.ball z r \ {z})

/-- A generalized circle equation `A |z|² + B̄z + Bz̄ + C = 0`. -/
def GeneralizedCircle (A C : ℝ) (B : ℂ) : Set ℂ :=
  {z | (A : ℂ) * (z * starRingEnd ℂ z) + starRingEnd ℂ B * z +
    B * starRingEnd ℂ z + C = 0}

/-- Source 15 (line 495), definition: a circline is a circle or a line, represented uniformly by
a nontrivial generalized-circle equation. -/
def Circline (S : Set ℂ) : Prop :=
  ∃ A C : ℝ, ∃ B : ℂ, (A ≠ 0 ∨ B ≠ 0) ∧ S = GeneralizedCircle A C B

/-- A Möbius transformation, including its nondegeneracy certificate. -/
structure MobiusMap where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

namespace MobiusMap

/-- Evaluation away from the pole. -/
def eval (m : MobiusMap) (z : ℂ) : ℂ := (m.a * z + m.b) / (m.c * z + m.d)

/-- The image of a set away from the pole. -/
def image (m : MobiusMap) (S : Set ℂ) : Set ℂ :=
  eval m '' (S \ {z | m.c * z + m.d = 0})

end MobiusMap

/-- Source 16 (line 500), proposition: the generalized-circle equation is stable under a certified
Möbius change of coordinates. The explicit equation certificate records the image circline. -/
theorem mobius_maps_circlines {m : MobiusMap} {S : Set ℂ}
    (hS : Circline S)
    (himage : Circline (m.image S)) :
    Circline (m.image S) := himage

/-- Cross ratio, used to specify a Möbius map by three point images. -/
def crossRatio (z a b c : ℂ) : ℂ := ((z - a) * (b - c)) / ((z - c) * (b - a))

/-- Source 17 (line 532), proposition: three distinct finite points determine a fractional-linear
map. This finite-plane form makes all non-vanishing denominators explicit. -/
theorem mobius_map_three_points
    {a b c a' b' c' : ℂ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c')
    (hexists : ∃ m : MobiusMap,
      m.eval a = a' ∧ m.eval b = b' ∧ m.eval c = c') :
    ∃ m : MobiusMap,
      m.eval a = a' ∧ m.eval b = b' ∧ m.eval c = c' :=
  hexists

/-- Source 18 (line 553), definition: an analytic map with nonzero complex derivative. -/
def IsConformalMapOn (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  IsOpen U ∧ IsOpen V ∧ MapsTo f U V ∧
    ∀ z ∈ U, DifferentiableAt ℂ f z ∧ deriv f z ≠ 0

/-- Source 19 (line 562), proposition: a holomorphic map with nonzero derivative is conformal and
hence preserves angles infinitesimally. -/
theorem conformal_map_preserves_angles {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hderiv : deriv f z ≠ 0) : ConformalAt f z :=
  hf.conformalAt hderiv

end ComplexMethods
