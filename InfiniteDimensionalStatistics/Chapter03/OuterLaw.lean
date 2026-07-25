/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.SauerShelah
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Chapter 3: Outer convergence in law

Bounded-continuous test functions, inner expectation, asymptotic
measurability, outer convergence in law, and compact containment from Section
3.7.  These notions remain meaningful for nonmeasurable random maps.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Tests

variable {E : Type*} [TopologicalSpace E]

/-- A bounded continuous real test function. -/
def IsBoundedContinuousTest (h : E → ℝ) : Prop :=
  Continuous h ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M

end Tests

section Expectations

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Inner expectation, defined by duality from outer expectation. -/
def innerExpectationReal (P : Measure Ω) (f : Ω → ℝ) : EReal :=
  -outerExpectationReal P (fun ω ↦ -f ω)

/-- Outer/inner expectation gap. -/
def expectationMeasurabilityGap (P : Measure Ω) (f : Ω → ℝ) : EReal :=
  outerExpectationReal P f - innerExpectationReal P f

end Expectations

section OuterLaw

variable {Ω E : Type*} [MeasurableSpace Ω]
  [TopologicalSpace E] [MeasurableSpace E]

/--
Convergence in outer law to a supplied tight Borel random element.

Source: Definition 3.7.22, printed p. 243; specification id
`definition_3_7_22`.
-/
def ConvergesInOuterLaw
    (P : ℕ → Measure Ω) (X : ℕ → Ω → E)
    (Q : Measure Ω) (Y : Ω → E) : Prop :=
  ∀ h : E → ℝ, IsBoundedContinuousTest h →
    Tendsto
      (fun n ↦ outerExpectationReal (P n) (fun ω ↦ h (X n ω)))
      atTop
      (𝓝 (EReal.ofReal (∫ ω, h (Y ω) ∂Q)))

/-- Asymptotic measurability through bounded-continuous test functions. -/
def IsAsymptoticallyMeasurable
    (P : ℕ → Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ h : E → ℝ, IsBoundedContinuousTest h →
    Tendsto
      (fun n ↦ expectationMeasurabilityGap (P n) (fun ω ↦ h (X n ω)))
      atTop (𝓝 0)

/-- Event that a random element lies outside a compact set. -/
def outsideCompactEvent (X : Ω → E) (K : Set E) : Set Ω :=
  {ω | X ω ∉ K}

/--
Strong compact-containment form of asymptotic tightness in outer probability.
-/
def IsOuterAsymptoticallyTight
    (P : ℕ → Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : Set E, IsCompact K ∧
      ∃ N : ℕ, ∀ n ≥ N,
        outerProbability (P n) (outsideCompactEvent (X n) K) ≤ ENNReal.ofReal ε

/-- Finite-dimensional evaluation map at a finite family of indices. -/
def finiteEvaluation {T : Type*} {m : ℕ}
    (t : Fin m → T) (x : T → ℝ) : Fin m → ℝ :=
  fun i ↦ x (t i)

/-- Finite-dimensional convergence in outer law. -/
def FiniteDimensionalOuterConvergence {T : Type*}
    (P : ℕ → Measure Ω) (X : ℕ → Ω → T → ℝ)
    (Q : Measure Ω) (Y : Ω → T → ℝ) : Prop :=
  ∀ m : ℕ, ∀ t : Fin m → T,
    ConvergesInOuterLaw P
      (fun n ω ↦ finiteEvaluation t (X n ω)) Q
      (fun ω ↦ finiteEvaluation t (Y ω))

end OuterLaw

end Chapter03
end InfiniteDimensionalStatistics
