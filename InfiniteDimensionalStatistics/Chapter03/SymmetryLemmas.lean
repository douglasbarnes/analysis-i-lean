/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.RademacherLemmas

/-!
# Chapter 3: Elementary symmetry and copy lemmas

Structural facts about independent copies and random variables symmetric about
zero.  These form the assumption layer for the Lévy and symmetrisation
inequalities.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace InfiniteDimensionalStatistics
namespace Chapter03

section IndependentCopies

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {P : Measure Ω} {X X' : Ω → S}

/-- The independent-copy relation is symmetric. -/
theorem AreIndependentCopies.symm
    (h : AreIndependentCopies P X X') :
    AreIndependentCopies P X' X := by
  exact ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

/-- Independent copies have the same push-forward law. -/
theorem AreIndependentCopies.map_eq
    (h : AreIndependentCopies P X X') :
    Measure.map X P = Measure.map X' P :=
  h.2.2.1

/-- Independent copies are independent random variables. -/
theorem AreIndependentCopies.indepFun
    (h : AreIndependentCopies P X X') :
    IndepFun X X' P :=
  h.2.2.2

end IndependentCopies

section SymmetricLaws

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {X : Ω → ℝ}

/-- The zero random variable is symmetric about zero. -/
@[simp] theorem isSymmetricAboutZero_zero :
    IsSymmetricAboutZero P (fun _ => 0) := by
  constructor
  · fun_prop
  · rfl

/-- The negative of a symmetric random variable is symmetric. -/
theorem IsSymmetricAboutZero.neg
    (hX : IsSymmetricAboutZero P X) :
    IsSymmetricAboutZero P (fun ω => -X ω) := by
  constructor
  · exact hX.1.neg
  · simpa using hX.2.symm

/-- A symmetric random variable has the same law as its negative. -/
theorem IsSymmetricAboutZero.map_eq
    (hX : IsSymmetricAboutZero P X) :
    Measure.map X P = Measure.map (fun ω => -X ω) P :=
  hX.2

end SymmetricLaws

end Chapter03
end InfiniteDimensionalStatistics
