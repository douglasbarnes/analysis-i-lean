/-
Copyright (c) 2026 Douglas Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Douglas Barnes
-/

import InfiniteDimensionalStatistics.Chapter03.LocalClassPermanence

/-!
# Chapter 3: Prelinearity lemmas

Algebraic closure and restriction properties of the prelinear maps introduced
on p. 251.  These facts isolate the finite-relation component of the suitable
prelinear bridge construction.
-/

noncomputable section

open scoped BigOperators
open Finset Set

namespace InfiniteDimensionalStatistics
namespace Chapter03

section Prelinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {C D : Set E}

/-- Restrict a scalar map on `C` to a subset `D`. -/
def restrictPrelinearMap (hDC : D ⊆ C) (G : C → ℝ) : D → ℝ :=
  G ∘ fun d : D => (⟨d.1, hDC d.2⟩ : C)

/-- The zero map is prelinear on every set. -/
theorem isPrelinearOn_zero (C : Set E) :
    IsPrelinearOn C (fun _ => 0) := by
  intro n c a hrel
  simp

/-- Sums of prelinear maps are prelinear. -/
theorem IsPrelinearOn.add {G H : C → ℝ}
    (hG : IsPrelinearOn C G) (hH : IsPrelinearOn C H) :
    IsPrelinearOn C (fun c => G c + H c) := by
  intro n c a hrel
  simp_rw [mul_add, Finset.sum_add_distrib, hG n c a hrel, hH n c a hrel, add_zero]

/-- Scalar multiples of prelinear maps are prelinear. -/
theorem IsPrelinearOn.const_mul {G : C → ℝ}
    (hG : IsPrelinearOn C G) (r : ℝ) :
    IsPrelinearOn C (fun c => r * G c) := by
  intro n c a hrel
  calc
    ∑ i, a i * (r * G (c i)) = r * ∑ i, a i * G (c i) := by
      simp_rw [mul_left_comm, Finset.mul_sum]
    _ = 0 := by rw [hG n c a hrel, mul_zero]

/-- Restriction to a subset preserves prelinearity. -/
theorem IsPrelinearOn.restrict {G : C → ℝ}
    (hG : IsPrelinearOn C G) (hDC : D ⊆ C) :
    IsPrelinearOn D (restrictPrelinearMap hDC G) := by
  intro n c a hrel
  simpa [restrictPrelinearMap] using
    hG n (fun i => (⟨(c i).1, hDC (c i).2⟩ : C)) a hrel

/-- Every linear functional restricts to a prelinear map on an arbitrary set. -/
theorem LinearMap.isPrelinearOn (L : E →ₗ[ℝ] ℝ) (C : Set E) :
    IsPrelinearOn C (fun c => L c.1) := by
  intro n c a hrel
  have h := congrArg L hrel
  simpa using h

end Prelinear

end Chapter03
end InfiniteDimensionalStatistics
