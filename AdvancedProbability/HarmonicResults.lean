import AdvancedProbability.BrownianMotion

noncomputable section

open Set

namespace AdvancedProbability

universe u

/-- Source 108: uniqueness for the Dirichlet problem follows from the maximum principle.

The only operator-level input is linearity of the supplied Laplacian under subtraction. Applying the
maximum principle to `u - v` and `v - u` gives both pointwise inequalities in the domain. -/
theorem DirichletUniquenessTheorem
    {E : Type u} [TopologicalSpace E] {laplacian : (E → ℝ) → E → ℝ}
    {D : Set E} {u v : E → ℝ}
    (hlap_sub : ∀ f g x,
      laplacian (fun y ↦ f y - g y) x = laplacian f x - laplacian g x)
    (hmax : MaximumPrinciple laplacian D)
    (hu : IsHarmonic laplacian D u) (hv : IsHarmonic laplacian D v)
    (hucont : ContinuousOn u (closure D)) (hvcont : ContinuousOn v (closure D))
    (hboundary : ∀ x, x ∈ frontier D → u x = v x) :
    ∀ x, x ∈ D → u x = v x := by
  have huv_harmonic : IsHarmonic laplacian D (fun y ↦ u y - v y) := by
    intro x hx
    rw [hlap_sub, hu x hx, hv x hx, sub_self]
  have hvu_harmonic : IsHarmonic laplacian D (fun y ↦ v y - u y) := by
    intro x hx
    rw [hlap_sub, hv x hx, hu x hx, sub_self]
  have huv_boundary : ∀ x, x ∈ frontier D → u x - v x ≤ 0 := by
    intro x hx
    rw [hboundary x hx, sub_self]
  have hvu_boundary : ∀ x, x ∈ frontier D → v x - u x ≤ 0 := by
    intro x hx
    rw [hboundary x hx, sub_self]
  intro x hx
  have huv_nonpos := hmax (fun y ↦ u y - v y) huv_harmonic
    (hucont.sub hvcont) 0 huv_boundary x hx
  have hvu_nonpos := hmax (fun y ↦ v y - u y) hvu_harmonic
    (hvcont.sub hucont) 0 hvu_boundary x hx
  exact le_antisymm (sub_nonpos.mp huv_nonpos) (sub_nonpos.mp hvu_nonpos)

end AdvancedProbability
