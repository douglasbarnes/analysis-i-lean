import Mathlib

open Filter Function Metric Set Topology
open scoped Topology NNReal

namespace AnalysisII

noncomputable section

/-- Analysis II source 53(i): Picard--Lindelöf existence on an admissible
closed interval.  `IsPicardLindelof` is precisely the source's continuity,
uniform spatial Lipschitz, vector-field bound, and time-radius hypotheses. -/
theorem source053_picard_lindelof_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self le_rfl)

/-- Analysis II source 53(i), uniqueness: two solutions through the same initial
point, remaining in the Picard--Lindelöf ball, agree on the whole interval. -/
theorem source053_picard_lindelof_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    {α β : ℝ → E}
    (hαc : ContinuousOn α (Icc tmin tmax))
    (hαd : ∀ t ∈ Ioo tmin tmax, HasDerivAt α (f t (α t)) t)
    (hαmem : ∀ t ∈ Ioo tmin tmax, α t ∈ closedBall x₀ a)
    (hβc : ContinuousOn β (Icc tmin tmax))
    (hβd : ∀ t ∈ Ioo tmin tmax, HasDerivAt β (f t (β t)) t)
    (hβmem : ∀ t ∈ Ioo tmin tmax, β t ∈ closedBall x₀ a)
    (hinit : α t₀ = β t₀) : EqOn α β (Icc tmin tmax) := by
  apply ODE_solution_unique_of_mem_Icc
    (v := f) (s := fun _ => closedBall x₀ a) (K := K)
    (t₀ := (t₀ : ℝ))
  · intro t ht
    exact hf.lipschitzOnWith t (Ioo_subset_Icc_self ht)
  · exact ht₀
  · exact hαc
  · exact hαd
  · exact hαmem
  · exact hβc
  · exact hβd
  · exact hβmem
  · exact hinit

/-- Analysis II source 53(ii): if the Picard--Lindelöf radius/time inequality
holds on the entire requested interval, the solution exists on that interval. -/
theorem source053_picard_lindelof_global_on_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {a b : ℝ} {t₀ : Icc a b}
    {x₀ : E} {R L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ R 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t :=
  source053_picard_lindelof_exists hf

end

end AnalysisII
