import AdvancedProbability.LpMartingaleResults

noncomputable section

open scoped ENNReal NNReal Topology MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory

namespace AdvancedProbability

universe u

/-- A martingale with terminal representation, stopped at an everywhere finite discrete stopping
 time, is the conditional expectation of its terminal variable with respect to the stopping-time
 sigma-algebra. -/
theorem stoppedValue_ae_eq_condExp_terminal_of_finite
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} [SigmaFiniteFiltration μ ℱ]
    {X : ℕ → Ω → ℝ} {Z : Ω → ℝ}
    (hrep : ∀ n, X n =ᵐ[μ] μ[Z | ℱ n])
    {T : Ω → ℕ∞} (hT : IsStoppingTime ℱ T) (hTfinite : ∀ ω, T ω ≠ ⊤) :
    MeasureTheory.stoppedValue X T =ᵐ[μ] μ[Z | hT.measurableSpace] := by
  let hcount : (Set.range T).Countable := Set.to_countable _
  have hUniv : (Set.univ : Set Ω) = ⋃ i ∈ Set.range T, {ω | T ω = i} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_setOf_eq, exists_apply_eq_apply']
  nth_rw 1 [← @Measure.restrict_univ Ω _ μ]
  rw [hUniv, ae_eq_restrict_biUnion_iff _ hcount]
  intro i hi
  have hiTop : i ≠ ⊤ := by
    intro hiEq
    subst i
    obtain ⟨ω, hω⟩ := hi
    exact hTfinite ω hω
  lift i to ℕ using hiTop with n
  calc
    MeasureTheory.stoppedValue X T =ᵐ[μ.restrict {ω | T ω = (n : ℕ∞)}] X n := by
      rw [Filter.EventuallyEq, ae_restrict_iff' (ℱ.le n _ (hT.measurableSet_eq n))]
      exact Filter.Eventually.of_forall fun ω hω ↦ by
        rw [Set.mem_setOf_eq] at hω
        simp [MeasureTheory.stoppedValue, hω]
    _ =ᵐ[μ.restrict {ω | T ω = (n : ℕ∞)}] μ[Z | ℱ n] :=
      ae_restrict_of_ae (hrep n)
    _ =ᵐ[μ.restrict {ω | T ω = (n : ℕ∞)}] μ[Z | hT.measurableSpace] :=
      (condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
        (f := Z) hT hcount n).symm

/-- Source 43: optional stopping for a uniformly integrable discrete martingale at everywhere finite
 stopping times.  The conditional identity follows from the terminal representation and the tower
 property; equality of expectations is its integral consequence. -/
theorem DiscreteUIOptionalStoppingTheorem
    {Ω : Type u} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} [SigmaFiniteFiltration μ ℱ]
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ)
    {S T : Ω → ℕ∞} (hS : IsStoppingTime ℱ S) (hT : IsStoppingTime ℱ T)
    (hST : S ≤ T) (hSfinite : ∀ ω, S ω ≠ ⊤) (hTfinite : ∀ ω, T ω ≠ ⊤) :
    MeasureTheory.stoppedValue X S =ᵐ[μ]
        μ[MeasureTheory.stoppedValue X T | hS.measurableSpace] ∧
      (∫ ω, MeasureTheory.stoppedValue X S ω ∂μ) =
        ∫ ω, MeasureTheory.stoppedValue X T ω ∂μ := by
  obtain ⟨Z, hZ, hrep⟩ := (DiscreteL1MartingaleConvergenceTheorem hX).1.mp hUI
  have hSterminal :=
    stoppedValue_ae_eq_condExp_terminal_of_finite hrep hS hSfinite
  have hTterminal :=
    stoppedValue_ae_eq_condExp_terminal_of_finite hrep hT hTfinite
  have hSTspace : hS.measurableSpace ≤ hT.measurableSpace :=
    hS.measurableSpace_mono hT hST
  have hcond : MeasureTheory.stoppedValue X S =ᵐ[μ]
      μ[MeasureTheory.stoppedValue X T | hS.measurableSpace] := by
    calc
      MeasureTheory.stoppedValue X S =ᵐ[μ] μ[Z | hS.measurableSpace] := hSterminal
      _ =ᵐ[μ] μ[μ[Z | hT.measurableSpace] | hS.measurableSpace] :=
        (condExp_condExp_of_le hSTspace hT.measurableSpace_le).symm
      _ =ᵐ[μ] μ[MeasureTheory.stoppedValue X T | hS.measurableSpace] :=
        condExp_congr_ae hTterminal.symm
  refine ⟨hcond, ?_⟩
  calc
    (∫ ω, MeasureTheory.stoppedValue X S ω ∂μ) =
        ∫ ω, μ[MeasureTheory.stoppedValue X T | hS.measurableSpace] ω ∂μ :=
      integral_congr_ae hcond
    _ = ∫ ω, MeasureTheory.stoppedValue X T ω ∂μ :=
      integral_condExp hS.measurableSpace_le

end AdvancedProbability
