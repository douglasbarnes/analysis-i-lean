import Mathlib

open Bornology Filter Function Set Topology
open scoped Topology

namespace AnalysisII

noncomputable section

/-- Analysis II source 22: Bolzano--Weierstrass in finite-dimensional Euclidean space. -/
theorem source022_bolzano_weierstrass
    {n : ℕ} {u : ℕ → (Fin n → ℝ)}
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ x : Fin n → ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) := by
  have hcompact : IsCompact (closure (Set.range u)) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hu.closure⟩
  obtain ⟨x, _hx, φ, hφ, hlim⟩ := hcompact.isSeqCompact
    (fun k => subset_closure ⟨k, rfl⟩)
  exact ⟨x, φ, hφ, hlim⟩

/-- The sequence-based definition of a limit point used in the notes. -/
def SequenceLimitPoint {X : Type*} [TopologicalSpace X] (E : Set X) (y : X) : Prop :=
  ∃ u : ℕ → X, (∀ n, u n ∈ E ∧ u n ≠ y) ∧ Tendsto u atTop (𝓝 y)

/-- Analysis II source 30: the punctured-ball characterization of a limit point.
The reverse implication is expressed using first countability, which holds in all
metric spaces. -/
theorem source030_limitPoint_iff_punctured_balls
    {X : Type*} [PseudoMetricSpace X] {E : Set X} {y : X} :
    SequenceLimitPoint E y ↔
      ∀ r > 0, ((Metric.ball y r \ {y}) ∩ E).Nonempty := by
  constructor
  · rintro ⟨u, huE, huy⟩ r hr
    have hEventually : ∀ᶠ n in atTop, u n ∈ Metric.ball y r :=
      huy (Metric.ball_mem_nhds y hr)
    obtain ⟨n, hn⟩ := hEventually.exists
    exact ⟨u n, ⟨hn, by simpa using (huE n).2⟩, (huE n).1⟩
  · intro hballs
    have hyclosure : y ∈ closure (E \ {y}) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨z, ⟨hzball, hzne⟩, hzE⟩ := hballs ε hε
      exact ⟨z, ⟨hzE, hzne⟩, hzball⟩
    rw [mem_closure_iff_seq_limit] at hyclosure
    obtain ⟨u, hu, hlim⟩ := hyclosure
    exact ⟨u, fun n => ⟨(hu n).1, by simpa using (hu n).2⟩, hlim⟩

/-- Analysis II source 33: sequential characterization of continuity at a point. -/
theorem source033_continuousAt_iff_sequences
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} :
    ContinuousAt f x ↔
      ∀ u : ℕ → X, Tendsto u atTop (𝓝 x) →
        Tendsto (f ∘ u) atTop (𝓝 (f x)) :=
  tendsto_nhds_iff_seq_tendsto

/-- Analysis II source 37(i): every bounded sequence in a finite-dimensional
real normed space has a convergent subsequence. -/
theorem source037_finiteDimensional_bolzano_weierstrass
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {u : ℕ → E}
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ x : E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) := by
  have hcompact : IsCompact (closure (Set.range u)) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hu.closure⟩
  obtain ⟨x, _hx, φ, hφ, hlim⟩ := hcompact.isSeqCompact
    (fun k => subset_closure ⟨k, rfl⟩)
  exact ⟨x, φ, hφ, hlim⟩

/-- Analysis II source 40: convergence is equivalent to eventual membership in
every neighbourhood of the proposed limit. -/
theorem source040_converges_iff_eventually_neighbourhoods
    {X : Type*} [TopologicalSpace X] {u : ℕ → X} {x : X} :
    Tendsto u atTop (𝓝 x) ↔
      ∀ V : Set X, IsOpen V → x ∈ V → ∀ᶠ n in atTop, u n ∈ V := by
  constructor
  · intro hu V hV hxV
    exact hu (hV.mem_nhds hxV)
  · intro h
    rw [tendsto_def]
    intro S hS
    obtain ⟨V, hVS, hVopen, hxV⟩ := mem_nhds_iff.mp hS
    exact Filter.mem_of_superset (h V hVopen hxV) hVS

/-- Analysis II source 50: the ε/δ, sequential, and neighbourhood formulations
of continuity at a point are equivalent. -/
theorem source050_continuity_characterizations
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    {f : X → Y} {y : X} :
    (ContinuousAt f y ↔
      ∀ u : ℕ → X, Tendsto u atTop (𝓝 y) →
        Tendsto (f ∘ u) atTop (𝓝 (f y))) ∧
    (ContinuousAt f y ↔
      ∀ V : Set Y, IsOpen V → f y ∈ V →
        ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ U ⊆ f ⁻¹' V) := by
  constructor
  · exact tendsto_nhds_iff_seq_tendsto
  · constructor
    · intro hf V hV hfy
      have hpre : f ⁻¹' V ∈ 𝓝 y := hf (hV.mem_nhds hfy)
      obtain ⟨U, hUsub, hUopen, hyU⟩ := mem_nhds_iff.mp hpre
      exact ⟨U, hUopen, hyU, hUsub⟩
    · intro h
      rw [ContinuousAt, tendsto_def]
      intro S hS
      obtain ⟨V, hVS, hVopen, hfyV⟩ := mem_nhds_iff.mp hS
      obtain ⟨U, hUopen, hyU, hUsub⟩ := h V hVopen hfyV
      exact Filter.mem_of_superset (hUopen.mem_nhds hyU)
        (hUsub.trans <| preimage_mono hVS)

end

end AnalysisII
