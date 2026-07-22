import Mathlib

open Filter Function Set Topology
open scoped Topology BigOperators

namespace AnalysisII

noncomputable section

/-! ## Comparing two norms through their defining inequalities -/

/-- The inequality data used in the lecture definition of Lipschitz-equivalent norms. -/
structure EquivalentGauges {V : Type*} (p q : V → ℝ) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_le : ∀ x, lower * p x ≤ q x
  le_upper : ∀ x, q x ≤ upper * p x

/-- Boundedness measured using a nonnegative gauge. -/
def GaugeBounded {V : Type*} (p : V → ℝ) (s : Set V) : Prop :=
  ∃ R : ℝ, ∀ x ∈ s, p x < R

/-- Sequence convergence measured using a gauge. -/
def GaugeConverges {V : Type*} [Sub V] (p : V → ℝ) (u : ℕ → V) (x : V) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, p (u n - x) < ε

/-- Cauchyness measured using a gauge. -/
def GaugeCauchy {V : Type*} [Sub V] (p : V → ℝ) (u : ℕ → V) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, p (u m - u n) < ε

/-- Completeness measured using a gauge. -/
def GaugeComplete {V : Type*} [Sub V] (p : V → ℝ) : Prop :=
  ∀ u : ℕ → V, GaugeCauchy p u → ∃ x, GaugeConverges p u x

/-- Analysis II source 19(i): Lipschitz-equivalent norms define the same bounded sets. -/
theorem source019_equivalent_norms_bounded
    {V : Type*} {p q : V → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (h : EquivalentGauges p q) (s : Set V) :
    GaugeBounded p s ↔ GaugeBounded q s := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨h.upper * R, fun x hx => lt_of_le_of_lt (h.le_upper x) ?_⟩
    exact mul_lt_mul_of_pos_left (hR x hx) h.upper_pos
  · rintro ⟨R, hR⟩
    refine ⟨R / h.lower, fun x hx => ?_⟩
    apply (lt_div_iff₀ h.lower_pos).2
    exact lt_of_le_of_lt (h.lower_le x) (hR x hx)

/-- Analysis II source 19(ii): Lipschitz-equivalent norms define the same convergence. -/
theorem source019_equivalent_norms_convergence
    {V : Type*} [Sub V] {p q : V → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (h : EquivalentGauges p q) (u : ℕ → V) (x : V) :
    GaugeConverges p u x ↔ GaugeConverges q u x := by
  constructor
  · intro hu ε hε
    obtain ⟨N, hN⟩ := hu (ε / h.upper) (div_pos hε h.upper_pos)
    refine ⟨N, fun n hn => ?_⟩
    calc
      q (u n - x) ≤ h.upper * p (u n - x) := h.le_upper _
      _ < h.upper * (ε / h.upper) :=
        mul_lt_mul_of_pos_left (hN n hn) h.upper_pos
      _ = ε := by field_simp [ne_of_gt h.upper_pos]
  · intro hu ε hε
    obtain ⟨N, hN⟩ := hu (h.lower * ε) (mul_pos h.lower_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hlo := h.lower_le (u n - x)
    have hq' := hN n hn
    have hp' := hp (u n - x)
    nlinarith [h.lower_pos]

/-- Analysis II source 20(i): limits in a normed space are unique. -/
theorem source020_limit_unique
    {V : Type*} [NormedAddCommGroup V] {u : ℕ → V} {x y : V}
    (hx : Tendsto u atTop (𝓝 x)) (hy : Tendsto u atTop (𝓝 y)) : x = y :=
  tendsto_nhds_unique hx hy

/-- Analysis II source 20(ii): scalar multiplication commutes with limits. -/
theorem source020_const_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : ℕ → V} {x : V} (a : ℝ) (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => a • u n) atTop (𝓝 (a • x)) :=
  tendsto_const_nhds.smul hu

/-- Analysis II source 20(iii): addition commutes with limits. -/
theorem source020_add
    {V : Type*} [NormedAddCommGroup V]
    {u v : ℕ → V} {x y : V} (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => u n + v n) atTop (𝓝 (x + y)) :=
  hu.add hv

/-- Analysis II source 21: convergence in finite-dimensional Euclidean space is
coordinatewise convergence. -/
theorem source021_euclidean_coordinatewise
    {n : ℕ} {u : ℕ → (Fin n → ℝ)} {x : Fin n → ℝ} :
    Tendsto u atTop (𝓝 x) ↔
      ∀ i, Tendsto (fun k => u k i) atTop (𝓝 (x i)) :=
  tendsto_pi_nhds

/-- Analysis II source 23: every convergent sequence is Cauchy. -/
theorem source023_convergent_is_cauchy
    {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} {x : X}
    (hu : Tendsto u atTop (𝓝 x)) : CauchySeq u :=
  hu.cauchy_map

/-- Analysis II source 24: every Cauchy sequence in a normed space is norm-bounded. -/
theorem source024_cauchy_bounded
    {V : Type*} [NormedAddCommGroup V] {u : ℕ → V} (hu : CauchySeq u) :
    ∃ R : ℝ, ∀ n, ‖u n‖ < R := by
  obtain ⟨R, hR, hdist⟩ := cauchySeq_bdd hu
  refine ⟨R + ‖u 0‖, fun n => ?_⟩
  have hd : ‖u n - u 0‖ < R := by
    simpa [dist_eq_norm] using hdist n 0
  calc
    ‖u n‖ = ‖(u n - u 0) + u 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖u n - u 0‖ + ‖u 0‖ := norm_add_le _ _
    _ < R + ‖u 0‖ := by linarith

/-- Analysis II source 25: a Cauchy sequence with a convergent subsequence converges. -/
theorem source025_cauchy_subsequence_limit
    {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} {x : X}
    (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsub : Tendsto (u ∘ φ) atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) :=
  tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hsub

/-- Analysis II source 26(i): equivalent norms define the same Cauchy sequences. -/
theorem source026_equivalent_norms_cauchy
    {V : Type*} [Sub V] {p q : V → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (h : EquivalentGauges p q) (u : ℕ → V) :
    GaugeCauchy p u ↔ GaugeCauchy q u := by
  constructor
  · intro hu ε hε
    obtain ⟨N, hN⟩ := hu (ε / h.upper) (div_pos hε h.upper_pos)
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      q (u m - u n) ≤ h.upper * p (u m - u n) := h.le_upper _
      _ < h.upper * (ε / h.upper) :=
        mul_lt_mul_of_pos_left (hN m hm n hn) h.upper_pos
      _ = ε := by field_simp [ne_of_gt h.upper_pos]
  · intro hu ε hε
    obtain ⟨N, hN⟩ := hu (h.lower * ε) (mul_pos h.lower_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hlo := h.lower_le (u m - u n)
    have hq' := hN m hm n hn
    have hp' := hp (u m - u n)
    nlinarith [h.lower_pos]

/-- Analysis II source 26(ii): equivalent norms define the same completeness. -/
theorem source026_equivalent_norms_complete
    {V : Type*} [Sub V] {p q : V → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (h : EquivalentGauges p q) : GaugeComplete p ↔ GaugeComplete q := by
  constructor
  · intro hpComplete u hu
    have hup : GaugeCauchy p u :=
      (source026_equivalent_norms_cauchy hp hq h u).mpr hu
    obtain ⟨x, hx⟩ := hpComplete u hup
    exact ⟨x, (source019_equivalent_norms_convergence hp hq h u x).mp hx⟩
  · intro hqComplete u hu
    have huq : GaugeCauchy q u :=
      (source026_equivalent_norms_cauchy hp hq h u).mp hu
    obtain ⟨x, hx⟩ := hqComplete u huq
    exact ⟨x, (source019_equivalent_norms_convergence hp hq h u x).mpr hx⟩

/-- Analysis II source 27: Euclidean space is complete. -/
theorem source027_euclidean_complete (n : ℕ) : CompleteSpace (Fin n → ℝ) := by
  infer_instance

/-- Analysis II source 29 (and duplicate source 31): closedness is equivalent to
openness of the complement. -/
theorem source029_closed_iff_complement_open
    {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsClosed s ↔ IsOpen sᶜ :=
  isOpen_compl_iff.symm

/-- Analysis II source 31 duplicates source 29. -/
theorem source031_closed_iff_complement_open
    {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsClosed s ↔ IsOpen sᶜ :=
  source029_closed_iff_complement_open s

/-- Missing clauses of Analysis II source 41: finite intersections and the trivial open sets. -/
theorem source041_finset_iInter_open
    {X ι : Type*} [TopologicalSpace X] (t : Finset ι) (s : ι → Set X)
    (hs : ∀ i ∈ t, IsOpen (s i)) : IsOpen (⋂ i ∈ t, s i) := by
  classical
  exact isOpen_biInter_finset hs

theorem source041_empty_open {X : Type*} [TopologicalSpace X] : IsOpen (∅ : Set X) :=
  isOpen_empty

theorem source041_univ_open {X : Type*} [TopologicalSpace X] : IsOpen (Set.univ : Set X) :=
  isOpen_univ

/-- Missing clauses of Analysis II source 43: finite unions and the trivial closed sets. -/
theorem source043_finset_iUnion_closed
    {X ι : Type*} [TopologicalSpace X] (t : Finset ι) (s : ι → Set X)
    (hs : ∀ i ∈ t, IsClosed (s i)) : IsClosed (⋃ i ∈ t, s i) := by
  classical
  exact isClosed_biUnion_finset hs

theorem source043_empty_closed {X : Type*} [TopologicalSpace X] : IsClosed (∅ : Set X) :=
  isClosed_empty

theorem source043_univ_closed {X : Type*} [TopologicalSpace X] : IsClosed (Set.univ : Set X) :=
  isClosed_univ

end

end AnalysisII
