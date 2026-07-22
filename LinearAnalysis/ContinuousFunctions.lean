import LinearAnalysis.Baire

/-!
# Linear Analysis: topology of continuous-function spaces

Normality, Urysohn separation, Tietze extension, equicontinuity, total boundedness,
Arzelà--Ascoli, and Stone--Weierstrass.
-/

noncomputable section

open Set Function Topology Filter
open scoped Topology

namespace Cambridge.LinearAnalysis

abbrev ContinuousFunctions (K : Type*) [TopologicalSpace K] := C(K, ℝ)

/-- The course's pointwise definition of equicontinuity for a family of functions. -/
def EquicontinuousFamily {K Y : Type*} [TopologicalSpace K] [UniformSpace Y]
    {ι : Type*} (F : ι → K → Y) : Prop :=
  Equicontinuous F

/-- An `ε`-net, stated in the metric form used in the notes. -/
def IsEpsilonNet {X : Type*} [PseudoMetricSpace X] (ε : ℝ) (N E : Set X) : Prop :=
  E ⊆ ⋃ x ∈ N, Metric.ball x ε

/-- Total boundedness in the sense used by Arzelà--Ascoli. -/
abbrev IsTotallyBounded {X : Type*} [PseudoMetricSpace X] (E : Set X) : Prop :=
  TotallyBounded E

/-- Compact Hausdorff spaces are normal. -/
theorem compactHausdorff_normal (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] : NormalSpace X := inferInstance

/-- Urysohn's lemma in the exact zero--one form of the course. -/
theorem urysohn {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Set.Icc 0 1 :=
  exists_continuous_zero_one_of_isClosed hs ht hd

/-- Tietze extension for a real-valued continuous function on a closed subspace. -/
theorem tietze_extension {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) (f : C(s, ℝ)) :
    ∃ g : C(X, ℝ), ContinuousMap.restrict s g = f :=
  ContinuousMap.exists_restrict_eq hs f

/-- A totally bounded subset of a complete metric space has compact closure. -/
theorem compact_closure_of_totallyBounded {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {E : Set X} (hE : TotallyBounded E) :
    IsCompact (closure E) :=
  hE.closure.isCompact_of_isClosed isClosed_closure

/-- Conversely, compact closure implies total boundedness. -/
theorem totallyBounded_of_compact_closure {X : Type*} [PseudoMetricSpace X]
    {E : Set X} (hE : IsCompact (closure E)) : TotallyBounded E :=
  hE.totallyBounded.subset subset_closure

/-- Stone--Weierstrass for real-valued continuous functions on a compact space. -/
theorem stoneWeierstrass {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

/-- Epsilon form of Stone--Weierstrass. -/
theorem stoneWeierstrass_approximation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : A, ‖(g : C(X, ℝ)) - f‖ < ε :=
  ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hA f ε hε

/-- Classical Weierstrass approximation on a compact real interval, as supplied by Mathlib's
polynomial approximation theorem. -/
theorem weierstrass_on_Icc (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure :=
  continuousMap_mem_polynomialFunctions_closure a b f

end Cambridge.LinearAnalysis
