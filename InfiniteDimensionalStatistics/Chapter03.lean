import InfiniteDimensionalStatistics.Chapter03.EmpiricalProcesses
import InfiniteDimensionalStatistics.Chapter03.Concentration
import InfiniteDimensionalStatistics.Chapter03.Symmetrisation
import InfiniteDimensionalStatistics.Chapter03.MetricEntropy
import InfiniteDimensionalStatistics.Chapter03.VapnikChervonenkis
import InfiniteDimensionalStatistics.Chapter03.WeakConvergence
import InfiniteDimensionalStatistics.Chapter03.ElementaryLemmas
import InfiniteDimensionalStatistics.Chapter03.Hoeffding
import InfiniteDimensionalStatistics.Chapter03.Rademacher

/-!
# Chapter 3: Empirical Processes

Source-order implementation root for Chapter 3.  The current implementation
contains the reusable definition layer, elementary proved consequences, and the
Mathlib-backed Hoeffding and Rademacher bounds.  Deep entropy, VC and Donsker
theorem proofs are added only when they have genuine Lean proofs; no assumption
or placeholder is used to simulate completion.
-/
