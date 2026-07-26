import InfiniteDimensionalStatistics.Chapter03.EmpiricalProcesses
import InfiniteDimensionalStatistics.Chapter03.Concentration
import InfiniteDimensionalStatistics.Chapter03.Symmetrisation
import InfiniteDimensionalStatistics.Chapter03.MetricEntropy
import InfiniteDimensionalStatistics.Chapter03.VapnikChervonenkis
import InfiniteDimensionalStatistics.Chapter03.WeakConvergence
import InfiniteDimensionalStatistics.Chapter03.ElementaryLemmas
import InfiniteDimensionalStatistics.Chapter03.Hoeffding
import InfiniteDimensionalStatistics.Chapter03.Rademacher
import InfiniteDimensionalStatistics.Chapter03.Bennett
import InfiniteDimensionalStatistics.Chapter03.FiniteMaximum
import InfiniteDimensionalStatistics.Chapter03.ProductGeometry
import InfiniteDimensionalStatistics.Chapter03.EntropyMethod
import InfiniteDimensionalStatistics.Chapter03.EmpiricalEntropy
import InfiniteDimensionalStatistics.Chapter03.UStatistics
import InfiniteDimensionalStatistics.Chapter03.EntropyGrowth
import InfiniteDimensionalStatistics.Chapter03.Variation
import InfiniteDimensionalStatistics.Chapter03.OuterMeasure
import InfiniteDimensionalStatistics.Chapter03.LimitClasses
import InfiniteDimensionalStatistics.Chapter03.GaussianBridge
import InfiniteDimensionalStatistics.Chapter03.LocalClasses
import InfiniteDimensionalStatistics.Chapter03.InterfaceLemmas
import InfiniteDimensionalStatistics.Chapter03.SauerShelah
import InfiniteDimensionalStatistics.Chapter03.OuterLaw
import InfiniteDimensionalStatistics.Chapter03.OuterMeasureLemmas
import InfiniteDimensionalStatistics.Chapter03.EmpiricalMeasureLemmas
import InfiniteDimensionalStatistics.Chapter03.EmpiricalAlgebra
import InfiniteDimensionalStatistics.Chapter03.FiniteClassGlivenkoCantelli
import InfiniteDimensionalStatistics.Chapter03.MeasurableWeakConvergence
import InfiniteDimensionalStatistics.Chapter03.Tightness
import InfiniteDimensionalStatistics.Chapter03.VCPermanence
import InfiniteDimensionalStatistics.Chapter03.ConvergenceInDistribution
import InfiniteDimensionalStatistics.Chapter03.AnalyticLemmas
import InfiniteDimensionalStatistics.Chapter03.SubgaussianMaximum
import InfiniteDimensionalStatistics.Chapter03.VCBooleanTrace
import InfiniteDimensionalStatistics.Chapter03.BridgeCovarianceLemmas
import InfiniteDimensionalStatistics.Chapter03.MetricEntropyLemmas
import InfiniteDimensionalStatistics.Chapter03.BracketingLemmas
import InfiniteDimensionalStatistics.Chapter03.GaussianPermanence
import InfiniteDimensionalStatistics.Chapter03.EquicontinuityPermanence
import InfiniteDimensionalStatistics.Chapter03.GlivenkoCantelliPermanence
import InfiniteDimensionalStatistics.Chapter03.OuterLawPermanence
import InfiniteDimensionalStatistics.Chapter03.LocalClassPermanence
import InfiniteDimensionalStatistics.Chapter03.PrelinearityLemmas
import InfiniteDimensionalStatistics.Chapter03.ConvexClosurePermanence
import InfiniteDimensionalStatistics.Chapter03.SampleBoundedPermanence
import InfiniteDimensionalStatistics.Chapter03.PseudoMetricLemmas
import InfiniteDimensionalStatistics.Chapter03.UStatisticLemmas
import InfiniteDimensionalStatistics.Chapter03.EntropyMethodLemmas
import InfiniteDimensionalStatistics.Chapter03.RademacherLemmas
import InfiniteDimensionalStatistics.Chapter03.SymmetryLemmas
import InfiniteDimensionalStatistics.Chapter03.BoundedLipschitzLemmas
import InfiniteDimensionalStatistics.Chapter03.UniformityLemmas
import InfiniteDimensionalStatistics.Chapter03.ProductGeometryLemmas
import InfiniteDimensionalStatistics.Chapter03.EntropyGrowthLemmas
import InfiniteDimensionalStatistics.Chapter03.LorentzLemmas
import InfiniteDimensionalStatistics.Chapter03.VCStructuralLemmas
import InfiniteDimensionalStatistics.Chapter03.VariationLemmas
import InfiniteDimensionalStatistics.Chapter03.PaleyZygmund
import InfiniteDimensionalStatistics.Chapter03.RademacherMoments
import InfiniteDimensionalStatistics.Chapter03.SubgaussianMaximumOptimized
import InfiniteDimensionalStatistics.Chapter03.BennettOptimization
import InfiniteDimensionalStatistics.Chapter03.MourierStrongLaw
import InfiniteDimensionalStatistics.Chapter03.ScalarCentralLimit
import InfiniteDimensionalStatistics.Chapter03.AzumaHoeffding

/-!
# Chapter 3: Empirical Processes

Source-order implementation root for Chapter 3.  The current implementation
contains the reusable definition layer and proved concentration results through
the optimized common sub-Gaussian finite maximal bound, Azuma–Hoeffding
martingale tails and finite Sauer–Shelah bound, together with empirical-measure
identities and algebra, elementary outer-measure and analytic calculus, finite
covering/packing and bracketing bounds, a proved finite-class
Glivenko–Cantelli theorem, measurable Portmanteau and Prokhorov results, exact
VC complement permanence, Boolean trace-cardinality bounds, measurable
continuous-mapping and Slutsky theorems, Brownian-bridge covariance/variance
identities, and restriction permanence for Gaussian bridge, motion,
pre-Gaussian realisations, sample boundedness, asymptotic equicontinuity and
strong/weak Glivenko–Cantelli classes.  Continuous maps also preserve outer
convergence in law, asymptotic measurability and compact containment;
finite-dimensional outer convergence is stable under reindexing;
population/empirical local difference classes are monotone; prelinear maps and
`H(𝓕,P)` have their basic algebra; the empirical/population pseudometrics have
nonnegativity and symmetry; the order-two U-statistic has its elementary
finite-sum and canonical-kernel algebra; coordinate-insensitivity, self-bounding
and bounded-difference predicates have elementary closure properties; the
Rademacher, independent-copy and symmetric-law interfaces have their basic law
algebra; the bounded-Lipschitz discrepancy satisfies pseudometric algebra;
uniform Donsker/pre-Gaussian predicates have domination and reindexing rules;
weighted/convex product distances have their exact order theory; regular,
uniform, polynomial and lower entropy-growth predicates have positivity and
monotonicity lemmas; the Lorentz `L₂,₁` functional has invariance and domination
rules; VC traces, subgraphs, thresholds, indicators and envelopes have their
structural monotonicity theory; bounded `p`-variation is invariant under output
translation and negation; Paley–Zygmund has both square-root and divided forms;
weighted Rademacher sums have exact first, variance and second-moment identities;
the Bennett Chernoff optimizer is reduced exactly to the `h(ct/v)` exponent,
conditional on the Bennett mgf estimate; Corollary 3.7.21 is supplied by the
Mathlib-backed Mourier Banach-valued strong law; and the scalar, fixed-coordinate
and finite Cramér–Wold projection central limit theorems are available through
Mathlib's CLT.  Full multivariate finite-dimensional convergence and the
bounded-differences-to-Doob-increment bridge remain separate layers.  The
Donsker interfaces used through Section 3.7 are also present.  Deep entropy, VC
and Donsker theorem proofs are added only when they have genuine Lean proofs;
no assumption or placeholder is used to simulate completion.
-/
