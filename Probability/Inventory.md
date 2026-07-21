# Part IA Probability — source inventory

Authoritative source: `IA_L/probability.tex` (2015 R. Weber notes). Examples are intentionally excluded. Count: **115** = 53 definitions + 42 theorems + 16 propositions + 4 corollaries.

| # | TeX line | Kind | Source title | Lean target |
|---:|---:|---|---|---|
| 1 | 61 | `defi` | Classical probability | `IAProbability.ClassicalProbability` |
| 2 | 77 | `defi` | Sample space | `IAProbability.SampleSpace` |
| 3 | 81 | `defi` | Event | `IAProbability.Event` |
| 4 | 90 | `defi` | Set notations | `IAProbability.eventOperations` |
| 5 | 101 | `defi` | Probability | `IAProbability.classicalProb` |
| 6 | 133 | `thm` | Fundamental rule of counting | `IAProbability.fundamentalRuleOfCounting` |
| 7 | 144 | `defi` | Sampling with replacement | `IAProbability.SamplingWithReplacement` |
| 8 | 148 | `defi` | Sampling without replacement | `IAProbability.SamplingWithoutReplacement` |
| 9 | 214 | `defi` | Multinomial coefficient | `IAProbability.multinomial` |
| 10 | 248 | `prop` | (untitled) | `IAProbability.logFactorial_le` |
| 11 | 288 | `thm` | Stirling's formula | `IAProbability.stirlingFormula` |
| 12 | 294 | `cor` | (untitled) | `IAProbability.factorialAsymptotic` |
| 13 | 365 | `prop` | non-examinable | `IAProbability.robbinsStirlingBound` |
| 14 | 391 | `defi` | Probability space | `IAProbability.ProbabilitySpace` |
| 15 | 416 | `defi` | Probability distribution | `IAProbability.ProbabilityDistribution` |
| 16 | 425 | `thm` | (untitled) | `IAProbability.elementaryProbabilityIdentities` |
| 17 | 446 | `defi` | Limit of events | `IAProbability.eventLimit` |
| 18 | 457 | `thm` | (untitled) | `IAProbability.probability_continuous_iUnion` |
| 19 | 486 | `thm` | Boole's inequality | `IAProbability.booleInequality` |
| 20 | 540 | `thm` | Inclusion-exclusion formula | `IAProbability.inclusionExclusionTwo` |
| 21 | 582 | `thm` | Bonferroni's inequalities | `IAProbability.bonferroniFirst` |
| 22 | 619 | `defi` | Independent events | `IAProbability.IndependentEvents` |
| 23 | 628 | `prop` | (untitled) | `IAProbability.independent_compl_right` |
| 24 | 663 | `defi` | Independence of multiple events | `IAProbability.MutuallyIndependentEvents` |
| 25 | 698 | `defi` | Bernoulli distribution | `IAProbability.bernoulliMass` |
| 26 | 705 | `defi` | Binomial distribution | `IAProbability.binomialMass` |
| 27 | 721 | `defi` | Geometric distribution | `IAProbability.geometricMass` |
| 28 | 729 | `defi` | Hypergeometric distribution | `IAProbability.hypergeometricMass` |
| 29 | 736 | `defi` | Poisson distribution | `IAProbability.poissonMass` |
| 30 | 745 | `thm` | Poisson approximation to binomial | `IAProbability.poissonApproximation` |
| 31 | 761 | `defi` | Conditional probability | `IAProbability.conditionalProbability` |
| 32 | 789 | `thm` | (untitled) | `IAProbability.conditional_mul` |
| 33 | 813 | `defi` | Partition | `IAProbability.Partition` |
| 34 | 819 | `prop` | (untitled) | `IAProbability.totalProbability` |
| 35 | 842 | `thm` | Bayes' formula | `IAProbability.bayesFormula` |
| 36 | 891 | `defi` | Random variable | `IAProbability.RandomVariable` |
| 37 | 896 | `defi` | Discrete random variables | `IAProbability.DiscreteRandomVariable` |
| 38 | 918 | `defi` | Discrete uniform distribution | `IAProbability.discreteUniformMass` |
| 39 | 942 | `defi` | Expectation | `IAProbability.expectation` |
| 40 | 1009 | `thm` | (untitled) | `IAProbability.expectation_affine` |
| 41 | 1042 | `thm` | (untitled) | `IAProbability.expectation_finset_sum` |
| 42 | 1055 | `defi` | Variance and standard deviation | `IAProbability.variance` |
| 43 | 1064 | `thm` | (untitled) | `IAProbability.variance_nonnegative` |
| 44 | 1114 | `defi` | Indicator function | `IAProbability.indicator` |
| 45 | 1127 | `prop` | (untitled) | `IAProbability.indicatorIdentities` |
| 46 | 1161 | `thm` | Inclusion-exclusion formula | `IAProbability.indicatorInclusionExclusion` |
| 47 | 1189 | `defi` | Independent random variables | `IAProbability.IndependentRandomVariables` |
| 48 | 1196 | `thm` | (untitled) | `IAProbability.independent_comp` |
| 49 | 1211 | `thm` | (untitled) | `IAProbability.expectation_mul_of_independent` |
| 50 | 1227 | `cor` | (untitled) | `IAProbability.expectation_transformed_product` |
| 51 | 1234 | `thm` | (untitled) | `IAProbability.variance_add_of_independent` |
| 52 | 1250 | `cor` | (untitled) | `IAProbability.variance_sampleMean` |
| 53 | 1295 | `defi` | Convex function | `IAProbability.ConvexOnInterval` |
| 54 | 1316 | `prop` | (untitled) | `IAProbability.convex_of_secondDerivative_nonnegative` |
| 55 | 1320 | `thm` | Jensen's inequality | `IAProbability.jensenFinite` |
| 56 | 1345 | `cor` | AM-GM inequality | `IAProbability.arithmeticGeometricMean` |
| 57 | 1366 | `thm` | Cauchy-Schwarz inequality | `IAProbability.cauchySchwarzFinite` |
| 58 | 1387 | `thm` | Markov inequality | `IAProbability.markovInequality` |
| 59 | 1408 | `thm` | Chebyshev inequality | `IAProbability.chebyshevInequality` |
| 60 | 1430 | `thm` | Weak law of large numbers | `IAProbability.weakLawOfLargeNumbers` |
| 61 | 1473 | `thm` | Strong law of large numbers | `IAProbability.strongLawOfLargeNumbers` |
| 62 | 1489 | `defi` | Covariance | `IAProbability.covariance` |
| 63 | 1496 | `prop` | (untitled) | `IAProbability.covariance_comm` |
| 64 | 1522 | `defi` | Correlation coefficient | `IAProbability.correlation` |
| 65 | 1529 | `prop` | (untitled) | `IAProbability.abs_correlation_le_one` |
| 66 | 1541 | `defi` | Conditional distribution | `IAProbability.conditionalMass` |
| 67 | 1574 | `thm` | (untitled) | `IAProbability.conditional_eq_of_factorization` |
| 68 | 1590 | `thm` | Tower property of conditional expectation | `IAProbability.towerProperty` |
| 69 | 1614 | `defi` | Probability generating function (pgf) | `IAProbability.pgf` |
| 70 | 1634 | `thm` | (untitled) | `IAProbability.pgf_unique` |
| 71 | 1646 | `thm` | Abel's lemma | `IAProbability.abelMeanFormula` |
| 72 | 1674 | `thm` | (untitled) | `IAProbability.secondFactorialMomentFormula` |
| 73 | 1708 | `thm` | (untitled) | `IAProbability.pgf_sum_product` |
| 74 | 1878 | `thm` | (untitled) | `IAProbability.branchingPgf_succ` |
| 75 | 1897 | `thm` | (untitled) | `IAProbability.branchingMeanVariance_recursion` |
| 76 | 1977 | `thm` | (untitled) | `IAProbability.extinction_smallest_fixed_point` |
| 77 | 2003 | `defi` | Random walk | `IAProbability.randomWalk` |
| 78 | 2170 | `defi` | Continuous random variable | `IAProbability.IsDensity` |
| 79 | 2187 | `defi` | Cumulative distribution function | `IAProbability.cdf` |
| 80 | 2235 | `defi` | Uniform distribution | `IAProbability.uniformDensity` |
| 81 | 2248 | `defi` | Exponential random variable | `IAProbability.exponentialDensity` |
| 82 | 2266 | `prop` | (untitled) | `IAProbability.exponential_memoryless` |
| 83 | 2304 | `defi` | Expectation | `IAProbability.continuousExpectation` |
| 84 | 2312 | `thm` | (untitled) | `IAProbability.expectation_eq_tailIntegral` |
| 85 | 2345 | `defi` | Variance | `IAProbability.continuousVariance` |
| 86 | 2368 | `defi` | Mode and median | `IAProbability.ModeMedian` |
| 87 | 2388 | `defi` | Sample mean | `IAProbability.sampleMean` |
| 88 | 2399 | `defi` | Stochastic order | `IAProbability.StochasticallyDominates` |
| 89 | 2432 | `defi` | Joint distribution | `IAProbability.jointCdf` |
| 90 | 2443 | `defi` | Jointly distributed random variables | `IAProbability.IsJointDensity` |
| 91 | 2469 | `thm` | (untitled) | `IAProbability.coordinate_measurable` |
| 92 | 2489 | `defi` | Independent continuous random variables | `IAProbability.IndependentContinuous` |
| 93 | 2514 | `prop` | (untitled) | `IAProbability.continuous_independent_product` |
| 94 | 2627 | `defi` | Normal distribution | `IAProbability.normalDensity` |
| 95 | 2649 | `prop` | (untitled) | `IAProbability.normalDensity_integral` |
| 96 | 2668 | `prop` | (untitled) | `IAProbability.normal_mean` |
| 97 | 2680 | `prop` | (untitled) | `IAProbability.normal_variance` |
| 98 | 2720 | `thm` | (untitled) | `IAProbability.density_transform_monotone` |
| 99 | 2751 | `thm` | (untitled) | `IAProbability.inverseCdfSimulation` |
| 100 | 2793 | `defi` | Jacobian determinant | `IAProbability.jacobianDeterminant` |
| 101 | 2812 | `prop` | (untitled) | `IAProbability.jointDensityChangeVariables` |
| 102 | 2945 | `defi` | Order statistics | `IAProbability.IsOrderStatistic` |
| 103 | 3026 | `defi` | Moment generating function | `IAProbability.mgf` |
| 104 | 3039 | `thm` | (untitled) | `IAProbability.mgfDeterminesDistribution` |
| 105 | 3043 | `defi` | Moment | `IAProbability.moment` |
| 106 | 3047 | `thm` | (untitled) | `IAProbability.mgfDerivativeMoment` |
| 107 | 3084 | `thm` | (untitled) | `IAProbability.mgf_add_of_independent` |
| 108 | 3096 | `defi` | Cauchy distribution | `IAProbability.cauchyDensity` |
| 109 | 3109 | `prop` | (untitled) | `IAProbability.cauchy_not_integrable` |
| 110 | 3160 | `defi` | Gamma distribution | `IAProbability.gammaDensity` |
| 111 | 3185 | `defi` | Beta distribution | `IAProbability.betaDensity` |
| 112 | 3201 | `prop` | (untitled) | `IAProbability.normalMgf` |
| 113 | 3220 | `thm` | (untitled) | `IAProbability.independentNormalAffine` |
| 114 | 3366 | `thm` | Central limit theorem | `IAProbability.centralLimitTheorem` |
| 115 | 3382 | `thm` | Continuity theorem | `IAProbability.continuityTheorem` |
