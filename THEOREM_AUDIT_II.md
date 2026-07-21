# Analysis II theorem audit

Complete declaration-level audit of the **68** theorem-like environments in the supplied Analysis II notes. Detailed statement corrections are in `SOURCE_CORRECTIONS_II.md`.

| ID | Lines | Status | Mathlib target |
|---:|---:|---|---|
| 1 | 200–202 | mathlib | `Mathlib.Topology.UniformSpace.UniformConvergence` — `TendstoUniformlyOn.uniformCauchySeqOn; UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` |
| 2 | 225–229 | mathlib | `Mathlib.Topology.UniformSpace.UniformConvergence` — `TendstoUniformlyOn.continuousOn / TendstoUniformly.continuous` |
| 3 | 247–252 | reformulated | `Mathlib.Analysis.BoxIntegral.Integrability` — `BoxIntegral uniform-limit/integral continuity API` |
| 4 | 298–305 | mathlib | `Mathlib.Analysis.Calculus.UniformLimitsDeriv` — `hasDerivAt_of_tendstoUniformlyOn; hasFDerivAt_of_tendstoUniformlyOn` |
| 5 | 389–394 | mathlib | `Mathlib.Topology.Algebra.Module` — `TendstoUniformly.add; TendstoUniformly.const_smul; UniformContinuous.comp_tendstoUniformly` |
| 6 | 428–430 | mathlib | `Mathlib.Analysis.Normed.Group.FunctionSeries` — `Summable.of_norm / summable_of_norm_bounded` |
| 7 | 465–471 | mathlib | `Mathlib.Analysis.Normed.Group.FunctionSeries` — `summable_of_norm_bounded` |
| 8 | 489–499 | reformulated | `Mathlib.Analysis.Analytic.ConvergenceRadius` — `FormalMultilinearSeries.radius; HasFPowerSeriesOnBall` |
| 9 | 519–529 | reformulated | `Mathlib.Analysis.Analytic.Constructions` — `HasFPowerSeriesOnBall.deriv / FormalMultilinearSeries.deriv` |
| 10 | 574–576 | duplicate | `Mathlib.Topology.UniformSpace.Compact` — `IsCompact.uniformContinuousOn_of_continuous` |
| 11 | 679–684 | reformulated | `Mathlib.Analysis.BoxIntegral.Integrability` — `BoxIntegral integrability criterion` |
| 12 | 687–689 | reformulated | `Mathlib.Analysis.BoxIntegral.Integrability` — `Riemann-integrable continuous composition theorem family` |
| 13 | 742–744 | duplicate | `Mathlib.Analysis.BoxIntegral.Integrability` — `continuous implies Riemann integrable` |
| 14 | 746–748 | reformulated | `Mathlib.Analysis.BoxIntegral.Integrability` — `Riemann integrability under uniform limits` |
| 15 | 782–791 | reformulated | `Mathlib.MeasureTheory.Integral.Bochner.Basic` — `norm_integral_le_integral_norm` |
| 16 | 817–823 | mathlib | `Mathlib.Analysis.Normed.Algebra.StoneWeierstrass` — `Stone–Weierstrass / polynomial approximation theorem family` |
| 17 | 923–925 | reformulated | `Mathlib.MeasureTheory.Integral.Bochner.Basic` — `Lebesgue criterion for Riemann integrability` |
| 18 | 1047–1052 | mathlib | `Mathlib.MeasureTheory.Integral.Bochner.L1` — `integral_mul_le_Lp_mul_Lq / inner-integral Cauchy–Schwarz` |
| 19 | 1173–1179 | reformulated | `Mathlib.Topology.Algebra.Module.FiniteDimension` — `equivalent normed structures induce the same bounded sets and convergence` |
| 20 | 1194–1201 | mathlib | `Mathlib.Topology.Algebra.Module` — `tendsto_nhds_unique; Filter.Tendsto.const_smul; Filter.Tendsto.add` |
| 21 | 1211–1213 | mathlib | `Mathlib.Topology.Instances.Pi` — `tendsto_pi_nhds` |
| 22 | 1232–1234 | mathlib | `Mathlib.Analysis.Normed.Module.FiniteDimension` — `FiniteDimensional.proper / bounded sequence subsequence theorem` |
| 23 | 1287–1289 | mathlib | `Mathlib.Topology.UniformSpace.Cauchy` — `Filter.Tendsto.cauchySeq` |
| 24 | 1298–1300 | mathlib | `Mathlib.Topology.MetricSpace.Bounded` — `CauchySeq.isBounded_range` |
| 25 | 1309–1311 | mathlib | `Mathlib.Topology.MetricSpace.Cauchy` — `CauchySeq.tendsto_of_subseq_tendsto` |
| 26 | 1320–1322 | mathlib | `Mathlib.Topology.UniformSpace.Basic` — `Cauchy and complete invariance under uniform equivalence` |
| 27 | 1328–1330 | mathlib | `Mathlib.Topology.Instances.Pi` — `Pi.instCompleteSpace` |
| 28 | 1365–1367 | mathlib | `Mathlib.Topology.MetricSpace.Basic` — `Metric.isOpen_ball` |
| 29 | 1395–1397 | mathlib | `Mathlib.Topology.MetricSpace.Closeds` — `isClosed_iff_clusterPt` |
| 30 | 1407–1413 | mathlib | `Mathlib.Topology.MetricSpace.Closeds` — `mem_clusterPt_iff` |
| 31 | 1422–1424 | duplicate | `Mathlib.Topology.MetricSpace.Closeds` — `isClosed_iff_clusterPt` |
| 32 | 1440–1446 | mathlib | `Mathlib.Topology.MetricSpace.ProperSpace` — `IsCompact.isClosed; IsCompact.isBounded; Metric.isCompact_iff_isClosed_bounded` |
| 33 | 1474–1476 | mathlib | `Mathlib.Topology.Sequences` — `continuousAt_iff_seqContinuousAt` |
| 34 | 1500–1510 | mathlib | `Mathlib.Topology.Basic` — `IsCompact.image; IsCompact.isClosed; IsCompact.isBounded; IsCompact.exists_isMaxOn` |
| 35 | 1521–1527 | reformulated | `Mathlib.Analysis.Normed.Module.FiniteDimension` — `Basis.equivFun and compact unit sphere` |
| 36 | 1542–1544 | reformulated | `Mathlib.Topology.Algebra.Module.FiniteDimension` — `FiniteDimensional continuous/uniform equivalence of norms` |
| 37 | 1583–1589 | mathlib | `Mathlib.Analysis.Normed.Module.FiniteDimension` — `FiniteDimensional.proper; Metric.isCompact_iff_isClosed_bounded` |
| 38 | 1597–1599 | mathlib | `Mathlib.Analysis.Normed.Module.FiniteDimension` — `FiniteDimensional.complete` |
| 39 | 1722–1724 | mathlib | `Mathlib.Topology.Separation.Hausdorff` — `tendsto_nhds_unique` |
| 40 | 1770–1772 | mathlib | `Mathlib.Topology.Defs.Filter` — `tendsto_nhds_iff_eventually` |
| 41 | 1780–1787 | mathlib | `Mathlib.Topology.Basic` — `isOpen_iUnion; IsOpen.inter; isOpen_empty; isOpen_univ` |
| 42 | 1807–1809 | mathlib | `Mathlib.Topology.Basic` — `isClosed_compl_iff` |
| 43 | 1816–1823 | mathlib | `Mathlib.Topology.Basic` — `isClosed_iInter; IsClosed.union; isClosed_empty; isClosed_univ` |
| 44 | 1829–1831 | mathlib | `Mathlib.Topology.Separation.Hausdorff` — `isClosed_singleton; Set.Finite.isClosed` |
| 45 | 1848–1854 | mathlib | `Mathlib.Topology.MetricSpace.Cauchy` — `Filter.Tendsto.cauchySeq; CauchySeq.tendsto_of_subseq_tendsto` |
| 46 | 1925–1931 | mathlib | `Mathlib.Topology.UniformSpace.Closeds` — `IsComplete.isClosed; IsClosed.isComplete` |
| 47 | 1951–1953 | mathlib | `Mathlib.Topology.MetricSpace.Bounded` — `IsCompact.isComplete; IsCompact.isBounded` |
| 48 | 1978–1980 | mathlib | `Mathlib.Topology.MetricSpace.Bounded` — `compact_iff_complete_totallyBounded theorem family` |
| 49 | 2070–2072 | mathlib | `Mathlib.Topology.UniformSpace.Compact` — `IsCompact.uniformContinuousOn_of_continuous` |
| 50 | 2082–2089 | mathlib | `Mathlib.Topology.Sequences` — `continuousAt_iff_seqContinuousAt; continuousAt_def` |
| 51 | 2112–2114 | mathlib | `Mathlib.Topology.Basic` — `continuous_iff_isOpen` |
| 52 | 2131–2135 | mathlib | `Mathlib.Topology.MetricSpace.Contracting` — `ContractingWith.exists_fixedPoint; fixedPoint_unique; isFixedPt_fixedPoint_iterate` |
| 53 | 2220–2238 | reformulated | `Mathlib.Analysis.ODE.PicardLindelof` — `Picard–Lindelöf existence and uniqueness API` |
| 54 | 2450–2452 | mathlib | `Mathlib.Analysis.Calculus.FDeriv.Basic` — `HasFDerivAt.unique` |
| 55 | 2560–2591 | mathlib | `Mathlib.Analysis.Calculus.FDeriv.Basic` — `HasFDerivAt.continuousAt; componentwise derivative; add/smul; ContinuousLinearMap.hasFDerivAt` |
| 56 | 2724–2731 | reformulated | `Mathlib.Analysis.Calculus.ContDiff.Defs` — `continuous partial derivatives imply Fréchet differentiability / ContDiff` |
| 57 | 2805–2819 | mathlib | `Mathlib.Analysis.Normed.Operator.Basic` — `ContinuousLinearMap.le_opNorm; opNorm_comp_le` |
| 58 | 2844–2849 | reformulated | `Mathlib.Analysis.InnerProductSpace.Dual` — `InnerProductSpace.toDual / Riesz representation` |
| 59 | 2865–2870 | mathlib | `Mathlib.Analysis.Calculus.FDeriv.Comp` — `HasFDerivAt.comp` |
| 60 | 2906–2911 | mathlib | `Mathlib.Analysis.Calculus.MeanValue` — `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` |
| 61 | 2942–2948 | mathlib | `Mathlib.Analysis.Calculus.MeanValue` — `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` |
| 62 | 2977–2979 | mathlib | `Mathlib.Analysis.Calculus.MeanValue` — `Convex.isConstantOn_of_fderivWithin_eq_zero` |
| 63 | 2998–3000 | mathlib | `Mathlib.Analysis.Calculus.LocalExtr.Basic` — `Preconnected.isConstant_of_fderiv_eq_zero theorem family` |
| 64 | 3027–3029 | reformulated | `Mathlib.Analysis.Calculus.ContDiff.Defs` — `ContDiff coordinate/partial derivative characterization` |
| 65 | 3074–3080 | reformulated | `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv` — `HasStrictFDerivAt.toPartialHomeomorph / inverse function theorem` |
| 66 | 3313–3320 | mathlib | `Mathlib.Analysis.Calculus.ContDiff.Clairaut` — `second Fréchet derivative symmetry / Clairaut theorem` |
| 67 | 3365–3371 | reformulated | `Mathlib.Analysis.Calculus.ContDiff.Clairaut` — `ContDiffAt second derivative symmetry` |
| 68 | 3379–3385 | reformulated | `Mathlib.Analysis.Calculus.Taylor` — `second-order Taylor theorem / isLittleO remainder` |
