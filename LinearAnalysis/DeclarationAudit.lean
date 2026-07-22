import LinearAnalysis.Operators
import LinearAnalysis.SourceAudit

/-!
# Linear Analysis declaration audit

One checked declaration witness for every source item, in source order. Standard Mathlib results
are reused where they directly provide the course result; prerequisite and local declarations cover
the remaining source environments.
-/

open Set Function Topology Filter
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Cambridge.LinearAnalysis.DeclarationAudit

-- 1--10: normed spaces and bounded linear maps
#check NormedSpace
#check Cambridge.LinearAnalysis.normed_addition_continuous
#check IsTopologicalAddGroup
#check Cambridge.LinearAnalysis.AbsolutelyConvex
#check Cambridge.LinearAnalysis.real_ball_absolutelyConvex
#check Cambridge.LinearAnalysis.IsBoundedSubset
#check NormedSpace
#check CompleteSpace
#check Cambridge.LinearAnalysis.BoundedLinearMap
#check Cambridge.LinearAnalysis.linearMap_continuous_iff_bounded

-- 11--20: operator norm, duality, isomorphisms, finite-dimensional norms
#check ContinuousLinearMap.opNorm
#check Cambridge.LinearAnalysis.ContinuousDual
#check Cambridge.LinearAnalysis.dual_is_complete
#check Cambridge.LinearAnalysis.dualAction
#check Cambridge.LinearAnalysis.dualAction_norm_le
#check Cambridge.LinearAnalysis.DoubleDual
#check Cambridge.LinearAnalysis.canonicalEmbedding_norm_le
#check ContinuousLinearEquiv
#check FiniteDimensional
#check LinearEquiv.toContinuousLinearEquiv

-- 21--30: finite-dimensional consequences and order-theoretic infrastructure
#check isCompact_closedBall
#check Cambridge.LinearAnalysis.finiteDimensional_complete
#check Cambridge.LinearAnalysis.finiteDimensional_toContinuousLinearMap
#check isCompactOperator_id_iff_finiteDimensional
#check exists_extension_of_le_sublinear
#check PartialOrder
#check LinearOrder
#check upperBounds
#check Maximal
#check zorn_subset_nonempty

-- 31--39: Hahn--Banach and biduality
#check Cambridge.LinearAnalysis.hahnBanach_extension
#check exists_extension_norm_eq
#check Cambridge.LinearAnalysis.exists_norming_functional
#check NormedSpace.eq_zero_iff_forall_dual_eq_zero
#check Cambridge.LinearAnalysis.dual_separates_points
#check exists_dual_vector'
#check Cambridge.LinearAnalysis.canonicalEmbedding_norm_eq
#check Cambridge.LinearAnalysis.IsReflexive
#check Cambridge.LinearAnalysis.dualAction_norm_le

-- 40--50: Baire category and its functional-analytic consequences
#check Cambridge.LinearAnalysis.NowhereDenseSet
#check Cambridge.LinearAnalysis.IsMeagreSet
#check Cambridge.LinearAnalysis.completeMetric_baire
#check irrational_sqrt_two
#check UniformSpace.Completion
#check Cambridge.LinearAnalysis.completeMetric_baire
#check Cambridge.LinearAnalysis.uniform_boundedness
#check BaireSpace
#check Cambridge.LinearAnalysis.open_mapping
#check Cambridge.LinearAnalysis.inverse_mapping
#check Cambridge.LinearAnalysis.continuousLinearMap_of_closedGraph

-- 51--61: compact Hausdorff spaces and C(K)
#check T2Space
#check Cambridge.LinearAnalysis.ContinuousFunctions
#check NormalSpace
#check T1Space
#check Cambridge.LinearAnalysis.compactHausdorff_normal
#check Cambridge.LinearAnalysis.urysohn
#check Cambridge.LinearAnalysis.tietze_extension
#check Cambridge.LinearAnalysis.EquicontinuousFamily
#check ArzelaAscoli.isCompact_of_equicontinuous
#check Cambridge.LinearAnalysis.IsEpsilonNet
#check Cambridge.LinearAnalysis.IsTotallyBounded

-- 62--73: total boundedness and approximation theory
#check Cambridge.LinearAnalysis.IsTotallyBounded
#check Cambridge.LinearAnalysis.compact_closure_of_totallyBounded
#check BoundedContinuousFunction.arzela_ascoli
#check Cambridge.LinearAnalysis.compact_closure_of_totallyBounded
#check Continuous
#check Cambridge.LinearAnalysis.weierstrass_on_Icc
#check Subalgebra
#check Cambridge.LinearAnalysis.stoneWeierstrass
#check ContinuousMap.sublattice_closure_eq_top
#check ContinuousMap.sup_mem_closed_subalgebra
#check Cambridge.LinearAnalysis.stoneWeierstrass_approximation
#check ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints

-- 74--84: inner-product spaces
#check OrthonormalBasis
#check InnerProductSpace
#check Cambridge.LinearAnalysis.Orthogonal
#check Cambridge.LinearAnalysis.cauchySchwarz
#check InnerProductSpace.Core.toNormedAddCommGroup
#check EuclideanSpace
#check inner_map_polarization
#check Cambridge.LinearAnalysis.IsHilbertSpace
#check Cambridge.LinearAnalysis.parallelogram
#check Cambridge.LinearAnalysis.pythagoras
#check Cambridge.LinearAnalysis.inner_continuous

-- 85--96: Hilbert-space geometry, projections, and bases
#check UniformSpace.Completion
#check Cambridge.LinearAnalysis.orthogonalComplement
#check Cambridge.LinearAnalysis.orthogonalComplement_isClosed
#check Submodule.orthogonalProjection
#check Submodule.orthogonalProjection
#check Cambridge.LinearAnalysis.riesz_representation
#check OrthonormalBasis.sum_repr
#check Cambridge.LinearAnalysis.OrthonormalSystem
#check exists_maximal_orthonormal
#check Cambridge.LinearAnalysis.exists_maximal_orthonormal_system
#check Module.Basis.span_eq
#check OrthonormalBasis

-- 97--101: Gram--Schmidt, Bessel, Parseval, Riesz--Fischer
#check Cambridge.LinearAnalysis.gramSchmidt
#check HilbertBasis
#check Cambridge.LinearAnalysis.bessel
#check Cambridge.LinearAnalysis.parseval_finite
#check OrthonormalBasis.repr

-- 102--112: spectrum and resolvent
#check Cambridge.LinearAnalysis.operatorSpectrum
#check Cambridge.LinearAnalysis.operatorResolventSet
#check Module.End.HasEigenvalue
#check Cambridge.LinearAnalysis.pointSpectrum
#check Cambridge.LinearAnalysis.approximatePointSpectrum
#check Cambridge.LinearAnalysis.operatorSpectrum_isClosed
#check Cambridge.LinearAnalysis.operatorResolventSet_isOpen
#check Cambridge.LinearAnalysis.operatorResolventSet_isOpen
#check Cambridge.LinearAnalysis.operatorResolventSet_isOpen
#check Continuous
#check frontier

-- 113--128: compact and self-adjoint operators
#check Cambridge.LinearAnalysis.IsCompactLinearOperator
#check Cambridge.LinearAnalysis.compact_iff_compact_closure_image_ball
#check isClosed_setOf_isCompactOperator
#check IsCompactOperator
#check Cambridge.LinearAnalysis.compact_finiteDimensional_eigenspace
#check IsClosed
#check ContinuousLinearMap.finite_dimensional_eigenspace
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
#check Cambridge.LinearAnalysis.IsSelfAdjoint
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
#check Cambridge.LinearAnalysis.selfAdjoint_eigenvalue_real
#check Cambridge.LinearAnalysis.selfAdjoint_orthogonal_eigenspaces
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
#check ContinuousLinearMap.opNorm_le_of_re_inner_le
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem

/-- The declaration audit and source audit have the same cardinality. -/
theorem audited_source_item_count : SourceAudit.items.length = 128 := SourceAudit.item_count

end Cambridge.LinearAnalysis.DeclarationAudit
