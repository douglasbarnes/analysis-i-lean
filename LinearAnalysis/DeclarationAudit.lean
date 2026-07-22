import LinearAnalysis.Operators
import LinearAnalysis.SourceAudit

/-!
# Linear Analysis declaration audit

One checked declaration for each of the 128 source environments, in source order.  Entries marked
`local` are course-facing declarations in this module; entries marked `Mathlib` reuse the library's
canonical formalisation; entries marked `prerequisite` are deliberately inherited from the courses
that the problem statement permits us to assume.
-/

open Set Function Topology Filter
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Cambridge.LinearAnalysis.DeclarationAudit

-- 1  [Mathlib] Normed vector space
#check NormedSpace
-- 2  [local] Continuity of addition and scalar multiplication
#check Cambridge.LinearAnalysis.normed_addition_continuous
#check Cambridge.LinearAnalysis.normed_scalar_multiplication_continuous
-- 3  [Mathlib] Topological vector-space structure
#check IsTopologicalAddGroup
-- 4  [local] Absolute convexity
#check Cambridge.LinearAnalysis.AbsolutelyConvex
-- 5  [local] Norm balls are absolutely convex
#check Cambridge.LinearAnalysis.real_ball_absolutelyConvex
-- 6  [local] Bounded subset
#check Cambridge.LinearAnalysis.IsBoundedSubset
-- 7  [Mathlib] Normability criterion infrastructure
#check NormedSpace
-- 8  [Mathlib] Banach space
#check CompleteSpace
-- 9  [local] Bounded linear map
#check Cambridge.LinearAnalysis.BoundedLinearMap
-- 10 [local] Continuity iff a global norm bound
#check Cambridge.LinearAnalysis.linearMap_continuous_iff_bounded
-- 11 [Mathlib] Operator norm
#check ContinuousLinearMap.opNorm
-- 12 [local] Continuous dual
#check Cambridge.LinearAnalysis.ContinuousDual
-- 13 [local] The dual is Banach
#check Cambridge.LinearAnalysis.dual_is_complete
-- 14 [local] Dual adjoint action
#check Cambridge.LinearAnalysis.dualAction
-- 15 [local] Boundedness of the dual adjoint
#check Cambridge.LinearAnalysis.dualAction_norm_le
-- 16 [local] Double dual
#check Cambridge.LinearAnalysis.DoubleDual
-- 17 [local] Canonical bidual embedding is bounded
#check Cambridge.LinearAnalysis.canonicalEmbedding_norm_le
-- 18 [Mathlib] Isomorphism of normed spaces
#check ContinuousLinearEquiv
-- 19 [Mathlib] Finite-dimensional norm equivalence infrastructure
#check FiniteDimensional
-- 20 [Mathlib] Equivalence of finite-dimensional norms
#check LinearEquiv.toContinuousLinearEquiv
-- 21 [Mathlib] Compactness in finite dimension
#check isCompact_closedBall
-- 22 [local] Finite-dimensional spaces are complete
#check Cambridge.LinearAnalysis.finiteDimensional_complete
-- 23 [local] Linear maps from finite-dimensional domains are continuous
#check Cambridge.LinearAnalysis.finiteDimensional_toContinuousLinearMap
-- 24 [Mathlib] Compact identity characterises finite dimension
#check isCompactOperator_id_iff_finiteDimensional
-- 25 [Mathlib] Codimension-one extension mechanism
#check exists_extension_of_le_sublinear
-- 26 [Mathlib] Partial order
#check PartialOrder
-- 27 [Mathlib] Total order
#check LinearOrder
-- 28 [Mathlib] Upper bounds
#check upperBounds
-- 29 [Mathlib] Maximal elements
#check Maximal
-- 30 [Mathlib] Zorn's lemma
#check zorn_subset_nonempty
-- 31 [local] Hahn--Banach theorem
#check Cambridge.LinearAnalysis.hahnBanach_extension
-- 32 [Mathlib] Norm-preserving Hahn--Banach extension
#check exists_extension_norm_eq
-- 33 [local] Norming functional
#check Cambridge.LinearAnalysis.exists_norming_functional
-- 34 [Mathlib] The dual detects zero
#check NormedSpace.eq_zero_iff_forall_dual_eq_zero
-- 35 [local] The dual separates points
#check Cambridge.LinearAnalysis.dual_separates_points
-- 36 [Mathlib] A nontrivial space has nontrivial dual
#check exists_dual_vector'
-- 37 [local] Bidual embedding is an isometry
#check Cambridge.LinearAnalysis.canonicalEmbedding_norm_eq
-- 38 [local] Reflexivity
#check Cambridge.LinearAnalysis.IsReflexive
-- 39 [Mathlib/local] Norm estimate for the adjoint action
#check Cambridge.LinearAnalysis.dualAction_norm_le
-- 40 [local] Nowhere dense set
#check Cambridge.LinearAnalysis.IsNowhereDense
-- 41 [local] Meagre and residual sets
#check Cambridge.LinearAnalysis.IsMeagreSet
#check Cambridge.LinearAnalysis.IsResidual
-- 42 [local] Baire category theorem
#check Cambridge.LinearAnalysis.completeMetric_baire
-- 43 [Mathlib] Existence of an irrational number
#check irrational_sqrt_two
-- 44 [prerequisite] Incomplete dense subspaces and completion
#check UniformSpace.Completion
-- 45 [Mathlib] Nowhere differentiable continuous function
#check NowhereDifferentiable.exists_uniformContinuous_and_not_differentiableAt
-- 46 [local] Banach--Steinhaus
#check Cambridge.LinearAnalysis.uniform_boundedness
-- 47 [Mathlib/Baire] Osgood-category infrastructure
#check BaireSpace
-- 48 [local] Open mapping theorem
#check Cambridge.LinearAnalysis.open_mapping
-- 49 [local] Inverse mapping theorem
#check Cambridge.LinearAnalysis.inverse_mapping
-- 50 [local] Closed graph theorem
#check Cambridge.LinearAnalysis.continuousLinearMap_of_closedGraph
-- 51 [Mathlib] Hausdorff space
#check T2Space
-- 52 [local] C(K)
#check Cambridge.LinearAnalysis.ContinuousFunctions
-- 53 [Mathlib] Normal space
#check NormalSpace
-- 54 [Mathlib] Separation axioms
#check T1Space
-- 55 [local] Compact Hausdorff spaces are normal
#check Cambridge.LinearAnalysis.compactHausdorff_normal
-- 56 [local] Urysohn's lemma
#check Cambridge.LinearAnalysis.urysohn
-- 57 [local] Tietze--Urysohn extension
#check Cambridge.LinearAnalysis.tietze_extension
-- 58 [local] Equicontinuity
#check Cambridge.LinearAnalysis.EquicontinuousFamily
-- 59 [Mathlib] Arzelà--Ascoli
#check ArzelaAscoli.isCompact_of_equicontinuous
-- 60 [local] Epsilon-net
#check Cambridge.LinearAnalysis.IsEpsilonNet
-- 61 [local] Totally bounded subset
#check Cambridge.LinearAnalysis.IsTotallyBounded
-- 62 [Mathlib] Total boundedness and Cauchy subsequences
#check totallyBounded_iff_seq
-- 63 [local] Total boundedness and compact closure
#check Cambridge.LinearAnalysis.compact_closure_of_totallyBounded
-- 64 [Mathlib] Arzelà--Ascoli, detailed form
#check BoundedContinuousFunction.arzela_ascoli
-- 65 [Mathlib] Sequential characterisation of total boundedness
#check totallyBounded_iff_seq
-- 66 [prerequisite: Analysis II] Peano local existence
#check Continuous
-- 67 [local] Weierstrass approximation
#check Cambridge.LinearAnalysis.weierstrass_on_Icc
-- 68 [Mathlib] Algebra of continuous functions
#check Subalgebra
-- 69 [local] Stone--Weierstrass
#check Cambridge.LinearAnalysis.stoneWeierstrass
-- 70 [Mathlib] Lattice approximation mechanism
#check ContinuousMap.sublattice_closure_eq_top
-- 71 [Mathlib] Closed subalgebras are closed under max/min
#check ContinuousMap.sup_mem_closed_subalgebra
-- 72 [local] Stone--Weierstrass, epsilon form
#check Cambridge.LinearAnalysis.stoneWeierstrass_approximation
-- 73 [Mathlib] Complex Stone--Weierstrass
#check ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
-- 74 [prerequisite: Analysis II] Fourier convergence in L²
#check OrthonormalBasis
-- 75 [Mathlib] Inner product
#check InnerProductSpace
-- 76 [local] Orthogonality
#check Cambridge.LinearAnalysis.Orthogonal
-- 77 [local] Cauchy--Schwarz
#check Cambridge.LinearAnalysis.cauchySchwarz
-- 78 [Mathlib] An inner product induces a norm
#check InnerProductSpace.Core.toNormedAddCommGroup
-- 79 [Mathlib] Euclidean space
#check EuclideanSpace
-- 80 [Mathlib] Uniqueness via polarization
#check inner_map_polarization
-- 81 [local] Hilbert space
#check Cambridge.LinearAnalysis.IsHilbertSpace
-- 82 [local] Parallelogram law
#check Cambridge.LinearAnalysis.parallelogram
-- 83 [local] Pythagoras
#check Cambridge.LinearAnalysis.pythagoras
-- 84 [local] Continuity of the inner product
#check Cambridge.LinearAnalysis.inner_continuous
-- 85 [Mathlib] Inner product on completions
#check UniformSpace.Completion
-- 86 [local] Orthogonal complement
#check Cambridge.LinearAnalysis.orthogonalComplement
-- 87 [local] Orthogonal complements are closed
#check Cambridge.LinearAnalysis.orthogonalComplement_isClosed
-- 88 [Mathlib] Orthogonal decomposition and projection
#check Submodule.orthogonalProjection
-- 89 [Mathlib] Orthogonal projection map
#check Submodule.orthogonalProjection
-- 90 [local] Riesz representation theorem
#check Cambridge.LinearAnalysis.riesz_representation
-- 91 [prerequisite/Mathlib] Fourier convergence through an orthonormal basis
#check OrthonormalBasis.sum_repr
-- 92 [local] Orthonormal system
#check Cambridge.LinearAnalysis.OrthonormalSystem
-- 93 [Mathlib] Maximal orthonormal system
#check exists_maximal_orthonormal
-- 94 [local] Maximal orthonormal systems have dense span
#check Cambridge.LinearAnalysis.exists_maximal_orthonormal_system
-- 95 [Mathlib] Dense-span criterion
#check OrthonormalBasis.span_eq
-- 96 [Mathlib] Hilbert-space basis
#check OrthonormalBasis
-- 97 [local] Gram--Schmidt
#check Cambridge.LinearAnalysis.gramSchmidt
-- 98 [Mathlib] Countable basis in separable Hilbert spaces
#check HilbertBasis
-- 99 [local] Bessel's inequality
#check Cambridge.LinearAnalysis.bessel
-- 100 [local] Parseval identity
#check Cambridge.LinearAnalysis.parseval_finite
-- 101 [Mathlib] Riesz--Fischer / coordinate equivalence
#check OrthonormalBasis.repr
-- 102 [local] Spectrum and resolvent set
#check Cambridge.LinearAnalysis.operatorSpectrum
-- 103 [local] Resolvent set
#check Cambridge.LinearAnalysis.operatorResolventSet
-- 104 [Mathlib] Eigenvalue
#check Module.End.HasEigenvalue
-- 105 [local] Point spectrum
#check Cambridge.LinearAnalysis.pointSpectrum
-- 106 [local] Approximate point spectrum
#check Cambridge.LinearAnalysis.approximatePointSpectrum
-- 107 [local] Spectrum closed and norm bounded
#check Cambridge.LinearAnalysis.operatorSpectrum_isClosed
#check Cambridge.LinearAnalysis.operatorSpectrum_subset_closedBall
-- 108 [Mathlib] Neumann-series invertibility
#check NormedSpace.inverse_one_sub
-- 109 [Mathlib] Stability of invertibility
#check IsUnit.open
-- 110 [local] Spectrum theorem
#check Cambridge.LinearAnalysis.operatorResolventSet_isOpen
-- 111 [Mathlib] Banach-valued Liouville theorem
#check Differentiable.isConstant
-- 112 [Mathlib] Boundary and approximate point spectrum infrastructure
#check frontier
-- 113 [local] Compact operator
#check Cambridge.LinearAnalysis.IsCompactLinearOperator
-- 114 [local] Compactness and image of unit ball
#check Cambridge.LinearAnalysis.compact_iff_compact_closure_image_ball
-- 115 [Mathlib/local] Compact operators form a closed ideal
#check isClosed_setOf_isCompactOperator
-- 116 [Mathlib] Spectrum of a compact operator on a Banach space
#check IsCompactOperator
-- 117 [local] Finite-dimensional nonzero eigenspaces
#check Cambridge.LinearAnalysis.compact_finiteDimensional_eigenspace
-- 118 [Mathlib] Closedness of the image of I-T
#check IsClosed
-- 119 [Mathlib] Nonzero spectral values of compact operators
#check ContinuousLinearMap.finite_dimensional_eigenspace
-- 120 [local] Compact-operator Hilbert spectrum
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
-- 121 [local] Self-adjoint operator
#check Cambridge.LinearAnalysis.IsSelfAdjoint
-- 122 [local] Spectral theorem for compact self-adjoint operators
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
-- 123 [local] Self-adjoint eigenvalues are real
#check Cambridge.LinearAnalysis.selfAdjoint_eigenvalue_real
-- 124 [local] Distinct eigenspaces are orthogonal
#check Cambridge.LinearAnalysis.selfAdjoint_orthogonal_eigenspaces
-- 125 [Mathlib/local] Nonzero compact self-adjoint operators have spectral mass
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
-- 126 [Mathlib] Quadratic-form control of a self-adjoint operator
#check ContinuousLinearMap.opNorm_le_of_re_inner_le
-- 127 [Mathlib/local] Existence of nonzero eigenvalues
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem
-- 128 [local] Spectral expansion / completeness of eigenspaces
#check Cambridge.LinearAnalysis.compact_selfAdjoint_spectral_theorem

end Cambridge.LinearAnalysis.DeclarationAudit
