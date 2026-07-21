import MethodsCourse.Core
import MethodsCourse.SourceAudit

-- Exactly one witness for each labelled environment, in TeX order.
#check MethodsCourse.VectorSpace
#check MethodsCourse.InnerProduct
#check MethodsCourse.FiniteBasis
#check MethodsCourse.IsHomogeneousBoundary
#check MethodsCourse.IsPeriodic
#check MethodsCourse.parseval_theorem
#check MethodsCourse.AdjointPair
#check MethodsCourse.weightedInnerProduct
#check MethodsCourse.IsWeightedEigenfunction
#check MethodsCourse.sturm_liouville_eigenvalues_real
#check MethodsCourse.distinct_eigenfunctions_orthogonal
#check MethodsCourse.compact_sturm_liouville_discrete
#check MethodsCourse.eigenfunction_completeness
#check MethodsCourse.weighted_parseval
#check MethodsCourse.SatisfiesLaplaceEquation
#check MethodsCourse.IsHarmonic
#check MethodsCourse.dirichlet_problem_exists_unique
#check MethodsCourse.SatisfiesHeatEquation
#check MethodsCourse.heat_equation_unique
#check MethodsCourse.wave_energy_conservation
#check MethodsCourse.wave_equation_unique
#check MethodsCourse.diracDelta
#check MethodsCourse.fourierTransform
#check MethodsCourse.fourier_transform_parseval
#check MethodsCourse.WellPosedProblem
#check MethodsCourse.tangentVector
#check MethodsCourse.IsIntegralCurve
#check MethodsCourse.symbolAndPrincipalPart
#check MethodsCourse.classifyEigenvalues
#check MethodsCourse.IsCharacteristic
#check MethodsCourse.greens_first_identity
#check MethodsCourse.greens_second_identity
#check MethodsCourse.greens_third_identity

namespace MethodsCourse.DeclarationAudit

theorem witness_count : MethodsCourse.SourceAudit.inventory.length = 33 :=
  MethodsCourse.SourceAudit.authoritative_count

end MethodsCourse.DeclarationAudit
