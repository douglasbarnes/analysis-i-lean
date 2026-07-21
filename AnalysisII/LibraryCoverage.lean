import Mathlib

/-!
Exact declaration checks for the Mathlib APIs used by the Analysis II audit. These commands are
compiled by Lean, so a renamed or absent library target fails the build rather than silently leaving a
stale prose mapping.
-/

#check TendstoUniformlyOn.uniformCauchySeqOn
#check UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
#check TendstoUniformlyOn.continuousOn
#check TendstoUniformly.continuous
#check hasFDerivAt_of_tendstoUniformlyOn
#check ContractingWith.exists_fixedPoint
#check ContractingWith.fixedPoint_unique
#check ContractingWith.isFixedPt_fixedPoint_iterate
#check IsCompact.uniformContinuousOn_of_continuous
#check Metric.isOpen_ball
#check tendsto_nhds_unique
#check isOpen_iUnion
#check isClosed_iInter
#check Set.Finite.isClosed
#check HasFDerivAt.unique
#check HasFDerivAt.continuousAt
#check ContinuousLinearMap.hasFDerivAt
#check ContinuousLinearMap.le_opNorm
#check HasFDerivAt.comp
#check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
#check norm_integral_le_integral_norm
