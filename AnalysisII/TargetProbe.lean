import Mathlib

/-! Temporary API probe for the Analysis II completion branch. -/

#check tendsto_pi_nhds
#check Metric.cauchySeq_iff
#check cauchySeq_bdd
#check CauchySeq.tendsto_of_subseq_tendsto
#check IsCompact.isSeqCompact
#check isCompact_closedBall
#check Metric.isCompact_iff_isClosed_bounded
#check IsCompact.isClosed
#check IsCompact.isBounded
#check IsCompact.image
#check FiniteDimensional.proper
#check FiniteDimensional.complete
#check completeSpace_coe_iff_isClosed
#check isCompact_iff_totallyBounded_isComplete
#check continuousAt_iff_seq_tendsto
#check continuous_iff_isOpen
#check continuous_iff_isClosed
#check IsCompact.uniformContinuousOn_of_continuous
#check ContractingWith.fixedPoint_unique
#check ContractingWith.fixedPoint_isFixedPt
#check ContractingWith.isFixedPt_fixedPoint_iterate
#check ODE_solution_unique
#check HasFDerivAt.continuousAt
#check HasFDerivAt.clm_apply
#check ContinuousLinearMap.le_opNorm
#check ContinuousLinearMap.opNorm_comp_le
#check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
#check IsPreconnected.eqOn_of_fderivWithin_eq_zero
#check HasStrictFDerivAt.localInverse
#check ContDiffAt.localInverse
#check ContDiffAt.clairaut
#check HasFDerivAt.taylor_mean_remainder
