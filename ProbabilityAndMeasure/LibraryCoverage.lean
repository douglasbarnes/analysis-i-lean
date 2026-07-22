import Mathlib

/-!
# Probability and Measure: compiled Mathlib coverage

These checks are part of the build.  They witness the library results used for the technically
substantial results in the source notes and fail if the pinned Mathlib API changes.
-/

/-! ## Measures, independence, and Borel--Cantelli -/

#check MeasureTheory.measure_iUnion
#check MeasureTheory.measure_limsup_atTop_eq_zero
#check ProbabilityTheory.measure_limsup_eq_one
#check ProbabilityTheory.iIndepSet
#check ProbabilityTheory.iIndepFun

/-! ## Integration and convergence -/

#check MeasureTheory.integral_add
#check MeasureTheory.integral_finsetSum
#check MeasureTheory.lintegral_liminf_le
#check MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
#check MeasureTheory.tendsto_lintegral_of_dominated_convergence
#check MeasureTheory.integral_condExp
#check MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul

/-! ## Inequalities and `Lᵖ` -/

#check MeasureTheory.mul_meas_ge_le_pow_eLpNorm'
#check ProbabilityTheory.meas_ge_le_variance_div_sq
#check MeasureTheory.MemLp
#check MeasureTheory.Lp

/-! ## Moments, Gaussian laws, characteristic functions, and limits -/

#check ProbabilityTheory.IndepFun.variance_add
#check ProbabilityTheory.integral_gaussianPDFReal_eq_one
#check ProbabilityTheory.integral_id_gaussianReal
#check ProbabilityTheory.variance_id_gaussianReal
#check ProbabilityTheory.iteratedDeriv_mgf_zero
#check ProbabilityTheory.IndepFun.mgf_add
#check ProbabilityTheory.mgf_id_gaussianReal
#check ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
#check MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun
#check ProbabilityTheory.strong_law_Lp
#check ProbabilityTheory.strong_law_ae
#check ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub

/-! ## Fourier analysis -/

#check VectorFourier.fourierIntegral
