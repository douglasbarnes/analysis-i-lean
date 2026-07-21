import DifferentialEquations.Core

/-! Compile-time witnesses for the Mathlib notions used to close the course inventory. -/

#check HasDerivAt
#check HasDerivAt.isLittleO
#check HasDerivAt.comp
#check HasDerivAt.mul
#check HasDerivAt.lhopital_zero_nhds
#check HasFDerivAt.comp
#check Asymptotics.IsLittleO
#check Asymptotics.IsBigO
#check Real.exp
#check Real.hasDerivAt_exp
#check intervalIntegral
#check ContDiff
#check ContDiffAt.isSymmSndFDerivAt
#check AnalyticAt
#check MeasureTheory.Measure.dirac
#check Matrix.det
#check IsPathConnected
#check IsSimplyConnected
#check taylor_isLittleO
#check Continuous.integral_hasStrictDerivAt
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check hasStrictFDerivAt_implicitFunctionOfBivariate
#check hasDerivAt_integral_of_dominated_loc_of_deriv_le
