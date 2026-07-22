import Mathlib

/-!
# Part IA Differential Equations: declaration inventory

This is a declaration-for-declaration inventory of the labelled mathematical
content in `IA_M/differential_equations.tex` (2014, M. G. Worster).  Line
numbers refer to the source retrieved on 2026-07-21.
-/

namespace DifferentialEquations.SourceAudit

inductive Kind where
  | definition | theorem | proposition | notation
  deriving DecidableEq, Repr

inductive Disposition where
  | mathlib | wrapper | corrected | notation
  deriving DecidableEq, Repr

structure Entry where
  line : Nat
  kind : Kind
  title : String
  target : String
  disposition : Disposition
  deriving DecidableEq, Repr

def inventory : List Entry := [
  ⟨71, .definition, "Derivative of function", "HasDerivAt", .mathlib⟩,
  ⟨83, .notation, "Prime derivative notation", "firstDerivative; secondDerivative", .notation⟩,
  ⟨90, .definition, "little-o and big-O", "Filter.IsLittleO; Filter.IsBigO", .mathlib⟩,
  ⟨110, .proposition, "Derivative as first-order approximation", "HasDerivAt.isLittleO", .mathlib⟩,
  ⟨125, .theorem, "Chain rule", "HasDerivAt.comp", .wrapper⟩,
  ⟨144, .theorem, "Product rule", "HasDerivAt.mul", .wrapper⟩,
  ⟨151, .theorem, "Leibniz rule", "iteratedDeriv and repeated HasDerivAt.mul", .wrapper⟩,
  ⟨160, .theorem, "Taylor theorem", "taylor_mean_remainder", .corrected⟩,
  ⟨176, .theorem, "L'Hopital rule", "HasDerivAt.lhopital_zero_nhds", .corrected⟩,
  ⟨193, .definition, "Integral", "intervalIntegral", .mathlib⟩,
  ⟨221, .theorem, "Fundamental theorem of calculus", "Continuous.integral_hasStrictDerivAt", .mathlib⟩,
  ⟨242, .notation, "Indefinite integral notation", "AntiderivativeOf", .notation⟩,
  ⟨279, .theorem, "Integration by parts", "intervalIntegral.integral_mul_deriv_eq_deriv_mul", .mathlib⟩,
  ⟨309, .definition, "Partial derivative", "fderiv; deriv of a slice", .wrapper⟩,
  ⟨330, .notation, "Partial derivative subscripts", "partialX; partialY", .notation⟩,
  ⟨336, .theorem, "Equality of mixed partials", "ContDiffAt.isSymmSndFDerivAt", .mathlib⟩,
  ⟨351, .theorem, "Multivariable chain rule", "HasFDerivAt.comp", .mathlib⟩,
  ⟨387, .theorem, "Implicit differentiation", "hasStrictFDerivAt_implicitFunctionOfBivariate", .corrected⟩,
  ⟨419, .theorem, "Differentiation under the integral sign", "hasDerivAt_integral_of_dominated_loc_of_deriv_le", .corrected⟩,
  ⟨462, .definition, "Exponential function", "Real.exp", .mathlib⟩,
  ⟨474, .definition, "Eigenfunction", "Eigenfunction", .wrapper⟩,
  ⟨487, .definition, "Linear differential equation", "LinearODE", .wrapper⟩,
  ⟨491, .definition, "Homogeneous differential equation", "HomogeneousODE", .wrapper⟩,
  ⟨495, .definition, "Constant coefficients", "ConstantCoefficientSecondOrder", .wrapper⟩,
  ⟨499, .definition, "First-order differential equation", "FirstOrderODE", .wrapper⟩,
  ⟨503, .theorem, "Exponential solutions for constant coefficients", "exp_solution_constantCoefficient", .corrected⟩,
  ⟨686, .definition, "Separable equation", "SeparableFirstOrder", .wrapper⟩,
  ⟨711, .definition, "Exact equation", "ExactDifferential", .wrapper⟩,
  ⟨731, .definition, "Simply-connected domain", "SimplyConnected", .wrapper⟩,
  ⟨739, .theorem, "Closed one-form is exact", "exact_of_potential (explicit-potential course wrapper)", .corrected⟩,
  ⟨858, .definition, "Equilibrium/fixed point", "Equilibrium", .wrapper⟩,
  ⟨863, .definition, "Stability of fixed point", "AttractingEquilibrium", .corrected⟩,
  ⟨905, .definition, "Autonomous system", "AutonomousSystem", .wrapper⟩,
  ⟨1138, .definition, "Characteristic equation", "characteristicPolynomial", .corrected⟩,
  ⟨1239, .definition, "Wronskian", "wronskian", .wrapper⟩,
  ⟨1246, .definition, "Independent solutions", "IndependentSolutions", .wrapper⟩,
  ⟨1261, .theorem, "Abel's theorem", "abel_dichotomy", .wrapper⟩,
  ⟨1462, .definition, "Equidimensional equation", "EquidimensionalSecondOrder", .wrapper⟩,
  ⟨1675, .definition, "Dirac delta", "Measure.dirac", .corrected⟩,
  ⟨1746, .definition, "Heaviside step function", "heaviside", .corrected⟩,
  ⟨1778, .definition, "Ordinary and singular points", "OrdinaryPoint; RegularSingularPoint", .wrapper⟩,
  ⟨1997, .definition, "Directional derivative", "directionalDerivative", .wrapper⟩,
  ⟨2004, .definition, "Gradient vector", "gradient", .wrapper⟩,
  ⟨2081, .definition, "Hessian matrix", "hessian", .wrapper⟩,
  ⟨2140, .definition, "Signature of Hessian matrix", "leadingPrincipalMinor", .wrapper⟩,
  ⟨2158, .proposition, "Sylvester criterion", "Matrix.PosDef iff leading principal minors", .corrected⟩,
  ⟨2468, .definition, "Equilibrium point (two-dimensional system)", "Equilibrium₂", .wrapper⟩
]

theorem inventory_count : inventory.length = 47 := by decide

end DifferentialEquations.SourceAudit
