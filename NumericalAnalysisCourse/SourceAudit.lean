import NumericalAnalysisCourse.Core

/-! Exact ordered inventory of labelled environments in `IB_L/numerical_analysis.tex`. -/

namespace NumericalAnalysisCourse.SourceAudit

inductive Kind where
  | notation | definition | theorem | lemma | proposition | corollary
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨39, .notation, "P_n[x]"⟩
  , ⟨70, .definition, "Lagrange cardinal polynomials"⟩
  , ⟨83, .theorem, "Existence and uniqueness of interpolation"⟩
  , ⟨140, .theorem, "Recurrence relation for Newton divided differences"⟩
  , ⟨198, .lemma, "Iterated Rolle zero count"⟩
  , ⟨206, .theorem, "Mean-value formula for divided differences"⟩
  , ⟨219, .theorem, "Interpolation error identity"⟩
  , ⟨240, .theorem, "Smooth interpolation error formula"⟩
  , ⟨256, .corollary, "Interpolation sup-norm error bound"⟩
  , ⟨272, .definition, "Chebyshev polynomial"⟩
  , ⟨316, .lemma, "3-term recurrence relation"⟩
  , ⟨334, .theorem, "Minimal property for n ≥ 1"⟩
  , ⟨348, .corollary, "Minimal nodal polynomial norm"⟩
  , ⟨363, .theorem, "Chebyshev interpolation bound"⟩
  , ⟨403, .definition, "Orthogonalilty"⟩
  , ⟨408, .definition, "Orthogonal polynomial"⟩
  , ⟨418, .definition, "Monic polynomial"⟩
  , ⟨425, .theorem, "Unique monic orthogonal polynomial"⟩
  , ⟨473, .theorem, "Orthogonal-polynomial three-term recurrence"⟩
  , ⟨562, .theorem, "Orthogonal projection minimizes error"⟩
  , ⟨613, .definition, "Linear functional"⟩
  , ⟨687, .proposition, "Quadrature degree barrier"⟩
  , ⟨708, .theorem, "Ordinary quadrature"⟩
  , ⟨723, .theorem, "Zeros of orthogonal polynomials"⟩
  , ⟨746, .theorem, "Gaussian quadrature exactness"⟩
  , ⟨809, .definition, "Sharp error bound"⟩
  , ⟨849, .theorem, "Peano kernel theorem"⟩
  , ⟨857, .definition, "Peano kernel"⟩
  , ⟨957, .definition, "Lipschitz function"⟩
  , ⟨983, .definition, "(Explicit) one-step method"⟩
  , ⟨993, .definition, "Euler's method"⟩
  , ⟨1001, .definition, "Convergence of numerical method"⟩
  , ⟨1011, .theorem, "Convergence of Euler's method"⟩
  , ⟨1076, .definition, "Local truncation error"⟩
  , ⟨1090, .definition, "Order"⟩
  , ⟨1096, .definition, "θ-method"⟩
  , ⟨1118, .definition, "2-step Adams-Bashforth method"⟩
  , ⟨1127, .definition, "Multi-step method"⟩
  , ⟨1147, .theorem, "Multi-step order conditions"⟩
  , ⟨1181, .theorem, "Generating-polynomial order criterion"⟩
  , ⟨1216, .definition, "Root condition"⟩
  , ⟨1223, .theorem, "Dahlquist equivalence theorem"⟩
  , ⟨1273, .definition, "Adams method"⟩
  , ⟨1278, .definition, "Adams-Bashforth method"⟩
  , ⟨1282, .definition, "Adams-Moulton method"⟩
  , ⟨1303, .definition, "Backward differentiation method"⟩
  , ⟨1312, .lemma, "Backward differentiation coefficients"⟩
  , ⟨1343, .definition, "Runge-Kutta method"⟩
  , ⟨1474, .definition, "Linear stability domain"⟩
  , ⟨1530, .definition, "A-stability"⟩
  , ⟨1564, .theorem, "Maximum principle"⟩
  , ⟨1671, .definition, "Triangular matrix"⟩
  , ⟨1770, .definition, "LU factorization"⟩
  , ⟨1922, .definition, "Leading principal submatrix"⟩
  , ⟨1930, .theorem, "Existence and uniqueness of LU"⟩
  , ⟨1940, .theorem, "Unique LDU factorization"⟩
  , ⟨1957, .theorem, "Symmetric LDLᵀ factorization"⟩
  , ⟨1978, .definition, "Positive definite matrix"⟩
  , ⟨1986, .theorem, "Positive definite leading minors"⟩
  , ⟨1998, .theorem, "Positive definite iff positive LDLᵀ"⟩
  , ⟨2029, .definition, "Cholesky factorization"⟩
  , ⟨2043, .definition, "Band matrix"⟩
  , ⟨2055, .proposition, "LU preserves bandwidth"⟩
  , ⟨2081, .theorem, "Least-squares normal equation"⟩
  , ⟨2112, .corollary, "Full-rank least-squares uniqueness"⟩
  , ⟨2134, .definition, "Orthogonal matrix"⟩
  , ⟨2146, .definition, "QR factorization"⟩
  , ⟨2263, .definition, "Givens rotation"⟩
  , ⟨2384, .definition, "Householder reflection"⟩
  , ⟨2408, .proposition, "Householder triangularization"⟩
  , ⟨2419, .lemma, "Householder maps equal-norm vectors"⟩
  , ⟨2456, .lemma, "Householder preserves initial components"⟩
  , ⟨2465, .lemma, "Householder tail mapping"⟩ ]

theorem item_count : items.length = 73 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide

def countKind (k : Kind) : ℕ := (items.filter fun x ↦ x.kind = k).length

theorem notation_count : countKind .notation = 1 := by native_decide
theorem definition_count : countKind .definition = 35 := by native_decide
theorem theorem_count : countKind .theorem = 25 := by native_decide
theorem lemma_count : countKind .lemma = 6 := by native_decide
theorem proposition_count : countKind .proposition = 3 := by native_decide
theorem corollary_count : countKind .corollary = 3 := by native_decide

theorem kind_counts_complete :
    countKind .notation + countKind .definition + countKind .theorem + countKind .lemma +
      countKind .proposition + countKind .corollary = items.length := by
  native_decide

end NumericalAnalysisCourse.SourceAudit
