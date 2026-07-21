import ComplexAnalysisCourse.Core

/-! Machine-checked inventory of every labelled environment in `IB_L/complex_analysis.tex`. -/

namespace ComplexAnalysisCourse.SourceAudit

inductive Kind where
  | definition | theorem | proposition | corollary | lemma | notation
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨46, .definition, "Open subset"⟩
  , ⟨62, .definition, "Path-connected subset"⟩
  , ⟨67, .definition, "Domain"⟩
  , ⟨72, .definition, "Differentiable function"⟩
  , ⟨83, .definition, "Analytic/holomorphic function"⟩
  , ⟨87, .definition, "Entire function"⟩
  , ⟨105, .proposition, "Cauchy-Riemann characterization"⟩
  , ⟨167, .definition, "Conformal function"⟩
  , ⟨218, .definition, "Conformal equivalence"⟩
  , ⟨245, .notation, "Punctured plane and upper half-plane"⟩
  , ⟨415, .theorem, "Riemann mapping theorem"⟩
  , ⟨422, .definition, "Simple closed curve"⟩
  , ⟨428, .definition, "Simply connected"⟩
  , ⟨489, .definition, "Uniform convergence"⟩
  , ⟨493, .proposition, "Uniform limit of continuous functions"⟩
  , ⟨497, .proposition, "Weierstrass M-test"⟩
  , ⟨501, .proposition, "Radius of convergence"⟩
  , ⟨508, .theorem, "Differentiability of power series"⟩
  , ⟨560, .corollary, "Vanishing power series"⟩
  , ⟨594, .definition, "Branch of logarithm"⟩
  , ⟨615, .proposition, "Principal logarithm"⟩
  , ⟨701, .lemma, "Norm bound for an integral"⟩
  , ⟨729, .definition, "Path"⟩
  , ⟨736, .definition, "Simple path"⟩
  , ⟨741, .definition, "Closed path"⟩
  , ⟨745, .definition, "Contour"⟩
  , ⟨760, .definition, "Complex integration"⟩
  , ⟨847, .definition, "Antiderivative"⟩
  , ⟨852, .theorem, "Fundamental theorem of calculus"⟩
  , ⟨886, .proposition, "Closed integrals and antiderivatives"⟩
  , ⟨977, .definition, "Star-shaped domain"⟩
  , ⟨1004, .definition, "Triangle"⟩
  , ⟨1033, .proposition, "Triangle criterion for an antiderivative"⟩
  , ⟨1051, .theorem, "Cauchy's theorem for a triangle"⟩
  , ⟨1057, .corollary, "Convex Cauchy"⟩
  , ⟨1176, .theorem, "Cauchy integral formula"⟩
  , ⟨1226, .corollary, "Local maximum principle"⟩
  , ⟨1308, .definition, "Elementary deformation"⟩
  , ⟨1340, .theorem, "Liouville's theorem"⟩
  , ⟨1358, .corollary, "Fundamental theorem of algebra"⟩
  , ⟨1383, .theorem, "Taylor's theorem"⟩
  , ⟨1417, .corollary, "Holomorphic functions are smooth"⟩
  , ⟨1427, .corollary, "Cauchy-Riemann converse"⟩
  , ⟨1438, .corollary, "Morera's theorem"⟩
  , ⟨1452, .corollary, "Uniform limit of holomorphic functions"⟩
  , ⟨1476, .definition, "Order of zero"⟩
  , ⟨1492, .lemma, "Principle of isolated zeroes"⟩
  , ⟨1503, .corollary, "Identity theorem"⟩
  , ⟨1522, .definition, "Analytic continuation"⟩
  , ⟨1582, .proposition, "Removal of singularities"⟩
  , ⟨1627, .proposition, "Pole factorization"⟩
  , ⟨1665, .definition, "Isolated singularity"⟩
  , ⟨1669, .definition, "Removable singularity"⟩
  , ⟨1673, .definition, "Pole"⟩
  , ⟨1681, .definition, "Isolated essential singularity"⟩
  , ⟨1703, .definition, "Meromorphic function"⟩
  , ⟨1717, .theorem, "Casorati-Weierstrass theorem"⟩
  , ⟨1730, .theorem, "Picard's theorem"⟩
  , ⟨1744, .theorem, "Laurent series"⟩
  , ⟨1844, .definition, "Principal part"⟩
  , ⟨1864, .lemma, "Uniqueness of Laurent coefficients"⟩
  , ⟨1987, .definition, "Residue"⟩
  , ⟨2042, .lemma, "Continuous polar lift"⟩
  , ⟨2108, .definition, "Winding number"⟩
  , ⟨2120, .lemma, "Integral formula for winding number"⟩
  , ⟨2158, .definition, "Homotopy of closed curves"⟩
  , ⟨2167, .proposition, "Elementary decomposition of a homotopy"⟩
  , ⟨2185, .corollary, "Homotopy invariance of contour integrals"⟩
  , ⟨2195, .definition, "Simply connected domain"⟩
  , ⟨2201, .corollary, "Cauchy's theorem for simply connected domains"⟩
  , ⟨2226, .theorem, "Cauchy's residue theorem"⟩
  , ⟨2324, .lemma, "Residue at a pole"⟩
  , ⟨2512, .lemma, "Small semicircle limit"⟩
  , ⟨2559, .lemma, "Jordan's lemma"⟩
  , ⟨2910, .theorem, "Argument principle"⟩
  , ⟨2959, .corollary, "Rouche's theorem"⟩
  , ⟨3016, .definition, "Local degree"⟩
  , ⟨3021, .lemma, "Local degree as winding number"⟩
  , ⟨3039, .proposition, "Local degree theorem"⟩
  , ⟨3055, .corollary, "Open mapping theorem"⟩
  , ⟨3065, .corollary, "Simply connected domain maps to the disc"⟩ ]

def countKind (k : Kind) : ℕ := (items.filter fun i ↦ i.kind = k).length

theorem item_count : items.length = 81 := by native_decide
theorem line_numbers_unique : (items.map Item.line).Nodup := by native_decide
theorem definition_count : countKind .definition = 34 := by native_decide
theorem theorem_count : countKind .theorem = 12 := by native_decide
theorem proposition_count : countKind .proposition = 11 := by native_decide
theorem corollary_count : countKind .corollary = 14 := by native_decide
theorem lemma_count : countKind .lemma = 9 := by native_decide
theorem notation_count : countKind .notation = 1 := by native_decide
theorem kind_counts_complete :
    countKind .definition + countKind .theorem + countKind .proposition +
      countKind .corollary + countKind .lemma + countKind .notation = items.length := by
  native_decide

end ComplexAnalysisCourse.SourceAudit
