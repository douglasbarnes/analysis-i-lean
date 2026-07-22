import OptimisationCourse.Core

/-! Exact ordered inventory of labelled environments in `IB_E/optimisation.tex`. -/

namespace OptimisationCourse.SourceAudit

inductive Kind where | definition | theorem | lemma
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨36, .definition, "Constrained optimization"⟩
  , ⟨61, .definition, "General and standard form"⟩
  , ⟨111, .definition, "Convex region"⟩
  , ⟨130, .definition, "Convex function"⟩
  , ⟨148, .lemma, "lemma at source line 148"⟩
  , ⟨156, .definition, "Positive-semidefinite"⟩
  , ⟨161, .theorem, "thm at source line 161"⟩
  , ⟨176, .definition, "Lagrangian"⟩
  , ⟨193, .theorem, "Lagrangian sufficiency"⟩
  , ⟨336, .theorem, "thm at source line 336"⟩
  , ⟨371, .theorem, "Weak duality"⟩
  , ⟨393, .definition, "Strong duality"⟩
  , ⟨435, .definition, "Supporting hyperplane"⟩
  , ⟨448, .theorem, "thm at source line 448"⟩
  , ⟨490, .theorem, "Supporting hyperplane theorem"⟩
  , ⟨497, .theorem, "thm at source line 497"⟩
  , ⟨532, .theorem, "thm at source line 532"⟩
  , ⟨584, .definition, "Extreme point"⟩
  , ⟨598, .definition, "Basic solution and basis"⟩
  , ⟨603, .definition, "Non-degenerate solutions"⟩
  , ⟨609, .definition, "Basic feasible solution"⟩
  , ⟨660, .theorem, "thm at source line 660"⟩
  , ⟨668, .theorem, "thm at source line 668"⟩
  , ⟨736, .theorem, "thm at source line 736"⟩
  , ⟨824, .theorem, "thm at source line 824"⟩
  , ⟨1162, .definition, "Bimatrix game"⟩
  , ⟨1198, .definition, "Strategy"⟩
  , ⟨1270, .definition, "Best response and equilibrium"⟩
  , ⟨1282, .theorem, "Nash, 1961"⟩
  , ⟨1289, .definition, "Zero-sum game"⟩
  , ⟨1298, .theorem, "von Neumann, 1928"⟩
  , ⟨1344, .definition, "Value"⟩
  , ⟨1351, .theorem, "thm at source line 1351"⟩
  , ⟨1365, .definition, "Directed graph/network"⟩
  , ⟨1369, .definition, "Degree"⟩
  , ⟨1373, .definition, "Walk"⟩
  , ⟨1377, .definition, "Path"⟩
  , ⟨1381, .definition, "Cycle"⟩
  , ⟨1385, .definition, "Connected graph"⟩
  , ⟨1389, .definition, "Tree"⟩
  , ⟨1393, .definition, "Spanning tree"⟩
  , ⟨1459, .theorem, "thm at source line 1459"⟩
  , ⟨1745, .definition, "Cut"⟩
  , ⟨1775, .theorem, "Max-flow min-cut theorem"⟩ ]

def countKind (k : Kind) : ℕ := (items.filter fun item ↦ item.kind = k).length

theorem item_count : items.length = 44 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide
theorem definition_count : countKind .definition = 26 := by native_decide
theorem theorem_count : countKind .theorem = 17 := by native_decide
theorem lemma_count : countKind .lemma = 1 := by native_decide
theorem kind_counts_complete :
    countKind .definition + countKind .theorem + countKind .lemma = items.length := by native_decide

end OptimisationCourse.SourceAudit

