import VariationalPrinciplesCourse.Core

/-! Exact ordered source inventory for `IB_E/variational_principles.tex`. -/

namespace VariationalPrinciplesCourse.SourceAudit

inductive Kind where
  | definition | theorem | lemma | corollary | law
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨62, .definition, "Stationary points"⟩
  , ⟨74, .definition, "Hessian matrix"⟩
  , ⟨134, .definition, "Convex set"⟩
  , ⟨153, .definition, "Convex function"⟩
  , ⟨218, .corollary, "Stationary point of a convex function"⟩
  , ⟨313, .definition, "Legendre transform"⟩
  , ⟨325, .lemma, "Convexity of the Legendre transform"⟩
  , ⟨379, .theorem, "Legendre transform involutivity"⟩
  , ⟨573, .definition, "Functional"⟩
  , ⟨605, .definition, "Functional derivative"⟩
  , ⟨613, .definition, "Euler-Lagrange equation"⟩
  , ⟨1005, .law, "Hamilton's principle"⟩
  , ⟨1100, .definition, "Hamiltonian"⟩
  , ⟨1156, .definition, "Symmetry"⟩
  , ⟨1190, .theorem, "Noether's theorem"⟩ ]

theorem item_count : items.length = 15 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide

def countKind (k : Kind) : ℕ := (items.filter fun x ↦ x.kind = k).length

theorem definition_count : countKind .definition = 10 := by native_decide
theorem theorem_count : countKind .theorem = 2 := by native_decide
theorem lemma_count : countKind .lemma = 1 := by native_decide
theorem corollary_count : countKind .corollary = 1 := by native_decide
theorem law_count : countKind .law = 1 := by native_decide

theorem kind_counts_complete :
    countKind .definition + countKind .theorem + countKind .lemma +
      countKind .corollary + countKind .law = items.length := by
  native_decide

end VariationalPrinciplesCourse.SourceAudit
