import StatisticsCourse.Core

/-! Exact ordered inventory of labelled environments in `IB_L/statistics.tex`. -/

namespace StatisticsCourse.SourceAudit

inductive Kind where | definition | theorem | proposition | lemma | notation
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨48, .definition, "Statistic"⟩
  , ⟨71, .definition, "Bias"⟩
  , ⟨92, .definition, "Mean squared error"⟩
  , ⟨178, .definition, "Sufficient statistic"⟩
  , ⟨183, .theorem, "The factorization criterion"⟩
  , ⟨244, .definition, "Minimal sufficiency"⟩
  , ⟨249, .theorem, "thm at source line 249"⟩
  , ⟨288, .theorem, "Rao-Blackwell Theorem"⟩
  , ⟨346, .definition, "Likelihood"⟩
  , ⟨425, .definition, "defi at source line 425"⟩
  , ⟨539, .definition, "Prior and posterior distribution"⟩
  , ⟨640, .definition, "Bayes estimator"⟩
  , ⟨722, .definition, "Simple and composite hypotheses"⟩
  , ⟨727, .definition, "Critical region"⟩
  , ⟨732, .definition, "Type I and II error"⟩
  , ⟨739, .definition, "Size and power"⟩
  , ⟨751, .definition, "Likelihood"⟩
  , ⟨768, .lemma, "Neyman-Pearson lemma"⟩
  , ⟨858, .definition, "$p$-value"⟩
  , ⟨866, .definition, "Power function"⟩
  , ⟨874, .definition, "Size"⟩
  , ⟨892, .definition, "Uniformly most powerful test"⟩
  , ⟨924, .definition, "Likelihood of a composite hypothesis"⟩
  , ⟨978, .theorem, "Generalized likelihood ratio theorem"⟩
  , ⟨1085, .definition, "Contingency table"⟩
  , ⟨1271, .definition, "Acceptance region"⟩
  , ⟨1276, .theorem, "Duality of hypothesis tests and confidence intervals"⟩
  , ⟨1346, .definition, "Multivariate normal distribution"⟩
  , ⟨1371, .proposition, "prop at source line 1371"⟩
  , ⟨1389, .proposition, "prop at source line 1389"⟩
  , ⟨1433, .proposition, "prop at source line 1433"⟩
  , ⟨1444, .theorem, "Joint distribution of $\\bar X$ and $S_{XX}$"⟩
  , ⟨1495, .definition, "$t$-distribution"⟩
  , ⟨1509, .proposition, "prop at source line 1509"⟩
  , ⟨1519, .notation, "notation at source line 1519"⟩
  , ⟨1670, .definition, "Least squares estimator"⟩
  , ⟨1695, .proposition, "prop at source line 1695"⟩
  , ⟨1794, .theorem, "Gauss Markov theorem"⟩
  , ⟨1841, .definition, "Fitted values and residuals"⟩
  , ⟨1970, .proposition, "prop at source line 1970"⟩
  , ⟨1994, .lemma, "lemma at source line 1994"⟩
  , ⟨2026, .theorem, "thm at source line 2026"⟩
  , ⟨2110, .definition, "$F$ distribution"⟩
  , ⟨2116, .proposition, "prop at source line 2116"⟩
  , ⟨2292, .lemma, "lemma at source line 2292"⟩ ]

def countKind (k : Kind) : ℕ := (items.filter fun item ↦ item.kind = k).length

theorem item_count : items.length = 45 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide
theorem definition_count : countKind .definition = 26 := by native_decide
theorem theorem_count : countKind .theorem = 8 := by native_decide
theorem proposition_count : countKind .proposition = 7 := by native_decide
theorem lemma_count : countKind .lemma = 3 := by native_decide
theorem notation_count : countKind .notation = 1 := by native_decide
theorem kind_counts_complete :
    countKind .definition + countKind .theorem + countKind .proposition +
      countKind .lemma + countKind .notation = items.length := by native_decide

end StatisticsCourse.SourceAudit
