import AdvancedProbability.Core

/-!
# Source audit: `III_M/advanced_probability.tex`

Every labelled `defi`, `thm`, `prop`, `lemma`, `cor`, and `notation` environment is listed in
source order.  The `line` field records the corresponding line in the normalized text extraction
of the source notes, allowing the inventory to be regenerated independently of Lean declaration
names.
-/

namespace AdvancedProbability.SourceAudit

inductive Kind where
  | definition | theorem | proposition | lemma | corollary | notation
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨138, .definition, "Sigma-algebra"⟩
  , ⟨144, .definition, "Measurable space"⟩
  , ⟨145, .definition, "Borel sigma-algebra"⟩
  , ⟨149, .definition, "Measure"⟩
  , ⟨159, .definition, "Measure space"⟩
  , ⟨161, .definition, "Measurable function"⟩
  , ⟨164, .notation, "Measurable real and positive functions"⟩
  , ⟨169, .theorem, "Existence and uniqueness of the non-negative integral"⟩
  , ⟨189, .definition, "Simple function"⟩
  , ⟨214, .definition, "Almost everywhere"⟩
  , ⟨223, .lemma, "Fatou lemma"⟩
  , ⟨239, .definition, "Integrable function"⟩
  , ⟨248, .theorem, "Dominated convergence theorem"⟩
  , ⟨254, .definition, "Product sigma-algebra"⟩
  , ⟨257, .theorem, "Existence and uniqueness of product measure"⟩
  , ⟨264, .theorem, "Fubini-Tonelli theorem"⟩
  , ⟨340, .lemma, "Conditional expectation characterization"⟩
  , ⟨380, .theorem, "Existence and uniqueness of conditional expectation"⟩
  , ⟨437, .lemma, "Doob-Dynkin factorization"⟩
  , ⟨515, .proposition, "Basic properties of conditional expectation"⟩
  , ⟨602, .lemma, "Uniform integrability of conditional expectations"⟩
  , ⟨651, .definition, "Filtration"⟩
  , ⟨654, .definition, "Stochastic process in discrete time"⟩
  , ⟨658, .definition, "Natural filtration"⟩
  , ⟨662, .definition, "Adapted process"⟩
  , ⟨664, .definition, "Integrable process"⟩
  , ⟨667, .definition, "Martingale, submartingale and supermartingale"⟩
  , ⟨700, .definition, "Stopping time"⟩
  , ⟨727, .definition, "Stopped random variable"⟩
  , ⟨735, .definition, "Stopped process"⟩
  , ⟨750, .definition, "Sigma-field at a stopping time"⟩
  , ⟨759, .proposition, "Stopping-time calculus"⟩
  , ⟨775, .theorem, "Optional stopping theorem"⟩
  , ⟨809, .theorem, "Characterizations of supermartingales"⟩
  , ⟨887, .theorem, "Almost sure martingale convergence theorem"⟩
  , ⟨894, .definition, "Upcrossing"⟩
  , ⟨903, .lemma, "Convergence criterion by upcrossings"⟩
  , ⟨918, .lemma, "Doob upcrossing lemma"⟩
  , ⟨1001, .lemma, "Maximal inequality"⟩
  , ⟨1032, .lemma, "Doob Lp inequality"⟩
  , ⟨1075, .theorem, "Lp martingale convergence theorem"⟩
  , ⟨1138, .theorem, "L1 convergence of martingales"⟩
  , ⟨1167, .theorem, "Uniformly integrable optional stopping"⟩
  , ⟨1207, .definition, "Backwards filtration"⟩
  , ⟨1213, .theorem, "Backwards martingale convergence"⟩
  , ⟨1240, .theorem, "Kolmogorov zero-one law"⟩
  , ⟨1257, .theorem, "Strong law of large numbers"⟩
  , ⟨1318, .theorem, "Radon-Nikodym theorem"⟩
  , ⟨1426, .definition, "Transition matrix"⟩
  , ⟨1428, .definition, "Markov chain"⟩
  , ⟨1433, .definition, "Harmonic function for a transition matrix"⟩
  , ⟨1446, .proposition, "Bounded harmonic functions yield martingales"⟩
  , ⟨1470, .definition, "Continuous-time stochastic process"⟩
  , ⟨1493, .definition, "Cadlag function"⟩
  , ⟨1500, .definition, "Continuous or cadlag stochastic process"⟩
  , ⟨1503, .notation, "Continuous path space"⟩
  , ⟨1519, .definition, "Finite-dimensional distribution"⟩
  , ⟨1534, .theorem, "Kolmogorov continuity criterion"⟩
  , ⟨1549, .definition, "Dyadic numbers"⟩
  , ⟨1636, .definition, "Continuous-time filtration"⟩
  , ⟨1645, .definition, "Continuous-time stopping time"⟩
  , ⟨1648, .proposition, "Continuous stopping-time calculus"⟩
  , ⟨1659, .lemma, "Measurability at a stopping time"⟩
  , ⟨1682, .definition, "Hitting time"⟩
  , ⟨1713, .proposition, "Closed-set hitting times"⟩
  , ⟨1721, .definition, "Right-continuous filtration"⟩
  , ⟨1731, .definition, "Usual conditions"⟩
  , ⟨1733, .proposition, "Open-set hitting times"⟩
  , ⟨1747, .definition, "Continuous-time martingale"⟩
  , ⟨1768, .theorem, "Continuous optional stopping theorem"⟩
  , ⟨1800, .theorem, "Continuous supermartingale convergence"⟩
  , ⟨1838, .lemma, "Continuous maximal inequality"⟩
  , ⟨1843, .lemma, "Continuous Doob Lp inequality"⟩
  , ⟨1848, .definition, "Version of a stochastic process"⟩
  , ⟨1859, .theorem, "Regularization of martingales"⟩
  , ⟨1891, .theorem, "Lp convergence of continuous martingales"⟩
  , ⟨1897, .theorem, "L1 convergence of continuous martingales"⟩
  , ⟨1904, .theorem, "Continuous uniformly integrable optional stopping"⟩
  , ⟨1921, .definition, "Law of a random variable"⟩
  , ⟨1937, .definition, "Weak convergence"⟩
  , ⟨1962, .proposition, "Portmanteau theorem"⟩
  , ⟨2047, .definition, "Tight probability measures"⟩
  , ⟨2054, .theorem, "Prokhorov theorem"⟩
  , ⟨2101, .definition, "Characteristic function"⟩
  , ⟨2108, .proposition, "Characteristic functions determine laws"⟩
  , ⟨2109, .theorem, "Levy convergence theorem"⟩
  , ⟨2114, .theorem, "Levy continuity theorem"⟩
  , ⟨2118, .lemma, "Characteristic-function tail bound"⟩
  , ⟨2193, .definition, "Brownian motion"⟩
  , ⟨2203, .theorem, "Wiener existence theorem"⟩
  , ⟨2306, .lemma, "Brownian motion is a Gaussian process"⟩
  , ⟨2317, .proposition, "Brownian invariance properties"⟩
  , ⟨2353, .theorem, "Future increments are independent of the right filtration"⟩
  , ⟨2370, .theorem, "Blumenthal zero-one law"⟩
  , ⟨2374, .proposition, "Brownian sample-path properties"⟩
  , ⟨2403, .theorem, "Strong Markov property"⟩
  , ⟨2465, .theorem, "Reflection principle"⟩
  , ⟨2499, .corollary, "Reflection hitting identity"⟩
  , ⟨2510, .corollary, "Running maximum law"⟩
  , ⟨2518, .proposition, "Brownian first-passage distribution"⟩
  , ⟨2553, .definition, "Domain"⟩
  , ⟨2554, .definition, "Harmonic function"⟩
  , ⟨2563, .lemma, "Mean-value characterization of harmonic functions"⟩
  , ⟨2580, .theorem, "Harmonic functions of Brownian motion are martingales"⟩
  , ⟨2593, .lemma, "Conditional expectation with an independent summand"⟩
  , ⟨2615, .theorem, "Second-order Brownian martingale"⟩
  , ⟨2669, .definition, "Maximum principle"⟩
  , ⟨2677, .corollary, "Uniqueness for the Dirichlet problem"⟩
  , ⟨2683, .definition, "Poincare cone condition"⟩
  , ⟨2693, .lemma, "Cone hitting estimate"⟩
  , ⟨2718, .theorem, "Brownian solution of the Dirichlet problem"⟩
  , ⟨2760, .theorem, "Brownian recurrence and transience"⟩
  , ⟨2838, .theorem, "Donsker invariance principle"⟩
  , ⟨2854, .theorem, "Skorokhod embedding theorem"⟩
  , ⟨2885, .lemma, "Two-sided Brownian hitting formula"⟩
  , ⟨3098, .lemma, "Fekete lemma"⟩
  , ⟨3112, .theorem, "Cramer theorem"⟩ ]

theorem item_count : items.length = 117 := by native_decide

theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide

def countKind (k : Kind) : ℕ := (items.filter fun x ↦ x.kind = k).length

theorem definition_count : countKind .definition = 46 := by native_decide
theorem theorem_count : countKind .theorem = 37 := by native_decide
theorem proposition_count : countKind .proposition = 11 := by native_decide
theorem lemma_count : countKind .lemma = 18 := by native_decide
theorem corollary_count : countKind .corollary = 3 := by native_decide
theorem notation_count : countKind .notation = 2 := by native_decide

theorem kind_counts_complete :
    countKind .definition + countKind .theorem + countKind .proposition +
      countKind .lemma + countKind .corollary + countKind .notation = items.length := by
  native_decide

end AdvancedProbability.SourceAudit
