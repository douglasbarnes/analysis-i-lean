import MarkovChains.Core

/-!
# Source audit: `IB_M/markov_chains.tex`

The list below was obtained directly from the TeX source. It includes every `defi`, `thm`,
`prop`, `lemma`, and `notation` environment and excludes examples, proofs, and unlabelled display
mathematics. Source order and original line numbers are preserved.
-/

namespace MarkovChains.SourceAudit

inductive Kind where
  | definition | theorem | proposition | lemma | notation
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨42, .definition, "Markov chain"⟩
  , ⟨71, .proposition, "Initial distribution and stochastic transition matrix"⟩
  , ⟨91, .theorem, "Factorized finite-dimensional distributions"⟩
  , ⟨126, .theorem, "Extended Markov property"⟩
  , ⟨140, .definition, "n-step transition probability"⟩
  , ⟨156, .theorem, "Chapman-Kolmogorov equation"⟩
  , ⟨163, .notation, "P(n), the n-step transition matrix"⟩
  , ⟨273, .definition, "Leading to and communicate"⟩
  , ⟨279, .proposition, "Communication is an equivalence relation"⟩
  , ⟨293, .definition, "Communicating classes"⟩
  , ⟨300, .definition, "Irreducible chain"⟩
  , ⟨306, .definition, "Closed"⟩
  , ⟨310, .proposition, "Closed iff closed under leading to"⟩
  , ⟨365, .notation, "Probability and expectation conditional on X₀ = i"⟩
  , ⟨378, .definition, "First passage time and probability"⟩
  , ⟨391, .definition, "Recurrent state"⟩
  , ⟨401, .theorem, "Recurrence iff the sum of return probabilities diverges"⟩
  , ⟨415, .theorem, "Renewal generating-function identity"⟩
  , ⟨441, .lemma, "Abel's lemma"⟩
  , ⟨450, .theorem, "Recurrence characterization"⟩
  , ⟨487, .theorem, "Recurrence on a communicating class and closedness"⟩
  , ⟨513, .theorem, "Finite state spaces contain a recurrent state"⟩
  , ⟨541, .theorem, "Pólya's theorem"⟩
  , ⟨655, .definition, "Hitting time"⟩
  , ⟨663, .theorem, "Minimal hitting-probability solution"⟩
  , ⟨720, .theorem, "Minimal mean-hitting-time solution"⟩
  , ⟨860, .definition, "Stopping time"⟩
  , ⟨870, .theorem, "Strong Markov property"⟩
  , ⟨944, .theorem, "Geometric law for the number of returns"⟩
  , ⟨958, .definition, "Mean recurrence time"⟩
  , ⟨969, .definition, "Null and positive state"⟩
  , ⟨975, .definition, "Period"⟩
  , ⟨982, .definition, "Ergodic state"⟩
  , ⟨989, .theorem, "Class properties of period and recurrence"⟩
  , ⟨1015, .proposition, "Irreducible chains hit recurrent states"⟩
  , ⟨1069, .definition, "Invariant distribution"⟩
  , ⟨1080, .theorem, "Invariant distributions and positive recurrence"⟩
  , ⟨1112, .proposition, "Occupation measure between returns"⟩
  , ⟨1180, .theorem, "Invariant distribution iff positive recurrence"⟩
  , ⟨1292, .theorem, "Convergence to equilibrium"⟩
  , ⟨1415, .theorem, "Time reversal"⟩
  , ⟨1459, .definition, "Reversible chain"⟩
  , ⟨1476, .proposition, "Detailed balance implies invariance and reversibility"⟩ ]

theorem item_count : items.length = 43 := by native_decide

theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide

def countKind (k : Kind) : ℕ := (items.filter fun x ↦ x.kind = k).length

theorem definition_count : countKind .definition = 16 := by native_decide
theorem theorem_count : countKind .theorem = 18 := by native_decide
theorem proposition_count : countKind .proposition = 6 := by native_decide
theorem lemma_count : countKind .lemma = 1 := by native_decide
theorem notation_count : countKind .notation = 2 := by native_decide

theorem kind_counts_complete :
    countKind .definition + countKind .theorem + countKind .proposition +
      countKind .lemma + countKind .notation = items.length := by native_decide

end MarkovChains.SourceAudit
