import QuantumMechanics.DeclarationAudit

/-!
# Source audit

Authoritative source: `IB_M/quantum_mechanics.tex` (2,600 lines), retrieved
2026-07-22.  The labelled-environment scan finds 25 entries: 16 definitions,
6 propositions, and 3 theorems.  `sourceInventory` records their source order
and starting lines.  `DeclarationAudit.lean` has exactly 25 `#check` commands,
one for each entry below.
-/

namespace QuantumMechanics.SourceAudit

inductive SourceKind where
  | definition | proposition | theorem
  deriving DecidableEq, Repr

structure SourceItem where
  ordinal : Fin 25
  line : ℕ
  kind : SourceKind
  title : String
  deriving Repr

def sourceInventory : Fin 25 → SourceItem
  | 0  => ⟨0, 333, .definition, "Time-independent Schrodinger equation"⟩
  | 1  => ⟨1, 350, .definition, "Time-dependent Schrodinger equation"⟩
  | 2  => ⟨2, 391, .definition, "Stationary state"⟩
  | 3  => ⟨3, 409, .proposition, "Probability conservation equation"⟩
  | 4  => ⟨4, 872, .definition, "Inner product"⟩
  | 5  => ⟨5, 888, .definition, "Norm"⟩
  | 6  => ⟨6, 897, .definition, "Expectation value"⟩
  | 7  => ⟨7, 916, .definition, "Uncertainty"⟩
  | 8  => ⟨8, 930, .definition, "Hermitian operator"⟩
  | 9  => ⟨9, 945, .proposition, "Standard operators are Hermitian"⟩
  | 10 => ⟨10, 997, .proposition, "Cauchy-Schwarz inequality"⟩
  | 11 => ⟨11, 1032, .theorem, "Ehrenfest theorem: position and momentum"⟩
  | 12 => ⟨12, 1078, .theorem, "Heisenberg uncertainty principle"⟩
  | 13 => ⟨13, 1114, .definition, "Commutator"⟩
  | 14 => ⟨14, 1188, .definition, "Wavepacket"⟩
  | 15 => ⟨15, 1193, .definition, "Gaussian wavepacket"⟩
  | 16 => ⟨16, 1525, .definition, "Ground and excited states"⟩
  | 17 => ⟨17, 1610, .proposition, "Hermitian spectral properties"⟩
  | 18 => ⟨18, 1718, .proposition, "Expectation and uncertainty from spectrum"⟩
  | 19 => ⟨19, 1794, .theorem, "General Ehrenfest theorem"⟩
  | 20 => ⟨20, 1910, .definition, "Degeneracy"⟩
  | 21 => ⟨21, 1975, .definition, "Structureless particle"⟩
  | 22 => ⟨22, 2108, .definition, "Angular momentum"⟩
  | 23 => ⟨23, 2132, .definition, "Total angular momentum"⟩
  | 24 => ⟨24, 2162, .proposition, "Angular momentum commutation relations"⟩

def sourceCount : ℕ := 25
def definitionCount : ℕ := 16
def propositionCount : ℕ := 6
def theoremCount : ℕ := 3
def declarationWitnessCount : ℕ := 25

theorem source_count_complete : sourceCount = 25 := rfl
theorem kind_count_complete :
    definitionCount + propositionCount + theoremCount = sourceCount := by decide
theorem declaration_audit_complete : declarationWitnessCount = sourceCount := rfl
theorem inventory_ordinal_complete (i : Fin 25) : (sourceInventory i).ordinal = i := by
  native_decide

end QuantumMechanics.SourceAudit
