import Mathlib

/-! Machine-checked source inventory for `IB_M/linear_algebra.tex` (4,652 lines). -/

namespace Cambridge.LinearAlgebraCourse.SourceAudit

inductive EnvironmentKind where
  | definition | lemma | theorem_ | proposition | corollary | notation
  deriving DecidableEq, Repr

def sourceLines : List Nat :=
  [46, 83, 97, 103, 126, 133, 148, 162, 195, 199, 209, 213, 230, 250, 284, 292,
   342, 384, 393, 405, 447, 484, 500, 514, 525, 538, 580, 586, 604, 643, 676, 688,
   733, 765, 798, 804, 829, 856, 860, 876, 965, 980, 1026, 1056, 1066, 1079, 1090,
   1118, 1173, 1233, 1252, 1265, 1283, 1316, 1333, 1367, 1371, 1391, 1432, 1489,
   1519, 1533, 1560, 1588, 1623, 1641, 1677, 1704, 1720, 1724, 1730, 1760, 1781,
   1796, 1831, 1847, 1878, 1899, 1907, 1943, 1959, 1971, 1976, 2003, 2007, 2048,
   2053, 2079, 2112, 2132, 2137, 2152, 2167, 2175, 2203, 2211, 2222, 2233, 2243,
   2281, 2286, 2311, 2324, 2330, 2338, 2357, 2372, 2376, 2384, 2389, 2402, 2410,
   2473, 2489, 2521, 2531, 2562, 2597, 2611, 2681, 2877, 2924, 2951, 2972, 2993,
   3032, 3153, 3201, 3255, 3397, 3414, 3436, 3452, 3464, 3499, 3526, 3706, 3738,
   3748, 3806, 3839, 3888, 3893, 3906, 3924, 3937, 3950, 3966, 3987, 4006, 4028,
   4064, 4092, 4112, 4116, 4124, 4144, 4167, 4206, 4216, 4228, 4236, 4263, 4274,
   4332, 4379, 4384, 4397, 4410, 4430, 4438, 4446, 4462, 4471, 4475, 4479, 4486,
   4499, 4548, 4572, 4576, 4584, 4600, 4608, 4613, 4627]

open EnvironmentKind

def sourceKinds : List EnvironmentKind :=
  [notation, definition, proposition, definition, definition, proposition, definition,
   definition, definition, definition, definition, definition, lemma, proposition, theorem_,
   corollary, corollary, definition, lemma, proposition, proposition, definition, definition,
   definition, definition, definition, definition, lemma, definition, proposition, corollary,
   proposition, proposition, corollary, definition, proposition, theorem_, definition, corollary,
   proposition, corollary, lemma, theorem_, definition, corollary, definition, theorem_, definition,
   proposition, definition, lemma, corollary, proposition, definition, proposition, definition,
   proposition, proposition, lemma, lemma, lemma, lemma, proposition, definition, definition,
   proposition, lemma, definition, definition, definition, lemma, definition, lemma, lemma,
   definition, lemma, lemma, corollary, theorem_, theorem_, corollary, definition, theorem_, notation,
   lemma, definition, theorem_, lemma, corollary, definition, lemma, definition, definition, lemma,
   definition, definition, definition, lemma, lemma, definition, theorem_, definition, definition,
   lemma, lemma, definition, lemma, corollary, corollary, theorem_, notation, theorem_, definition,
   lemma, theorem_, theorem_, theorem_, definition, lemma, theorem_, lemma, definition, lemma, lemma,
   definition, theorem_, theorem_, theorem_, definition, definition, lemma, lemma, definition,
   definition, proposition, theorem_, theorem_, corollary, theorem_, definition, theorem_, definition,
   corollary, definition, definition, definition, lemma, proposition, lemma, theorem_, definition,
   theorem_, corollary, definition, definition, definition, lemma, theorem_, corollary, definition,
   definition, proposition, definition, proposition, lemma, definition, definition, definition, lemma,
   corollary, definition, proposition, definition, lemma, corollary, definition, proposition, lemma,
   theorem_, corollary, corollary, corollary, corollary, corollary, proposition, theorem_]

def sourceInventory : List (Nat × EnvironmentKind) := sourceLines.zip sourceKinds

theorem authoritative_environment_count : sourceInventory.length = 186 := by native_decide
theorem line_and_kind_inventory_complete :
    sourceLines.length = sourceKinds.length := by native_decide
theorem source_lines_strictly_ordered : sourceLines.Pairwise (· < ·) := by native_decide
theorem definition_count : (sourceKinds.filter (· = definition)).length = 70 := by native_decide
theorem lemma_count : (sourceKinds.filter (· = lemma)).length = 38 := by native_decide
theorem theorem_count : (sourceKinds.filter (· = theorem_)).length = 27 := by native_decide
theorem proposition_count : (sourceKinds.filter (· = proposition)).length = 24 := by native_decide
theorem corollary_count : (sourceKinds.filter (· = corollary)).length = 24 := by native_decide
theorem notation_count : (sourceKinds.filter (· = notation)).length = 3 := by native_decide
theorem kind_partition_complete : 70 + 38 + 27 + 24 + 24 + 3 = 186 := by decide

end Cambridge.LinearAlgebraCourse.SourceAudit
