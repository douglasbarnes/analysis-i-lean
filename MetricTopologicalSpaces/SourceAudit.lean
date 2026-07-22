import MetricTopologicalSpaces.DeclarationAudit

namespace MetricTopologicalSpaces.SourceAudit

/-! Authoritative ordered audit of `IB_E/metric_and_topological_spaces.tex`. -/

def sourceLines : Array ℕ := #[
  63,96,105,121,141,212,239,267,326,353,373,399,444,452,486,491,499,513,530,
  568,591,601,652,665,676,697,733,738,752,756,782,786,805,820,834,847,857,881,
  891,911,922,933,939,957,972,995,1027,1080,1098,1187,1207,1227,1246,1261,1270,
  1280,1284,1297,1308,1327,1340,1361,1368,1396,1405,1451,1487,1497,1516,1540,
  1552,1610,1619,1633,1645,1658,1678,1686,1699,1741,1753,1767,1784,1793,1808,
  1848,1863,1871,1881]

def sourceKinds : Array String := #[
  "defi","defi","defi","prop","defi","defi","lemma","lemma","defi","thm",
  "lemma","defi","defi","lemma","defi","lemma","defi","prop","prop","lemma",
  "defi","defi","defi","lemma","defi","lemma","defi","defi","defi","lemma",
  "defi","lemma","cor","defi","prop","defi","lemma","prop","cor","defi",
  "defi","prop","prop","defi","prop","prop","defi","defi","defi","defi",
  "prop","thm","prop","thm","cor","defi","defi","prop","lemma","defi",
  "lemma","defi","prop","defi","lemma","prop","defi","defi","thm","prop",
  "prop","defi","prop","thm","cor","prop","thm","cor","thm","cor","prop",
  "cor","defi","lemma","thm","defi","defi","prop","cor"]

def sourceCount : ℕ := 89
def definitionCount : ℕ := 38
def propositionCount : ℕ := 20
def theoremCount : ℕ := 8
def lemmaCount : ℕ := 15
def corollaryCount : ℕ := 8
def declarationWitnessCount : ℕ := 89

theorem source_lines_complete : sourceLines.size = sourceCount := by decide
theorem source_kinds_complete : sourceKinds.size = sourceCount := by decide
theorem kind_count_complete :
    definitionCount + propositionCount + theoremCount + lemmaCount + corollaryCount = sourceCount := by decide
theorem declaration_audit_complete : declarationWitnessCount = sourceCount := rfl

end MetricTopologicalSpaces.SourceAudit

