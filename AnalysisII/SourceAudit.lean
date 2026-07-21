/-- Machine-readable inventory of the 68 theorem-like environments in the supplied Analysis II notes. -/
namespace AnalysisII

inductive CoverageStatus where
  | mathlib | reformulated | localProof | duplicate
  deriving Repr, DecidableEq

structure AuditEntry where
  id : Nat
  lineStart : Nat
  lineEnd : Nat
  kind : String
  status : CoverageStatus
  deriving Repr

def theoremAudit : Array AuditEntry := #[
  { id := 1, lineStart := 200, lineEnd := 202, kind := "thm", status := .mathlib },
  { id := 2, lineStart := 225, lineEnd := 229, kind := "thm", status := .mathlib },
  { id := 3, lineStart := 247, lineEnd := 252, kind := "thm", status := .reformulated },
  { id := 4, lineStart := 298, lineEnd := 305, kind := "thm", status := .mathlib },
  { id := 5, lineStart := 389, lineEnd := 394, kind := "prop", status := .mathlib },
  { id := 6, lineStart := 428, lineEnd := 430, kind := "prop", status := .mathlib },
  { id := 7, lineStart := 465, lineEnd := 471, kind := "thm", status := .mathlib },
  { id := 8, lineStart := 489, lineEnd := 499, kind := "thm", status := .reformulated },
  { id := 9, lineStart := 519, lineEnd := 529, kind := "thm", status := .reformulated },
  { id := 10, lineStart := 574, lineEnd := 576, kind := "thm", status := .duplicate },
  { id := 11, lineStart := 679, lineEnd := 684, kind := "thm", status := .reformulated },
  { id := 12, lineStart := 687, lineEnd := 689, kind := "thm", status := .reformulated },
  { id := 13, lineStart := 742, lineEnd := 744, kind := "cor", status := .duplicate },
  { id := 14, lineStart := 746, lineEnd := 748, kind := "thm", status := .reformulated },
  { id := 15, lineStart := 782, lineEnd := 791, kind := "prop", status := .reformulated },
  { id := 16, lineStart := 817, lineEnd := 823, kind := "thm", status := .mathlib },
  { id := 17, lineStart := 923, lineEnd := 925, kind := "thm", status := .reformulated },
  { id := 18, lineStart := 1047, lineEnd := 1052, kind := "lemma", status := .mathlib },
  { id := 19, lineStart := 1173, lineEnd := 1179, kind := "prop", status := .reformulated },
  { id := 20, lineStart := 1194, lineEnd := 1201, kind := "prop", status := .mathlib },
  { id := 21, lineStart := 1211, lineEnd := 1213, kind := "prop", status := .mathlib },
  { id := 22, lineStart := 1232, lineEnd := 1234, kind := "thm", status := .mathlib },
  { id := 23, lineStart := 1287, lineEnd := 1289, kind := "prop", status := .mathlib },
  { id := 24, lineStart := 1298, lineEnd := 1300, kind := "prop", status := .mathlib },
  { id := 25, lineStart := 1309, lineEnd := 1311, kind := "prop", status := .mathlib },
  { id := 26, lineStart := 1320, lineEnd := 1322, kind := "prop", status := .mathlib },
  { id := 27, lineStart := 1328, lineEnd := 1330, kind := "thm", status := .mathlib },
  { id := 28, lineStart := 1365, lineEnd := 1367, kind := "prop", status := .mathlib },
  { id := 29, lineStart := 1395, lineEnd := 1397, kind := "prop", status := .mathlib },
  { id := 30, lineStart := 1407, lineEnd := 1413, kind := "lemma", status := .mathlib },
  { id := 31, lineStart := 1422, lineEnd := 1424, kind := "prop", status := .duplicate },
  { id := 32, lineStart := 1440, lineEnd := 1446, kind := "thm", status := .mathlib },
  { id := 33, lineStart := 1474, lineEnd := 1476, kind := "thm", status := .mathlib },
  { id := 34, lineStart := 1500, lineEnd := 1510, kind := "thm", status := .mathlib },
  { id := 35, lineStart := 1521, lineEnd := 1527, kind := "lemma", status := .reformulated },
  { id := 36, lineStart := 1542, lineEnd := 1544, kind := "thm", status := .reformulated },
  { id := 37, lineStart := 1583, lineEnd := 1589, kind := "cor", status := .mathlib },
  { id := 38, lineStart := 1597, lineEnd := 1599, kind := "cor", status := .mathlib },
  { id := 39, lineStart := 1722, lineEnd := 1724, kind := "prop", status := .mathlib },
  { id := 40, lineStart := 1770, lineEnd := 1772, kind := "prop", status := .mathlib },
  { id := 41, lineStart := 1780, lineEnd := 1787, kind := "thm", status := .mathlib },
  { id := 42, lineStart := 1807, lineEnd := 1809, kind := "prop", status := .mathlib },
  { id := 43, lineStart := 1816, lineEnd := 1823, kind := "thm", status := .mathlib },
  { id := 44, lineStart := 1829, lineEnd := 1831, kind := "prop", status := .mathlib },
  { id := 45, lineStart := 1848, lineEnd := 1854, kind := "prop", status := .mathlib },
  { id := 46, lineStart := 1925, lineEnd := 1931, kind := "thm", status := .mathlib },
  { id := 47, lineStart := 1951, lineEnd := 1953, kind := "thm", status := .mathlib },
  { id := 48, lineStart := 1978, lineEnd := 1980, kind := "thm", status := .mathlib },
  { id := 49, lineStart := 2070, lineEnd := 2072, kind := "thm", status := .mathlib },
  { id := 50, lineStart := 2082, lineEnd := 2089, kind := "thm", status := .mathlib },
  { id := 51, lineStart := 2112, lineEnd := 2114, kind := "cor", status := .mathlib },
  { id := 52, lineStart := 2131, lineEnd := 2135, kind := "thm", status := .mathlib },
  { id := 53, lineStart := 2220, lineEnd := 2238, kind := "thm", status := .reformulated },
  { id := 54, lineStart := 2450, lineEnd := 2452, kind := "prop", status := .mathlib },
  { id := 55, lineStart := 2560, lineEnd := 2591, kind := "prop", status := .mathlib },
  { id := 56, lineStart := 2724, lineEnd := 2731, kind := "thm", status := .reformulated },
  { id := 57, lineStart := 2805, lineEnd := 2819, kind := "prop", status := .mathlib },
  { id := 58, lineStart := 2844, lineEnd := 2849, kind := "prop", status := .reformulated },
  { id := 59, lineStart := 2865, lineEnd := 2870, kind := "thm", status := .mathlib },
  { id := 60, lineStart := 2906, lineEnd := 2911, kind := "thm", status := .mathlib },
  { id := 61, lineStart := 2942, lineEnd := 2948, kind := "thm", status := .mathlib },
  { id := 62, lineStart := 2977, lineEnd := 2979, kind := "cor", status := .mathlib },
  { id := 63, lineStart := 2998, lineEnd := 3000, kind := "thm", status := .mathlib },
  { id := 64, lineStart := 3027, lineEnd := 3029, kind := "prop", status := .reformulated },
  { id := 65, lineStart := 3074, lineEnd := 3080, kind := "thm", status := .reformulated },
  { id := 66, lineStart := 3313, lineEnd := 3320, kind := "thm", status := .mathlib },
  { id := 67, lineStart := 3365, lineEnd := 3371, kind := "prop", status := .reformulated },
  { id := 68, lineStart := 3379, lineEnd := 3385, kind := "thm", status := .reformulated }
]

end AnalysisII
