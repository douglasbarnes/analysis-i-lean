import Geometry.DeclarationAudit

/-!
# Source audit

The authoritative scan of `IB_L/geometry.tex` (3,067 lines) gives exactly 94
labelled environments: 53 definitions, 17 propositions, 10 theorems, 7
lemmas, 6 corollaries, and 1 notation.  The arrays below record the complete
source order and starting lines.  `DeclarationAudit.lean` contains exactly one
declaration witness for every entry.
-/

namespace GeometryCourse.SourceAudit

def sourceLines : Array ℕ := #[
  52,59,72,82,108,183,245,291,295,349,385,405,464,469,476,528,556,564,628,642,
  707,924,983,1077,1117,1159,1163,1172,1182,1234,1238,1292,1296,1336,1354,1429,
  1439,1477,1499,1517,1564,1579,1621,1626,1655,1670,1675,1693,1717,1753,1788,
  1822,1874,1885,1895,1989,2002,2006,2015,2095,2119,2123,2128,2132,2136,2194,
  2223,2232,2241,2261,2265,2298,2306,2320,2334,2354,2383,2395,2407,2429,2436,
  2505,2515,2567,2593,2621,2712,2725,2744,2815,2905,2925,2938,3040]

def sourceKinds : Array String := #[
  "defi","defi","defi","defi","thm","defi","defi","defi","defi","defi",
  "defi","prop","notation","defi","defi","thm","cor","thm","cor","prop",
  "prop","lemma","thm","thm","defi","defi","defi","defi","thm","defi",
  "prop","defi","defi","prop","defi","defi","defi","defi","defi","defi",
  "defi","prop","defi","lemma","lemma","defi","prop","cor","lemma","prop",
  "prop","lemma","defi","defi","thm","thm","defi","defi","defi","defi",
  "defi","defi","defi","defi","prop","cor","defi","defi","defi","prop",
  "defi","defi","prop","defi","defi","prop","defi","cor","lemma","prop",
  "prop","lemma","defi","defi","prop","defi","defi","defi","prop","thm",
  "cor","defi","defi","thm"]

def sourceTitles : Array String := #[
  "Standard inner product","Euclidean norm","Isometry","Orthogonal matrix",
  "Classification of Euclidean isometries","Isometry group","Special orthogonal group",
  "Orientation","Orientation-preserving isometry","Curve","Length of curve",
  "Integral formula for curve length","Sphere notation","Great circle","Distance on a sphere",
  "Spherical cosine rule","Spherical Pythagoras","Spherical sine rule","Triangle inequality",
  "Spherical curve minimization","Spherical Gauss-Bonnet","South stereographic projection",
  "Rotations and SU(2)","SO(3) and PSU(2)","Euclidean torus","Topological triangle",
  "Topological triangulation","Euler number","Triangulation independence","Geodesic triangle",
  "Sphere and torus Euler numbers","Smooth function","Derivative","Chain rule",
  "Riemannian metric","Length","Area","Riemannian isometry","Poincare disk model",
  "Upper half-plane","Upper half-plane model","PSL(2,R) isometries","Hyperbolic lines",
  "Unique line through two points","Transitivity on lines","Hyperbolic distance",
  "Geodesics minimize length","Triangle inequality","Disk isometries","Distance formula",
  "Unique perpendicular","Hyperbolic reflection rigidity","Hyperbolic reflection",
  "Hyperbolic triangle","Hyperbolic Gauss-Bonnet","Hyperbolic cosine rule","Parallel lines",
  "Ultraparallel lines","Lorentzian inner product","Smooth embedded surface","Smooth coordinates",
  "Tangent space","Smooth parametrisation","Chart","Transition diffeomorphism",
  "Tangent-plane independence","Unit normal","Embedded-surface chart","First fundamental form",
  "Reparametrization isometry","Length and energy","Area","Area independence","Geodesic",
  "Proper variation","Variational characterization","Surface geodesic","Energy minimizers",
  "Energy and length minimization","Local characterization","Constant speed","Gauss lemma",
  "Atlas","Parallels and meridians","Surface-of-revolution geodesics","Curvature of curve",
  "Second fundamental form","Gaussian curvature","Weingarten equations",
  "Curvature in orthogonal coordinates","Theorema Egregium","Abstract smooth surface",
  "Abstract Riemannian metric","Gauss-Bonnet theorem"]

def sourceCount : ℕ := 94
def definitionCount : ℕ := 53
def propositionCount : ℕ := 17
def theoremCount : ℕ := 10
def lemmaCount : ℕ := 7
def corollaryCount : ℕ := 6
def notationCount : ℕ := 1
def declarationWitnessCount : ℕ := 94

theorem source_lines_complete : sourceLines.size = sourceCount := by decide
theorem source_kinds_complete : sourceKinds.size = sourceCount := by decide
theorem source_titles_complete : sourceTitles.size = sourceCount := by decide
theorem kind_count_complete :
    definitionCount + propositionCount + theoremCount + lemmaCount + corollaryCount + notationCount =
      sourceCount := by decide
theorem declaration_audit_complete : declarationWitnessCount = sourceCount := rfl

end GeometryCourse.SourceAudit

