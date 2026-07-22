import Mathlib
/-!
# Linear Analysis source audit

Ordered inventory of every definition, notation, proposition, theorem, lemma, and corollary in
`II_M/linear_analysis.tex` (J. W. Luk, Michaelmas 2015).  Line numbers refer to the source TeX.
-/

namespace Cambridge.LinearAnalysis.SourceAudit

inductive Kind where
  | definition | notation | proposition | theorem | lemma | corollary
  deriving DecidableEq, Repr

structure Item where
  line : Nat
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item := [
  ⟨50, .definition, "Normed vector space"⟩, -- 1
  ⟨82, .proposition, "Addition and scalar multiplication are continuous"⟩, -- 2
  ⟨92, .definition, "Topological vector space"⟩, -- 3
  ⟨101, .definition, "Absolute convexity"⟩, -- 4
  ⟨105, .proposition, "Norm balls are absolutely convex"⟩, -- 5
  ⟨113, .definition, "Bounded subset"⟩, -- 6
  ⟨122, .proposition, "Normability criterion"⟩, -- 7
  ⟨163, .definition, "Banach space"⟩, -- 8
  ⟨245, .definition, "Bounded linear map"⟩, -- 9
  ⟨252, .proposition, "Linear map: continuity, continuity at zero, and boundedness"⟩, -- 10
  ⟨271, .definition, "Operator norm"⟩, -- 11
  ⟨283, .definition, "Dual space"⟩, -- 12
  ⟨297, .proposition, "The dual space is Banach"⟩, -- 13
  ⟨350, .definition, "Adjoint on the continuous dual"⟩, -- 14
  ⟨362, .proposition, "The adjoint is bounded"⟩, -- 15
  ⟨380, .definition, "Double dual"⟩, -- 16
  ⟨390, .proposition, "Canonical bidual embedding is bounded"⟩, -- 17
  ⟨408, .definition, "Isomorphism of normed spaces"⟩, -- 18
  ⟨484, .proposition, "Finite-dimensional norms are equivalent to the ℓ¹ norm"⟩, -- 19
  ⟨488, .corollary, "All norms on a finite-dimensional vector space are equivalent"⟩, -- 20
  ⟨558, .proposition, "The closed unit ball is compact in finite dimension"⟩, -- 21
  ⟨570, .proposition, "Finite-dimensional normed spaces are Banach"⟩, -- 22
  ⟨578, .proposition, "Linear maps from finite-dimensional normed spaces are bounded"⟩, -- 23
  ⟨612, .proposition, "Compact unit ball implies finite dimension"⟩, -- 24
  ⟨669, .proposition, "Codimension-one Hahn–Banach extension"⟩, -- 25
  ⟨745, .definition, "Partial order"⟩, -- 26
  ⟨754, .definition, "Total order"⟩, -- 27
  ⟨758, .definition, "Upper bound"⟩, -- 28
  ⟨762, .definition, "Maximal element"⟩, -- 29
  ⟨767, .lemma, "Zorn's lemma"⟩, -- 30
  ⟨778, .theorem, "Hahn–Banach theorem"⟩, -- 31
  ⟨814, .corollary, "Norm-preserving Hahn–Banach extension"⟩, -- 32
  ⟨835, .proposition, "Existence of a norming functional"⟩, -- 33
  ⟨843, .corollary, "The dual detects zero"⟩, -- 34
  ⟨847, .corollary, "The dual separates points"⟩, -- 35
  ⟨851, .corollary, "A nontrivial space has nontrivial dual"⟩, -- 36
  ⟨857, .proposition, "The canonical bidual embedding is an isometry"⟩, -- 37
  ⟨881, .definition, "Reflexive space"⟩, -- 38
  ⟨903, .proposition, "Norm of the adjoint equals norm of the operator"⟩, -- 39
  ⟨942, .definition, "Nowhere dense set"⟩, -- 40
  ⟨947, .definition, "Meagre and residual sets"⟩, -- 41
  ⟨955, .theorem, "Baire category theorem"⟩, -- 42
  ⟨981, .proposition, "Existence of irrational numbers"⟩, -- 43
  ⟨997, .proposition, "Finitely supported ℓ¹ sequences form an incomplete space"⟩, -- 44
  ⟨1030, .proposition, "Existence of a nowhere differentiable continuous function"⟩, -- 45
  ⟨1056, .theorem, "Banach–Steinhaus theorem"⟩, -- 46
  ⟨1131, .theorem, "Osgood theorem"⟩, -- 47
  ⟨1146, .theorem, "Open mapping theorem"⟩, -- 48
  ⟨1278, .theorem, "Inverse mapping theorem"⟩, -- 49
  ⟨1286, .theorem, "Closed graph theorem"⟩, -- 50
  ⟨1386, .definition, "Hausdorff space"⟩, -- 51
  ⟨1399, .notation, "The Banach space C(K)"⟩, -- 52
  ⟨1416, .definition, "Normal space"⟩, -- 53
  ⟨1422, .definition, "Separation axioms T_i"⟩, -- 54
  ⟨1438, .theorem, "Compact Hausdorff spaces are normal"⟩, -- 55
  ⟨1475, .lemma, "Urysohn's lemma"⟩, -- 56
  ⟨1540, .theorem, "Tietze–Urysohn extension theorem"⟩, -- 57
  ⟨1689, .definition, "Equicontinuity"⟩, -- 58
  ⟨1697, .theorem, "Arzelà–Ascoli theorem"⟩, -- 59
  ⟨1704, .definition, "Epsilon-net"⟩, -- 60
  ⟨1708, .definition, "Totally bounded subset"⟩, -- 61
  ⟨1713, .proposition, "Total boundedness and Cauchy subsequences"⟩, -- 62
  ⟨1718, .corollary, "Total boundedness and compact closure"⟩, -- 63
  ⟨1723, .theorem, "Arzelà–Ascoli theorem, detailed proof"⟩, -- 64
  ⟨1770, .proposition, "Sequential characterization of total boundedness"⟩, -- 65
  ⟨1826, .theorem, "Peano local existence theorem"⟩, -- 66
  ⟨1837, .theorem, "Weierstrass approximation theorem"⟩, -- 67
  ⟨1846, .definition, "Algebra of functions"⟩, -- 68
  ⟨1876, .theorem, "Stone–Weierstrass theorem"⟩, -- 69
  ⟨1889, .lemma, "Lattice approximation lemma"⟩, -- 70
  ⟨2001, .lemma, "Closed real subalgebras are closed under max and min"⟩, -- 71
  ⟨2038, .theorem, "Stone–Weierstrass theorem, proof"⟩, -- 72
  ⟨2095, .theorem, "Complex Stone–Weierstrass theorem"⟩, -- 73
  ⟨2127, .proposition, "Fourier partial sums converge in L²"⟩, -- 74
  ⟨2139, .definition, "Inner product"⟩, -- 75
  ⟨2149, .definition, "Orthogonality"⟩, -- 76
  ⟨2158, .proposition, "Cauchy–Schwarz inequality"⟩, -- 77
  ⟨2183, .proposition, "An inner product induces a norm"⟩, -- 78
  ⟨2205, .definition, "Euclidean space"⟩, -- 79
  ⟨2212, .proposition, "Uniqueness of the inner product inducing a Euclidean norm"⟩, -- 80
  ⟨2244, .definition, "Hilbert space"⟩, -- 81
  ⟨2249, .proposition, "Parallelogram law"⟩, -- 82
  ⟨2276, .proposition, "Pythagoras theorem"⟩, -- 83
  ⟨2295, .proposition, "Continuity of the inner product"⟩, -- 84
  ⟨2311, .proposition, "Extension of an inner product to the completion"⟩, -- 85
  ⟨2351, .definition, "Orthogonal space"⟩, -- 86
  ⟨2358, .proposition, "Orthogonal complements and closure of spans"⟩, -- 87
  ⟨2382, .theorem, "Orthogonal decomposition and nearest-point projection"⟩, -- 88
  ⟨2445, .corollary, "Orthogonal projection map"⟩, -- 89
  ⟨2471, .proposition, "Riesz representation theorem"⟩, -- 90
  ⟨2533, .proposition, "Fourier convergence in L² via Hilbert space"⟩, -- 91
  ⟨2599, .definition, "Orthonormal system"⟩, -- 92
  ⟨2607, .definition, "Maximal orthonormal system"⟩, -- 93
  ⟨2616, .proposition, "Maximal orthonormal systems have dense span"⟩, -- 94
  ⟨2631, .proposition, "Dense span implies maximality"⟩, -- 95
  ⟨2648, .definition, "Hilbert-space basis"⟩, -- 96
  ⟨2654, .proposition, "Gram–Schmidt orthogonalisation"⟩, -- 97
  ⟨2701, .proposition, "A separable Hilbert space has a countable basis"⟩, -- 98
  ⟨2749, .lemma, "Bessel's inequality"⟩, -- 99
  ⟨2782, .proposition, "Parseval identity and coordinate expansion"⟩, -- 100
  ⟨2859, .proposition, "Riesz–Fischer theorem"⟩, -- 101
  ⟨2887, .definition, "Spectrum and resolvent set"⟩, -- 102
  ⟨2908, .definition, "Resolvent operator"⟩, -- 103
  ⟨2915, .definition, "Eigenvalue"⟩, -- 104
  ⟨2919, .definition, "Point spectrum"⟩, -- 105
  ⟨2927, .definition, "Approximate point spectrum"⟩, -- 106
  ⟨2940, .theorem, "Spectrum is nonempty, closed, and norm bounded"⟩, -- 107
  ⟨2949, .lemma, "Neumann series invertibility"⟩, -- 108
  ⟨2974, .lemma, "Stability of invertibility"⟩, -- 109
  ⟨2998, .theorem, "Spectrum theorem, proof"⟩, -- 110
  ⟨3077, .proposition, "Banach-valued Liouville theorem"⟩, -- 111
  ⟨3102, .theorem, "The approximate point spectrum contains the spectral boundary"⟩, -- 112
  ⟨3211, .definition, "Compact operator"⟩, -- 113
  ⟨3219, .proposition, "Compactness and the image of the unit ball"⟩, -- 114
  ⟨3226, .proposition, "Compact operators form a closed ideal"⟩, -- 115
  ⟨3283, .theorem, "Spectrum of a compact operator on a Banach space"⟩, -- 116
  ⟨3294, .proposition, "Only finitely many independent eigenvectors above a spectral threshold"⟩, -- 117
  ⟨3341, .lemma, "The image of I-T is closed for compact T"⟩, -- 118
  ⟨3377, .proposition, "A nonzero spectral value of a compact Hilbert operator is an eigenvalue"⟩, -- 119
  ⟨3409, .theorem, "Spectrum of a compact operator on a Hilbert space"⟩, -- 120
  ⟨3434, .definition, "Self-adjoint operator"⟩, -- 121
  ⟨3459, .theorem, "Spectral theorem for compact self-adjoint operators"⟩, -- 122
  ⟨3477, .proposition, "Eigenvalues of a self-adjoint operator are real"⟩, -- 123
  ⟨3489, .proposition, "Distinct eigenspaces are orthogonal"⟩, -- 124
  ⟨3502, .proposition, "A nonzero compact self-adjoint operator has a nonzero eigenvalue"⟩, -- 125
  ⟨3508, .lemma, "Norm of a self-adjoint operator from its quadratic form"⟩, -- 126
  ⟨3552, .proposition, "Existence of a nonzero eigenvalue, proof"⟩, -- 127
  ⟨3585, .proposition, "Spectral expansion of a compact self-adjoint operator"⟩ -- 128
]

theorem item_count : items.length = 128 := by native_decide

theorem source_lines_strictly_increase :
    List.Pairwise (fun a b : Nat ↦ a < b) (items.map Item.line) := by native_decide

end Cambridge.LinearAnalysis.SourceAudit
