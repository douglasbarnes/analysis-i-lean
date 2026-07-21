import ComplexMethods.Transforms

namespace ComplexMethods.SourceAudit

/-- The five labelled-environment kinds used by the source. -/
inductive Kind where
  | definition | proposition | theorem | lemma | notation
  deriving DecidableEq, Repr

/-- A source item with its one-based ordinal, TeX line, kind, and printed title/description. -/
structure Item where
  ordinal : ℕ
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

/-- Ordered, authoritative extraction from `IB_L/complex_methods.tex`. -/
def items : List Item :=
  [ ⟨1, 45, .definition, "Modulus and argument"⟩
  , ⟨2, 53, .definition, "Principal value of argument"⟩
  , ⟨3, 62, .definition, "Open set"⟩
  , ⟨4, 66, .definition, "Neighbourhood"⟩
  , ⟨5, 72, .definition, "The extended complex plane"⟩
  , ⟨6, 109, .definition, "Complex differentiable function"⟩
  , ⟨7, 118, .definition, "Analytic function"⟩
  , ⟨8, 122, .definition, "Entire function"⟩
  , ⟨9, 158, .proposition, "Cauchy-Riemann equations"⟩
  , ⟨10, 165, .proposition, "Cauchy-Riemann converse"⟩
  , ⟨11, 236, .definition, "Harmonic conjugates"⟩
  , ⟨12, 267, .definition, "Harmonic function"⟩
  , ⟨13, 272, .proposition, "Analytic parts are harmonic"⟩
  , ⟨14, 306, .definition, "Branch point"⟩
  , ⟨15, 495, .definition, "Circline"⟩
  , ⟨16, 500, .proposition, "Mobius maps take circlines to circlines"⟩
  , ⟨17, 532, .proposition, "Mobius map through three prescribed points"⟩
  , ⟨18, 553, .definition, "Conformal map"⟩
  , ⟨19, 562, .proposition, "Conformal maps preserve angles"⟩
  , ⟨20, 868, .definition, "Curve"⟩
  , ⟨21, 872, .definition, "Closed curve"⟩
  , ⟨22, 876, .definition, "Simple curve"⟩
  , ⟨23, 880, .definition, "Contour"⟩
  , ⟨24, 885, .notation, "Reverse and joined contours"⟩
  , ⟨25, 900, .definition, "Contour integral"⟩
  , ⟨26, 956, .proposition, "Contour integral rules"⟩
  , ⟨27, 1000, .definition, "Simply connected domain"⟩
  , ⟨28, 1015, .theorem, "Cauchy's theorem"⟩
  , ⟨29, 1042, .proposition, "Contour deformation invariance"⟩
  , ⟨30, 1124, .theorem, "Cauchy's integral formula"⟩
  , ⟨31, 1179, .theorem, "Liouville's theorem"⟩
  , ⟨32, 1217, .proposition, "Laurent series"⟩
  , ⟨33, 1356, .definition, "Zeros"⟩
  , ⟨34, 1362, .definition, "Simple zero"⟩
  , ⟨35, 1389, .definition, "Isolated singularity"⟩
  , ⟨36, 1464, .definition, "Residue"⟩
  , ⟨37, 1468, .proposition, "Residue at a simple pole"⟩
  , ⟨38, 1485, .proposition, "Residue at a pole of order N"⟩
  , ⟨39, 1593, .theorem, "One-singularity residue formula"⟩
  , ⟨40, 1606, .theorem, "Residue theorem"⟩
  , ⟨41, 2140, .lemma, "Jordan's lemma"⟩
  , ⟨42, 2283, .definition, "Fourier transform"⟩
  , ⟨43, 2321, .notation, "Fourier transform notation"⟩
  , ⟨44, 2440, .definition, "Laplace transform"⟩
  , ⟨45, 2448, .notation, "Laplace transform notation"⟩
  , ⟨46, 2492, .proposition, "Laplace transform rules"⟩
  , ⟨47, 2578, .proposition, "Bromwich inversion"⟩
  , ⟨48, 2606, .proposition, "Inversion by finitely many residues"⟩
  , ⟨49, 2778, .definition, "Convolution"⟩
  , ⟨50, 2789, .theorem, "Convolution theorem"⟩ ]

/-- The extraction contains exactly all 50 labelled environments. -/
theorem item_count : items.length = 50 := by native_decide

/-- The source ordinals have no gaps or repetitions. -/
theorem ordinal_completeness : items.map Item.ordinal = List.range' 1 50 := by native_decide

/-- Authoritative environment split: 26 definitions, 14 propositions, 6 theorems, 1 lemma,
and 3 notation blocks. -/
theorem kind_counts :
    (items.countP (fun i ↦ i.kind = .definition),
      items.countP (fun i ↦ i.kind = .proposition),
      items.countP (fun i ↦ i.kind = .theorem),
      items.countP (fun i ↦ i.kind = .lemma),
      items.countP (fun i ↦ i.kind = .notation)) = (26, 14, 6, 1, 3) := by
  native_decide

end ComplexMethods.SourceAudit
