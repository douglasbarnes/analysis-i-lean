import GroupsRingsModules.Modules

/-! Exact ordered inventory of every labelled environment in `IB_L/groups_rings_and_modules.tex`. -/

namespace GroupsRingsModules.SourceAudit

inductive Kind where
  | definition
  | lemma
  | theorem
  | proposition
  | corollary
  | notation
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨52, .definition, "Group"⟩
  , ⟨62, .lemma, "lemma at source line 62"⟩
  , ⟨73, .definition, "Subgroup"⟩
  , ⟨84, .lemma, "lemma at source line 84"⟩
  , ⟨88, .definition, "Abelian group"⟩
  , ⟨111, .definition, "Coset"⟩
  , ⟨120, .theorem, "Lagrange's theorem"⟩
  , ⟨130, .definition, "Order of group"⟩
  , ⟨135, .definition, "Order of element"⟩
  , ⟨142, .lemma, "lemma at source line 142"⟩
  , ⟨198, .definition, "Normal subgroup"⟩
  , ⟨203, .definition, "Quotient group"⟩
  , ⟨214, .definition, "Homomorphism"⟩
  , ⟨222, .lemma, "lemma at source line 222"⟩
  , ⟨245, .definition, "Kernel"⟩
  , ⟨252, .definition, "Image"⟩
  , ⟨259, .lemma, "lemma at source line 259"⟩
  , ⟨285, .definition, "Isomorphism"⟩
  , ⟨289, .definition, "Isomorphic group"⟩
  , ⟨295, .lemma, "lemma at source line 295"⟩
  , ⟨302, .theorem, "First isomorphism theorem"⟩
  , ⟨357, .theorem, "Second isomorphism theorem"⟩
  , ⟨407, .theorem, "Third isomorphism theorem"⟩
  , ⟨433, .definition, "Simple group"⟩
  , ⟨439, .lemma, "lemma at source line 439"⟩
  , ⟨454, .theorem, "thm at source line 454"⟩
  , ⟨478, .definition, "Symmetric group"⟩
  , ⟨491, .definition, "Even and odd permutation"⟩
  , ⟨506, .definition, "Alternating group"⟩
  , ⟨517, .definition, "Symmetric group of $X$"⟩
  , ⟨523, .definition, "Permutation group"⟩
  , ⟨536, .definition, "Group action"⟩
  , ⟨549, .lemma, "lemma at source line 549"⟩
  , ⟨574, .definition, "Permutation representation"⟩
  , ⟨580, .notation, "notation at source line 580"⟩
  , ⟨585, .proposition, "prop at source line 585"⟩
  , ⟨669, .theorem, "thm at source line 669"⟩
  , ⟨681, .corollary, "cor at source line 681"⟩
  , ⟨704, .definition, "Orbit"⟩
  , ⟨711, .definition, "Stabilizer"⟩
  , ⟨719, .theorem, "Orbit-stabilizer theorem"⟩
  , ⟨743, .definition, "Automorphism group"⟩
  , ⟨756, .definition, "Conjugacy class"⟩
  , ⟨764, .definition, "Centralizer"⟩
  , ⟨772, .definition, "Center"⟩
  , ⟨781, .proposition, "prop at source line 781"⟩
  , ⟨790, .definition, "Normalizer"⟩
  , ⟨801, .theorem, "thm at source line 801"⟩
  , ⟨883, .definition, "$p$-group"⟩
  , ⟨887, .theorem, "thm at source line 887"⟩
  , ⟨906, .lemma, "lemma at source line 906"⟩
  , ⟨921, .corollary, "cor at source line 921"⟩
  , ⟨929, .theorem, "thm at source line 929"⟩
  , ⟨949, .theorem, "Classification of finite abelian groups"⟩
  , ⟨963, .lemma, "lemma at source line 963"⟩
  , ⟨976, .corollary, "cor at source line 976"⟩
  , ⟨992, .theorem, "Sylow theorems"⟩
  , ⟨1008, .lemma, "lemma at source line 1008"⟩
  , ⟨1016, .corollary, "cor at source line 1016"⟩
  , ⟨1179, .definition, "Ring"⟩
  , ⟨1199, .notation, "notation at source line 1199"⟩
  , ⟨1206, .definition, "Commutative ring"⟩
  , ⟨1212, .definition, "Subring"⟩
  , ⟨1229, .definition, "Unit"⟩
  , ⟨1235, .definition, "Field"⟩
  , ⟨1267, .definition, "Product of rings"⟩
  , ⟨1277, .definition, "Polynomial"⟩
  , ⟨1286, .definition, "Degree of polynomial"⟩
  , ⟨1290, .definition, "Monic polynomial"⟩
  , ⟨1294, .definition, "Polynomial ring"⟩
  , ⟨1311, .definition, "Power series"⟩
  , ⟨1333, .definition, "Laurent polynomials"⟩
  , ⟨1355, .definition, "Homomorphism of rings"⟩
  , ⟨1365, .definition, "Isomorphism of rings"⟩
  , ⟨1369, .definition, "Kernel"⟩
  , ⟨1376, .definition, "Image"⟩
  , ⟨1383, .lemma, "lemma at source line 1383"⟩
  , ⟨1393, .definition, "Ideal"⟩
  , ⟨1403, .lemma, "lemma at source line 1403"⟩
  , ⟨1447, .definition, "Generator of ideal"⟩
  , ⟨1461, .definition, "Generator of ideal"⟩
  , ⟨1469, .definition, "Principal ideal"⟩
  , ⟨1484, .definition, "Quotient ring"⟩
  , ⟨1492, .proposition, "prop at source line 1492"⟩
  , ⟨1534, .proposition, "Euclidean algorithm for polynomials"⟩
  , ⟨1614, .theorem, "First isomorphism theorem"⟩
  , ⟨1641, .theorem, "Second isomorphism theorem"⟩
  , ⟨1686, .theorem, "Third isomorphism theorem"⟩
  , ⟨1716, .definition, "Characteristic of ring"⟩
  , ⟨1729, .definition, "Integral domain"⟩
  , ⟨1734, .definition, "Zero divisor"⟩
  , ⟨1753, .lemma, "lemma at source line 1753"⟩
  , ⟨1769, .lemma, "lemma at source line 1769"⟩
  , ⟨1785, .notation, "notation at source line 1785"⟩
  , ⟨1793, .definition, "Field of fractions"⟩
  , ⟨1802, .theorem, "thm at source line 1802"⟩
  , ⟨1871, .lemma, "lemma at source line 1871"⟩
  , ⟨1885, .definition, "Maximal ideal"⟩
  , ⟨1891, .lemma, "lemma at source line 1891"⟩
  , ⟨1900, .definition, "Prime ideal"⟩
  , ⟨1916, .lemma, "lemma at source line 1916"⟩
  , ⟨1927, .proposition, "prop at source line 1927"⟩
  , ⟨1944, .lemma, "lemma at source line 1944"⟩
  , ⟨1957, .definition, "Unit"⟩
  , ⟨1961, .definition, "Division"⟩
  , ⟨1965, .definition, "Associates"⟩
  , ⟨1976, .definition, "Irreducible"⟩
  , ⟨1981, .definition, "Prime"⟩
  , ⟨1992, .lemma, "lemma at source line 1992"⟩
  , ⟨2004, .lemma, "lemma at source line 2004"⟩
  , ⟨2046, .definition, "Euclidean domain"⟩
  , ⟨2107, .definition, "Principal ideal domain"⟩
  , ⟨2115, .proposition, "prop at source line 2115"⟩
  , ⟨2154, .definition, "Unique factorization domain"⟩
  , ⟨2166, .lemma, "lemma at source line 2166"⟩
  , ⟨2189, .lemma, "lemma at source line 2189"⟩
  , ⟨2194, .definition, "Ascending chain condition"⟩
  , ⟨2198, .definition, "Noetherian ring"⟩
  , ⟨2218, .proposition, "prop at source line 2218"⟩
  , ⟨2245, .definition, "Greatest common divisor"⟩
  , ⟨2251, .lemma, "lemma at source line 2251"⟩
  , ⟨2296, .definition, "Content"⟩
  , ⟨2304, .definition, "Primitive polynomial"⟩
  , ⟨2310, .lemma, "Gauss' lemma"⟩
  , ⟨2336, .lemma, "lemma at source line 2336"⟩
  , ⟨2363, .corollary, "cor at source line 2363"⟩
  , ⟨2377, .lemma, "Gauss' lemma"⟩
  , ⟨2414, .proposition, "prop at source line 2414"⟩
  , ⟨2461, .theorem, "thm at source line 2461"⟩
  , ⟨2524, .proposition, "Eisenstein's criterion"⟩
  , ⟨2600, .definition, "Gaussian integers"⟩
  , ⟨2620, .proposition, "prop at source line 2620"⟩
  , ⟨2633, .lemma, "lemma at source line 2633"⟩
  , ⟨2645, .proposition, "prop at source line 2645"⟩
  , ⟨2675, .corollary, "cor at source line 2675"⟩
  , ⟨2725, .definition, "Algebraic integer"⟩
  , ⟨2731, .notation, "notation at source line 2731"⟩
  , ⟨2741, .proposition, "prop at source line 2741"⟩
  , ⟨2750, .definition, "Minimal polynomial"⟩
  , ⟨2803, .lemma, "lemma at source line 2803"⟩
  , ⟨2815, .definition, "Noetherian ring"⟩
  , ⟨2847, .definition, "Finitely generated ideal"⟩
  , ⟨2851, .proposition, "prop at source line 2851"⟩
  , ⟨2884, .proposition, "prop at source line 2884"⟩
  , ⟨2899, .theorem, "Hilbert basis theorem"⟩
  , ⟨2979, .definition, "Module"⟩
  , ⟨3053, .definition, "Submodule"⟩
  , ⟨3065, .definition, "Quotient module"⟩
  , ⟨3075, .definition, "$R$-module homomorphism and isomorphism"⟩
  , ⟨3090, .theorem, "First isomorphism theorem"⟩
  , ⟨3107, .theorem, "Second isomorphism theorem"⟩
  , ⟨3122, .theorem, "Third isomorphism theorem"⟩
  , ⟨3136, .definition, "Annihilator"⟩
  , ⟨3154, .definition, "Submodule generated by element"⟩
  , ⟨3178, .definition, "Finitely generated module"⟩
  , ⟨3187, .lemma, "lemma at source line 3187"⟩
  , ⟨3226, .corollary, "cor at source line 3226"⟩
  , ⟨3261, .definition, "Direct sum of modules"⟩
  , ⟨3281, .definition, "Linear independence"⟩
  , ⟨3290, .definition, "Freely generate"⟩
  , ⟨3301, .definition, "Free module and basis"⟩
  , ⟨3310, .proposition, "prop at source line 3310"⟩
  , ⟨3355, .definition, "Relations"⟩
  , ⟨3359, .definition, "Finitely presented module"⟩
  , ⟨3375, .proposition, "Invariance of dimension/rank"⟩
  , ⟨3399, .proposition, "prop at source line 3399"⟩
  , ⟨3404, .proposition, "prop at source line 3404"⟩
  , ⟨3414, .proposition, "Invariance of dimension/rank"⟩
  , ⟨3440, .definition, "Elementary row operations"⟩
  , ⟨3491, .definition, "Equivalent matrices"⟩
  , ⟨3516, .theorem, "Smith normal form"⟩
  , ⟨3536, .definition, "Invariant factors"⟩
  , ⟨3686, .definition, "Minor"⟩
  , ⟨3691, .definition, "Fitting ideal"⟩
  , ⟨3696, .lemma, "lemma at source line 3696"⟩
  , ⟨3759, .corollary, "cor at source line 3759"⟩
  , ⟨3808, .lemma, "lemma at source line 3808"⟩
  , ⟨3834, .theorem, "thm at source line 3834"⟩
  , ⟨3872, .corollary, "cor at source line 3872"⟩
  , ⟨3884, .theorem, "Classification of finitely-generated modules over a Euclidean domain"⟩
  , ⟨3967, .corollary, "Classification of finitely-generated abelian groups"⟩
  , ⟨3983, .corollary, "cor at source line 3983"⟩
  , ⟨3997, .lemma, "Chinese remainder theorem"⟩
  , ⟨4062, .theorem, "Prime decomposition theorem"⟩
  , ⟨4095, .lemma, "lemma at source line 4095"⟩
  , ⟨4180, .theorem, "Rational canonical form"⟩
  , ⟨4216, .lemma, "lemma at source line 4216"⟩
  , ⟨4226, .theorem, "Jordan normal form"⟩
  , ⟨4274, .theorem, "Cayley-Hamilton theorem"⟩
  , ⟨4317, .lemma, "lemma at source line 4317"⟩
  , ⟨4349, .corollary, "cor at source line 4349"⟩ ]

def countKind (k : Kind) : ℕ := (items.filter fun item ↦ item.kind = k).length

theorem item_count : items.length = 191 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide
theorem definition_count : countKind .definition = 92 := by native_decide
theorem lemma_count : countKind .lemma = 36 := by native_decide
theorem theorem_count : countKind .theorem = 28 := by native_decide
theorem proposition_count : countKind .proposition = 19 := by native_decide
theorem corollary_count : countKind .corollary = 12 := by native_decide
theorem notation_count : countKind .notation = 4 := by native_decide
theorem kind_counts_complete :
    countKind .definition + countKind .lemma + countKind .theorem + countKind .proposition + countKind .corollary + countKind .notation = items.length := by native_decide

end GroupsRingsModules.SourceAudit

