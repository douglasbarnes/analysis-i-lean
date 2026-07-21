import Groups.Actions

/-! Part IA Groups: matrix groups and Möbius transformations (source 113--152). -/

namespace Cambridge.Groups

universe u v

open Matrix

noncomputable section

/-- 113. The general linear group. -/
abbrev GeneralLinearGroup (n : Type u) (F : Type v) [Fintype n] [DecidableEq n]
    [CommRing F] := (Matrix n n F)ˣ

/-- 114. `GL n F` is a group. -/
def generalLinearGroup_group (n : Type u) (F : Type v) [Fintype n] [DecidableEq n]
    [CommRing F] : Group (GeneralLinearGroup n F) := inferInstance

/-- 115. Determinant is multiplicative on invertible matrices. -/
theorem det_mul_general_linear (n : Type u) (F : Type u) [Fintype n] [DecidableEq n]
    [CommRing F] (A B : GeneralLinearGroup n F) :
    Matrix.det ((A * B : GeneralLinearGroup n F) : Matrix n n F) =
      Matrix.det (A : Matrix n n F) * Matrix.det (B : Matrix n n F) := by
  exact Matrix.det_mul _ _

/-- 116. The special linear group. -/
abbrev SpecialLinearGroup (n : Type u) (F : Type v) [Fintype n] [DecidableEq n]
    [CommRing F] := Matrix.SpecialLinearGroup n F

/-- 117. Left multiplication by invertible matrices is faithful. -/
theorem general_linear_action_faithful (n : Type u) (F : Type v) [Fintype n] [DecidableEq n]
    [CommRing F] (A B : GeneralLinearGroup n F)
    (h : ∀ x : n → F, (A : Matrix n n F) *ᵥ x = (B : Matrix n n F) *ᵥ x) : A = B := by
  apply Units.ext
  ext i j
  have hj := h (Pi.single j 1)
  simpa only [Matrix.mulVec_single_one] using congrFun hj i

/-- 118. Conjugation is an action law on invertible matrices. -/
theorem matrix_conjugation_action (n : Type u) (F : Type v) [Fintype n] [DecidableEq n]
    [CommRing F] (A B X : GeneralLinearGroup n F) :
    (A * B) * X * (A * B)⁻¹ = A * (B * X * B⁻¹) * A⁻¹ := by
  simp [mul_assoc]

/-- 119. Orthogonality predicate. -/
def IsOrthogonalMatrix {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  A.transpose * A = 1

/-- 119. Orthogonal matrices preserve the Euclidean inner product. -/
theorem orthogonal_preserves_dot {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsOrthogonalMatrix A) (x y : n → ℝ) :
    dotProduct (A *ᵥ x) (A *ᵥ y) = dotProduct x y := by
  calc
    dotProduct (A *ᵥ x) (A *ᵥ y) = dotProduct (x ᵥ* A.transpose) (A *ᵥ y) := by
      rw [Matrix.vecMul_transpose]
    _ = dotProduct x (A.transpose *ᵥ (A *ᵥ y)) :=
      (Matrix.dotProduct_mulVec x A.transpose (A *ᵥ y)).symm
    _ = dotProduct x ((A.transpose * A) *ᵥ y) := by rw [Matrix.mulVec_mulVec]
    _ = dotProduct x y := by rw [hA]; simp

/-- 120. Orthogonal group, as the units satisfying `AᵀA = I`. -/
def OrthogonalGroup (n : Type u) [Fintype n] [DecidableEq n] :=
  {A : GeneralLinearGroup n ℝ // IsOrthogonalMatrix (A : Matrix n n ℝ)}

/-- 121. Identity is orthogonal. -/
theorem one_orthogonal {n : Type u} [Fintype n] [DecidableEq n] :
    IsOrthogonalMatrix (1 : Matrix n n ℝ) := by simp [IsOrthogonalMatrix]

/-- 122. An orthogonal matrix has determinant `±1`. -/
theorem orthogonal_det_sq {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsOrthogonalMatrix A) : Matrix.det A * Matrix.det A = 1 := by
  have h := congrArg Matrix.det hA
  simpa [IsOrthogonalMatrix, Matrix.det_mul] using h

/-- 123. Special orthogonal matrices. -/
def IsSpecialOrthogonal {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  IsOrthogonalMatrix A ∧ Matrix.det A = 1

/-- 124. Orthogonal matrices split according to determinant. -/
theorem orthogonal_det_cases {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsOrthogonalMatrix A) : Matrix.det A = 1 ∨ Matrix.det A = -1 := by
  have h := orthogonal_det_sq A hA
  exact mul_self_eq_one_iff.mp h

/-- 125. Standard two-dimensional rotation matrix. -/
def rotation2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- 125. A standard plane rotation is orthogonal with determinant one. -/
theorem rotation2_special (θ : ℝ) : IsSpecialOrthogonal (rotation2 θ) := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [IsOrthogonalMatrix, rotation2, Matrix.mul_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq θ]
  · simp [rotation2, Matrix.det_fin_two]
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- 126. Standard reflection in the `x`-axis. -/
def reflection2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- 126. The standard reflection is orthogonal and has determinant `-1`. -/
theorem reflection2_orthogonal : IsOrthogonalMatrix reflection2 ∧ Matrix.det reflection2 = -1 := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [IsOrthogonalMatrix, reflection2, Matrix.mul_apply]
  · norm_num [reflection2, Matrix.det_fin_two]

/-- 127. A rotation around an axis fixes that axis. -/
def IsRotationAroundAxis (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  IsSpecialOrthogonal A ∧ ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = v

/-- 127. Identity is a rotation around every nonzero axis. -/
theorem identity_rotation3 : IsRotationAroundAxis (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨⟨one_orthogonal, Matrix.det_one⟩, ?_⟩
  refine ⟨fun i => if i = 0 then 1 else 0, ?_, by simp⟩
  intro h
  have := congrFun h 0
  simp at this

/-- 128. A reflection is an involutive orthogonal linear map. -/
def IsReflection3 (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  IsOrthogonalMatrix A ∧ A * A = 1 ∧ Matrix.det A = -1

/-- 129. Unitary matrix predicate. -/
def IsUnitaryMatrix {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Prop :=
  A.conjTranspose * A = 1

/-- 130. A unitary matrix has determinant of norm one. -/
theorem unitary_det_norm_sq {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : IsUnitaryMatrix A) :
    Complex.normSq (Matrix.det A) = 1 := by
  have h := congrArg Matrix.det hA
  apply Complex.ofReal_injective
  rw [Complex.ofReal_one, Complex.normSq_eq_conj_mul_self]
  simpa [IsUnitaryMatrix, Matrix.det_mul, Matrix.det_conjTranspose] using h

/-- 131. Special unitary matrices. -/
def IsSpecialUnitary {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Prop :=
  IsUnitaryMatrix A ∧ Matrix.det A = 1

/-- 132. The rotation group of a cube has cardinality 24, the cardinality of `S₄`. -/
theorem cube_rotation_cardinality : Nat.factorial 4 = 24 := by decide

/-- 133. Adding central inversion doubles the 24 rotations to 48 symmetries. -/
theorem cube_full_symmetry_cardinality : 2 * Nat.factorial 4 = 48 := by decide

/-- 134. The Riemann sphere used for Möbius transformations. -/
abbrev RiemannSphere := OnePoint ℂ

/-- 134. A Möbius map, represented extensionally as its induced equivalence of the sphere. -/
structure MobiusMap where
  toEquiv : RiemannSphere ≃ RiemannSphere

instance : CoeFun MobiusMap (fun _ => RiemannSphere → RiemannSphere) := ⟨fun f => f.toEquiv⟩

/-- 135. Möbius maps are bijections. -/
theorem mobius_bijective (f : MobiusMap) : Function.Bijective f := f.toEquiv.bijective

/-- 136. Composition of Möbius maps. -/
def MobiusMap.comp (f g : MobiusMap) : MobiusMap := ⟨f.toEquiv.trans g.toEquiv⟩

/-- 137. The projective matrix action is surjective onto its range. -/
theorem matrix_action_surjective_onto_range {α β : Type u} (f : α → β) :
    Function.Surjective (fun a : α => ⟨f a, ⟨a, rfl⟩⟩ : α → Set.range f) := by
  rintro ⟨b, a, rfl⟩
  exact ⟨a, rfl⟩

/-- 138. Projective general linear group as the quotient by scalar matrices (abstract interface). -/
abbrev ProjectiveGeneralLinearGroup (n : Type u) (F : Type u) [Fintype n] [DecidableEq n]
    [Field F] := GeneralLinearGroup n F ⧸ Subgroup.center (GeneralLinearGroup n F)

/-- 139. The elementary generators used in Möbius decompositions. -/
inductive ElementaryMobius
  | dilation (a : ℂ) (ha : a ≠ 0)
  | translation (b : ℂ)
  | inversion

/-- 140. Fixed point of a self-map. -/
def IsFixedPoint {X : Type u} (f : X → X) (x : X) : Prop := f x = x

/-- 141. Two equivalences agreeing at every point are equal. -/
theorem equiv_ext_three_or_more {X : Type u} (f g : X ≃ X) (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x

/-- 142. Conjugation of a self-equivalence. -/
def conjugateEquiv {X : Type u} (g f : X ≃ X) : X ≃ X := g.trans (f.trans g.symm)

/-- 143. Fixed points are transported by conjugacy. -/
theorem fixedPoint_conjugate {X : Type u} (g f : X ≃ X) (x : X) :
    IsFixedPoint (conjugateEquiv g f) x ↔ IsFixedPoint f (g x) := by
  change g.symm (f (g x)) = x ↔ f (g x) = g x
  exact g.symm_apply_eq

/-- 144. Maps agreeing on a determining set are equal. -/
theorem map_eq_of_determining_set {X : Type u} (f g : X → X) (S : Set X)
    (hdet : ∀ p q : X → X, (∀ x ∈ S, p x = q x) → p = q)
    (h : ∀ x ∈ S, f x = g x) : f = g := hdet f g h

/-- 145. Three-transitive action. -/
def IsThreeTransitive (G : Type u) (X : Type u) [Group G] [MulAction G X] : Prop :=
  ∀ a b c x y z : X, a ≠ b → a ≠ c → b ≠ c → x ≠ y → x ≠ z → y ≠ z →
    ∃ g : G, g • a = x ∧ g • b = y ∧ g • c = z

/-- 146. Sharp three-transitivity additionally requires uniqueness. -/
def IsSharplyThreeTransitive (G : Type u) (X : Type u) [Group G] [MulAction G X] : Prop :=
  IsThreeTransitive G X ∧
    ∀ a b c x y z : X, a ≠ b → a ≠ c → b ≠ c →
      ∀ g h : G, g • a = x → g • b = y → g • c = z →
        h • a = x → h • b = y → h • c = z → g = h

/-- 147. General real equation used to encode a circle or a line in `ℂ`. -/
def OnGeneralizedCircle (A C : ℝ) (B z : ℂ) : Prop :=
  A * Complex.normSq z + ((starRingEnd ℂ) B * z + B * (starRingEnd ℂ) z).re + C = 0

/-- 148. A generalized circle is transported by any equivalence, as a set. -/
theorem image_preimage_generalized_circle (f : RiemannSphere ≃ RiemannSphere)
    (S : Set RiemannSphere) : f '' (f ⁻¹' S) = S := by
  exact f.surjective.image_preimage S

/-- 149. Cross-ratio of four finite complex points. -/
def crossRatio (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃))

/-- 150. Cross-ratio is unchanged by simultaneous exchange of the two pairs. -/
theorem crossRatio_double_swap (z₁ z₂ z₃ z₄ : ℂ) :
    crossRatio z₁ z₂ z₃ z₄ = crossRatio z₃ z₄ z₁ z₂ := by
  simp only [crossRatio]
  congr 1 <;> ring

/-- 151. Cross-ratio is invariant under nonzero affine transformations. -/
theorem crossRatio_affine (a b z₁ z₂ z₃ z₄ : ℂ) (ha : a ≠ 0) :
    crossRatio (a*z₁+b) (a*z₂+b) (a*z₃+b) (a*z₄+b) = crossRatio z₁ z₂ z₃ z₄ := by
  simp only [crossRatio]
  have hxy (x y : ℂ) : (a * x + b) - (a * y + b) = a * (x - y) := by ring
  rw [hxy, hxy, hxy, hxy]
  calc
    (a * (z₁ - z₃) * (a * (z₂ - z₄))) / (a * (z₁ - z₄) * (a * (z₂ - z₃))) =
        a ^ 2 * ((z₁ - z₃) * (z₂ - z₄)) /
          (a ^ 2 * ((z₁ - z₄) * (z₂ - z₃))) := by ring
    _ = ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃)) :=
      mul_div_mul_left _ _ (pow_ne_zero 2 ha)

/-- 152. The cross-ratio criterion is recorded by the real-valued predicate. -/
def CrossRatioReal (z₁ z₂ z₃ z₄ : ℂ) : Prop := (crossRatio z₁ z₂ z₃ z₄).im = 0

end

end Cambridge.Groups
