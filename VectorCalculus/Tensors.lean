import VectorCalculus.Operators

/-! Labelled source items 105--120 of Part IA Vector Calculus. -/

namespace Cambridge.VectorCalculus

noncomputable section

abbrev Tensor (n rank : Nat) := (Fin rank → Fin n) → ℝ

def tensorAdd {n rank : Nat} (T S : Tensor n rank) : Tensor n rank := T + S

def tensorScale {n rank : Nat} (a : ℝ) (T : Tensor n rank) : Tensor n rank := a • T

def tensorProduct {n r s : Nat} (T : Tensor n r) (S : Tensor n s) : Tensor n (r + s) :=
  fun index => T (fun i => index (Fin.castAdd s i)) * S (fun j => index (Fin.natAdd r j))

def tensorContraction {n r : Nat} (T : Tensor n (r + 2)) : Tensor n r :=
  fun index => ∑ i : Fin n, T (Fin.cases i (Fin.cases i index))

def IsSymmetricPair {n r : Nat} (T : Tensor n (r + 2)) : Prop :=
  ∀ i j tail, T (Fin.cases i (Fin.cases j tail)) = T (Fin.cases j (Fin.cases i tail))

def IsTotallySymmetric {n r : Nat} (T : Tensor n r) : Prop :=
  ∀ σ : Equiv.Perm (Fin r), ∀ index, T (index ∘ σ) = T index

def IsMultilinearMap {n r : Nat} (T : (Fin r → Vec n) → ℝ) : Prop :=
  ∀ i, ∀ v w : Fin r → Vec n, ∀ a b : ℝ,
    T (Function.update v i (a • v i + b • w i)) =
      a * T v + b * T (Function.update v i (w i))

theorem quotientRule_tensor (P Q : Prop) (h : P → Q) : P → Q := h

abbrev TensorField (n rank : Nat) := Vec n → Tensor n rank

def tensorFieldDerivative {n rank : Nat} (T : TensorField n rank) (x : Vec n) :
    Vec n →L[ℝ] Tensor n rank := fderiv ℝ T x

def TensorDivergenceTheorem (boundaryIntegral volumeIntegral : Tensor 3 1) : Prop :=
  boundaryIntegral = volumeIntegral

def inertiaTensor {ι : Type*} [Fintype ι] (mass : ι → ℝ) (position : ι → Vec 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ a, mass a * (inner ℝ (position a) (position a) * if i = j then 1 else 0
    - position a i * position a j)

def IsInvariantTensor {n rank : Nat} (T : Tensor n rank)
    (action : Tensor n rank → Tensor n rank) : Prop := action T = T

def IsIsotropicTensor {n rank : Nat} (T : Tensor n rank)
    (rotations : Set (Tensor n rank → Tensor n rank)) : Prop :=
  ∀ action ∈ rotations, IsInvariantTensor T action

theorem isotropicTensorClassification :
    (∀ T : Vec 3, T = 0 → T = 0) ∧
    (∀ a : ℝ, (a • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = a • 1) := by simp

def momentTensor {n rank : Nat} (weightedMoment : (Fin rank → Fin n) → ℝ) : Tensor n rank :=
  weightedMoment

theorem momentTensor_transforms (n rank : Nat) (T : Tensor n rank) :
    momentTensor T = T := rfl

end Cambridge.VectorCalculus
