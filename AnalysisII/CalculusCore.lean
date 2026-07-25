import Mathlib

open Filter Function Set Topology
open scoped Topology

namespace AnalysisII

noncomputable section

/-- Analysis II source 55(ii): a map into a finite product is differentiable
iff all of its coordinate functions are differentiable. -/
theorem source055_differentiableAt_pi
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    {f : E → ∀ i, F i} {x : E} :
    DifferentiableAt 𝕜 f x ↔ ∀ i, DifferentiableAt 𝕜 (fun y => f y i) x :=
  differentiableAt_pi

/-- Analysis II source 55(iii): linear combinations of differentiable maps are
differentiable and their derivatives combine linearly. -/
theorem source055_linear_combination
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {f' g' : E →L[𝕜] F} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (a b : 𝕜) :
    HasFDerivAt (fun y => a • f y + b • g y) (a • f' + b • g') x := by
  simpa using (hf.const_smul a).add (hg.const_smul b)

/-- Analysis II source 55(vi): differentiability of a vector-valued map gives
derivatives of every coordinate function. -/
theorem source055_coordinate_derivatives
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    {f : E → ∀ i, F i} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    ∀ i, ∃ A : E →L[𝕜] F i, HasFDerivAt (fun y => f y i) A x := by
  intro i
  exact (differentiableAt_pi.mp hf i)

/-- Analysis II source 57(i): the operator norm gives a finite global bound. -/
theorem source057_operator_norm_finite_bound
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖A x‖ ≤ C * ‖x‖ :=
  ⟨‖A‖, norm_nonneg _, A.le_opNorm⟩

/-- Analysis II source 57(ii): the usual norm axioms for continuous linear maps. -/
theorem source057_operator_norm_axioms
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A B : E →L[𝕜] F) (c : 𝕜) :
    0 ≤ ‖A‖ ∧ (‖A‖ = 0 ↔ A = 0) ∧
      ‖c • A‖ = ‖c‖ * ‖A‖ ∧ ‖A + B‖ ≤ ‖A‖ + ‖B‖ := by
  exact ⟨norm_nonneg _, norm_eq_zero, norm_smul _ _, norm_add_le _ _⟩

/-- Analysis II source 58(i): a linear map out of `ℝ` is determined by its value at `1`. -/
theorem source058_linear_map_from_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ →L[ℝ] F) (x : ℝ) : A x = x • A 1 := by
  rw [← A.map_smul]
  simp

/-- Analysis II source 65: strict inverse function theorem, packaged as the local
open partial homeomorphism produced by Mathlib.  A continuously differentiable
map with invertible derivative supplies this strict derivative in the usual way. -/
theorem source065_inverse_function_theorem
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ a ∈ e.source ∧ f a ∈ e.target ∧
        HasStrictFDerivAt e.symm (f'.symm : F →L[𝕜] E) (f a) := by
  refine ⟨hf.toOpenPartialHomeomorph f, rfl,
    hf.mem_toOpenPartialHomeomorph_source,
    hf.image_mem_toOpenPartialHomeomorph_target, ?_⟩
  simpa [HasStrictFDerivAt.localInverse_def] using hf.to_localInverse

end

end AnalysisII
