import MethodsCourse.Core

namespace MethodsCourse.SourceAudit

inductive SourceItem
  | l0079 | l0095 | l0109 | l0164 | l0173 | l0354 | l0404 | l0500 | l0512
  | l0521 | l0534 | l0547 | l0555 | l0659 | l0720 | l0734 | l0738 | l1195
  | l1345 | l1635 | l1654 | l1774 | l2120 | l2334 | l2696 | l2736 | l2746
  | l2957 | l3002 | l3039 | l3454 | l3466 | l3506
  deriving DecidableEq, Repr

structure Entry where
  item : SourceItem
  line : Nat
  kind : String
  title : String
  deriving DecidableEq, Repr

def inventory : List Entry :=
  [⟨.l0079, 79, "definition", "Vector space"⟩,
   ⟨.l0095, 95, "definition", "Inner product"⟩,
   ⟨.l0109, 109, "definition", "Basis"⟩,
   ⟨.l0164, 164, "definition", "Homogeneous boundary conditions"⟩,
   ⟨.l0173, 173, "definition", "Periodic function"⟩,
   ⟨.l0354, 354, "theorem", "Parseval's theorem"⟩,
   ⟨.l0404, 404, "definition", "Adjoint and self-adjoint"⟩,
   ⟨.l0500, 500, "definition", "Inner product with weight"⟩,
   ⟨.l0512, 512, "definition", "Eigenfunction with weight"⟩,
   ⟨.l0521, 521, "proposition", "Sturm--Liouville eigenvalues are real"⟩,
   ⟨.l0534, 534, "proposition", "Distinct eigenfunctions are orthogonal"⟩,
   ⟨.l0547, 547, "theorem", "Compact-domain spectrum is discrete"⟩,
   ⟨.l0555, 555, "theorem", "Eigenfunctions are complete"⟩,
   ⟨.l0659, 659, "theorem", "Parseval's theorem II"⟩,
   ⟨.l0720, 720, "definition", "Laplace's equation"⟩,
   ⟨.l0734, 734, "definition", "Harmonic functions"⟩,
   ⟨.l0738, 738, "proposition", "Dirichlet problem existence and uniqueness"⟩,
   ⟨.l1195, 1195, "definition", "Heat equation"⟩,
   ⟨.l1345, 1345, "proposition", "Heat-equation uniqueness"⟩,
   ⟨.l1635, 1635, "proposition", "Wave energy conservation"⟩,
   ⟨.l1654, 1654, "proposition", "Wave-equation uniqueness"⟩,
   ⟨.l1774, 1774, "definition", "Dirac-delta"⟩,
   ⟨.l2120, 2120, "definition", "Fourier transform"⟩,
   ⟨.l2334, 2334, "theorem", "Parseval's theorem (again)"⟩,
   ⟨.l2696, 2696, "definition", "Well-posed problem"⟩,
   ⟨.l2736, 2736, "definition", "Tangent vector"⟩,
   ⟨.l2746, 2746, "definition", "Integral curve"⟩,
   ⟨.l2957, 2957, "definition", "Symbol and principal part"⟩,
   ⟨.l3002, 3002, "definition", "Elliptic/hyperbolic/ultra-hyperbolic/parabolic"⟩,
   ⟨.l3039, 3039, "definition", "Characteristic surface"⟩,
   ⟨.l3454, 3454, "proposition", "Green's first identity"⟩,
   ⟨.l3466, 3466, "proposition", "Green's second identity"⟩,
   ⟨.l3506, 3506, "proposition", "Green's third identity"⟩]

def sourceItems : List SourceItem := inventory.map Entry.item

theorem authoritative_count : inventory.length = 33 := by native_decide
theorem definition_count : (inventory.filter (fun e => e.kind = "definition")).length = 19 := by
  native_decide
theorem proposition_count : (inventory.filter (fun e => e.kind = "proposition")).length = 9 := by
  native_decide
theorem theorem_count : (inventory.filter (fun e => e.kind = "theorem")).length = 5 := by
  native_decide

theorem ordered_lines : inventory.map Entry.line =
    [79, 95, 109, 164, 173, 354, 404, 500, 512, 521, 534, 547, 555, 659,
     720, 734, 738, 1195, 1345, 1635, 1654, 1774, 2120, 2334, 2696, 2736,
     2746, 2957, 3002, 3039, 3454, 3466, 3506] := by native_decide

theorem complete (item : SourceItem) : item ∈ sourceItems := by
  cases item <;> native_decide

theorem no_duplicates : sourceItems.Nodup := by native_decide

end MethodsCourse.SourceAudit
