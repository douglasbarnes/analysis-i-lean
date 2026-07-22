import FluidDynamicsCourse.Core

/-!
# Source audit: `IB_L/fluid_dynamics.tex`

Every labelled `defi`, `prop`, and `law` environment in the authoritative TeX source is listed
below in exact source order, with its original line number and title.
-/

namespace FluidDynamicsCourse.SourceAudit

inductive Kind where
  | definition | proposition | law
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨59, .definition, "Fluid"⟩
  , ⟨73, .definition, "Newtonian fluids and viscosity"⟩
  , ⟨78, .definition, "Stress"⟩
  , ⟨83, .definition, "Strain"⟩
  , ⟨107, .definition, "Normal stress"⟩
  , ⟨141, .definition, "Tangential stress"⟩
  , ⟨147, .law, "Newtonian shear-stress proportionality"⟩
  , ⟨154, .definition, "Dynamic viscosity"⟩
  , ⟨201, .definition, "Steady flow"⟩
  , ⟨205, .definition, "Parallel flow"⟩
  , ⟨371, .definition, "Volume flux"⟩
  , ⟨392, .definition, "Vorticity"⟩
  , ⟨544, .definition, "Kinematic viscosity"⟩
  , ⟨643, .definition, "Material derivative"⟩
  , ⟨702, .definition, "Incompressible fluid"⟩
  , ⟨801, .definition, "Vector potential"⟩
  , ⟨820, .definition, "Streamfunction"⟩
  , ⟨834, .definition, "Streamlines"⟩
  , ⟨948, .law, "Navier-Stokes equation"⟩
  , ⟨1041, .definition, "Reynolds number"⟩
  , ⟨1054, .definition, "Dynamic similarity"⟩
  , ⟨1306, .proposition, "Euler momentum equation"⟩
  , ⟨1322, .proposition, "Momentum integral for steady flow"⟩
  , ⟨1336, .proposition, "Bernoulli's equation"⟩
  , ⟨1559, .proposition, "Vorticity equation"⟩
  , ⟨1643, .definition, "Velocity potential"⟩
  , ⟨1654, .definition, "Potential flow"⟩
  , ⟨2525, .proposition, "Euler's equation in a rotating frame"⟩
  , ⟨2531, .definition, "Coriolis parameter/planetary vorticity"⟩
  , ⟨2606, .definition, "Shallow water streamfunction"⟩
  , ⟨2676, .definition, "Potential vorticity"⟩
  , ⟨2759, .definition, "Rossby radius of deformation"⟩ ]

theorem item_count : items.length = 32 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide

def countKind (k : Kind) : ℕ := (items.filter fun x ↦ x.kind = k).length

theorem definition_count : countKind .definition = 25 := by native_decide
theorem proposition_count : countKind .proposition = 5 := by native_decide
theorem law_count : countKind .law = 2 := by native_decide

theorem kind_counts_complete :
    countKind .definition + countKind .proposition + countKind .law = items.length := by
  native_decide

end FluidDynamicsCourse.SourceAudit
