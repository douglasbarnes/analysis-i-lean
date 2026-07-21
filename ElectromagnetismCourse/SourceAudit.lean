import ElectromagnetismCourse.Core

/-! Exact ordered inventory of labelled environments in `IB_L/electromagnetism.tex`. -/

namespace ElectromagnetismCourse.SourceAudit

inductive Kind where | definition | law | proposition | theorem
  deriving DecidableEq, Repr

structure Item where
  line : ℕ
  kind : Kind
  title : String
  deriving DecidableEq, Repr

def items : List Item :=
  [ ⟨47, .definition, "Charge density"⟩
  , ⟨56, .definition, "Current and current density"⟩
  , ⟨78, .law, "Continuity equation"⟩
  , ⟨110, .law, "Lorentz force law"⟩
  , ⟨116, .law, "Maxwell's Equations"⟩
  , ⟨150, .law, "Gauss' law"⟩
  , ⟨156, .definition, "Flux through surface"⟩
  , ⟨331, .definition, "Electrostatic potential"⟩
  , ⟨378, .definition, "Dipole"⟩
  , ⟨399, .definition, "Electric dipole moment"⟩
  , ⟨459, .definition, "Field line"⟩
  , ⟨465, .definition, "Equipotentials"⟩
  , ⟨562, .proposition, "Electric-field energy"⟩
  , ⟨574, .definition, "Conductor"⟩
  , ⟨684, .law, "Ampere's law"⟩
  , ⟨831, .definition, "Vector potential"⟩
  , ⟨846, .definition, "(Coulomb) gauge"⟩
  , ⟨850, .proposition, "Existence of Coulomb gauge"⟩
  , ⟨889, .law, "Biot-Savart law"⟩
  , ⟨955, .definition, "Magnetic dipole moment (loop)"⟩
  , ⟨996, .definition, "Magnetic dipole moment (distribution)"⟩
  , ⟨1077, .definition, "Electromotive force (emf)"⟩
  , ⟨1086, .definition, "Magnetic flux"⟩
  , ⟨1093, .law, "Faraday's law of induction"⟩
  , ⟨1238, .definition, "Inductance"⟩
  , ⟨1300, .proposition, "Magnetic-field energy"⟩
  , ⟨1318, .law, "Ohm's law (circuit)"⟩
  , ⟨1323, .definition, "Resistance"⟩
  , ⟨1328, .definition, "Resistivity and conductivity"⟩
  , ⟨1339, .law, "Ohm's law (local)"⟩
  , ⟨1409, .definition, "Joule heating"⟩
  , ⟨1509, .definition, "Amplitude, wave number and frequency"⟩
  , ⟨1552, .definition, "Wave vector"⟩
  , ⟨1564, .definition, "Linearly polarized wave"⟩
  , ⟨1578, .definition, "Elliptically polarized wave"⟩
  , ⟨1649, .theorem, "Poynting theorem"⟩
  , ⟨1655, .definition, "Poynting vector"⟩
  , ⟨1807, .definition, "Orthonormal basis"⟩
  , ⟨1811, .definition, "Lorentz transformations"⟩
  , ⟨1844, .definition, "Vectors and covectors"⟩
  , ⟨1864, .definition, "Tensor"⟩
  , ⟨1877, .definition, "4-derivative"⟩ ]

def countKind (k : Kind) : ℕ := (items.filter fun item ↦ item.kind = k).length

theorem item_count : items.length = 42 := by native_decide
theorem line_numbers_are_unique : (items.map Item.line).Nodup := by native_decide
theorem definition_count : countKind .definition = 29 := by native_decide
theorem law_count : countKind .law = 9 := by native_decide
theorem proposition_count : countKind .proposition = 3 := by native_decide
theorem theorem_count : countKind .theorem = 1 := by native_decide
theorem kind_counts_complete :
    countKind .definition + countKind .law + countKind .proposition + countKind .theorem =
      items.length := by native_decide

end ElectromagnetismCourse.SourceAudit
