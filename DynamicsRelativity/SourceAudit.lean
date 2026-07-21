import DynamicsRelativity.Core

/-!
# Source audit

The list below is an exact source-order inventory of the 86 labelled
environments in `dynamics_and_relativity.tex`.  `line` is the line at which the
environment begins in the downloaded 2015 TeX source; `target` is the compiled
Lean witness checked by `DeclarationAudit.lean`.
-/

namespace DynamicsRelativity

structure SourceItem where
  line : Nat
  kind : String
  title : String
  target : String
  deriving Repr, DecidableEq

def sourceInventory : List SourceItem := [
  ⟨57, "definition", "Particle", "Particle"⟩,
  ⟨70, "definition", "Frame of reference", "FrameOfReference"⟩,
  ⟨76, "definition", "Velocity", "velocity"⟩,
  ⟨83, "definition", "Acceleration", "acceleration"⟩,
  ⟨90, "definition", "Momentum", "momentum"⟩,
  ⟨100, "law", "Newton's First Law of Motion", "NewtonFirstLaw"⟩,
  ⟨104, "law", "Newton's Second Law of Motion", "NewtonSecondLaw"⟩,
  ⟨108, "law", "Newton's Third Law of Motion", "NewtonThirdLaw"⟩,
  ⟨116, "definition", "Inertial frames", "IsInertialFrame"⟩,
  ⟨170, "definition", "Galilean boost", "galileanBoost"⟩,
  ⟨181, "law", "Galilean relativity", "GalileanRelativity"⟩,
  ⟨201, "law", "Equation of motion", "EquationOfMotion"⟩,
  ⟨332, "definition", "Potential energy", "IsPotentialEnergy"⟩,
  ⟨348, "definition", "Total energy", "totalEnergy1D"⟩,
  ⟨356, "proposition", "Conservation of total energy", "totalEnergy1D_hasDerivAt_zero"⟩,
  ⟨450, "definition", "Equilibrium point", "IsEquilibrium"⟩,
  ⟨534, "definition", "Kinetic energy", "kineticEnergy"⟩,
  ⟨545, "definition", "Power", "power"⟩,
  ⟨551, "definition", "Work done", "work"⟩,
  ⟨558, "definition", "Conservative force and potential energy", "IsConservativeForce"⟩,
  ⟨566, "proposition", "Conservative-force energy and work", "conservative_energy_derivative_zero"⟩,
  ⟨590, "definition", "Central force", "IsCentralPotential"⟩,
  ⟨595, "proposition", "Gradient of radius", "radial_unit_norm"⟩,
  ⟨615, "proposition", "Radial form of central force", "central_force_radial"⟩,
  ⟨631, "definition", "Angular momentum", "angularMomentum"⟩,
  ⟨638, "proposition", "Angular momentum conservation", "angularMomentum_derivative_zero"⟩,
  ⟨649, "definition", "Torque", "torque"⟩,
  ⟨661, "law", "Newton's law of gravitation", "NewtonGravitationLaw"⟩,
  ⟨676, "definition", "Gravitational potential and field", "gravitationalPotential"⟩,
  ⟨698, "proposition", "Exterior potential of spherical body", "SphericalExteriorPotential"⟩,
  ⟨752, "law", "Lorentz force law", "LorentzForceLaw"⟩,
  ⟨762, "definition", "Electrostatic potential", "IsElectrostaticPotential"⟩,
  ⟨769, "proposition", "Energy in static electromagnetic fields", "magnetic_force_power_zero"⟩,
  ⟨868, "law", "Coulomb's law", "CoulombLaw"⟩,
  ⟨884, "definition", "Electric constant", "ElectricConstant"⟩,
  ⟨1039, "proposition", "Polar unit-vector derivatives", "polar_unit_vector_derivatives"⟩,
  ⟨1063, "definition", "Radial and angular velocity", "PolarVelocity"⟩,
  ⟨1110, "notation", "Angular momentum per unit mass", "specificAngularMomentum"⟩,
  ⟨1170, "definition", "Periapsis, apoapsis and apsides", "Apsides"⟩,
  ⟨1174, "definition", "Perihelion and aphelion", "Perihelion"⟩,
  ⟨1179, "definition", "Perigee and apogee", "Perigee"⟩,
  ⟨1248, "notation", "Reciprocal radius", "reciprocalRadius"⟩,
  ⟨1268, "proposition", "Binet's equation", "SatisfiesBinetEquation"⟩,
  ⟨1299, "proposition", "Kepler conic orbit", "keplerOrbit_satisfies_reciprocal"⟩,
  ⟨1307, "definition", "Eccentricity", "Eccentricity"⟩,
  ⟨1404, "law", "Kepler's first law", "KeplerFirstLaw"⟩,
  ⟨1408, "law", "Kepler's second law", "KeplerSecondLaw"⟩,
  ⟨1412, "law", "Kepler's third law", "KeplerThirdLaw"⟩,
  ⟨1513, "definition", "Angular velocity vector", "angularVelocityVector"⟩,
  ⟨1540, "proposition", "Rotating-frame derivative", "RotatingDerivativeRelation"⟩,
  ⟨1562, "proposition", "Rotating-frame equation of motion", "RotatingFrameEquation"⟩,
  ⟨1568, "definition", "Fictitious forces", "fictitiousForces"⟩,
  ⟨1724, "definition", "Total mass", "totalMass"⟩,
  ⟨1728, "definition", "Center of mass", "centerOfMass"⟩,
  ⟨1736, "definition", "Total linear momentum", "totalMomentum"⟩,
  ⟨1744, "definition", "Total external force", "totalExternalForce"⟩,
  ⟨1752, "proposition", "Center-of-mass equation", "center_of_mass_equation"⟩,
  ⟨1769, "law", "Conservation of momentum", "momentum_conserved_if_no_external_force"⟩,
  ⟨1774, "definition", "Center of mass frame", "IsCenterOfMassFrame"⟩,
  ⟨1780, "definition", "Total angular momentum", "totalAngularMomentum"⟩,
  ⟨1802, "definition", "Total external torque", "totalExternalTorque"⟩,
  ⟨1951, "proposition", "Rocket equation", "SatisfiesRocketEquation"⟩,
  ⟨1981, "definition", "Rigid body", "IsRigidBody"⟩,
  ⟨2018, "definition", "Moment of inertia of a particle", "particleMomentOfInertia"⟩,
  ⟨2041, "definition", "Moment of inertia of a rigid body", "rigidBodyMomentOfInertia"⟩,
  ⟨2048, "definition", "Angular momentum of a rigid body", "rigidBodyAngularMomentum"⟩,
  ⟨2081, "definition", "Continuum mass data", "ContinuumMassData"⟩,
  ⟨2172, "theorem", "Perpendicular axis theorem", "perpendicular_axis_theorem"⟩,
  ⟨2202, "theorem", "Parallel axis theorem", "parallel_axis_theorem"⟩,
  ⟨2612, "definition", "Lorentz factor", "lorentzFactor"⟩,
  ⟨2650, "law", "Principle of Special Relativity", "SpecialRelativityPrinciple"⟩,
  ⟨2740, "definition", "Spacetime", "MinkowskiSpacetime"⟩,
  ⟨2771, "definition", "Simultaneous events", "Simultaneous"⟩,
  ⟨2944, "definition", "Proper length", "ProperLength"⟩,
  ⟨3005, "definition", "Invariant interval", "intervalSq"⟩,
  ⟨3013, "proposition", "Lorentz invariance of interval", "lorentz_interval_invariant"⟩,
  ⟨3030, "definition", "Line element", "lineElementSq"⟩,
  ⟨3037, "definition", "Timelike, spacelike and lightlike separation", "Separation"⟩,
  ⟨3156, "definition", "Rapidity", "IsRapidity"⟩,
  ⟨3184, "definition", "Proper time", "properTimeDifference"⟩,
  ⟨3221, "definition", "Position 4-vector and 4-velocity", "positionFourVector"⟩,
  ⟨3255, "definition", "4-vector", "FourVector"⟩,
  ⟨3328, "definition", "4-momentum", "fourMomentum"⟩,
  ⟨3358, "definition", "Relativistic energy", "relativisticEnergy"⟩,
  ⟨3419, "definition", "4-force", "fourForce"⟩,
  ⟨3496, "definition", "Center of momentum frame", "IsCenterOfMomentumFrame"⟩
]

theorem inventory_count : sourceInventory.length = 86 := by native_decide

end DynamicsRelativity
