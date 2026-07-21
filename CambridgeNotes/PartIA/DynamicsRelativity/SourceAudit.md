# Part IA — Dynamics and Relativity: source audit

Source: [dynamics_and_relativity.tex](https://dec41.user.srcf.net/notes/IA_L/dynamics_and_relativity.tex)

Status: **audited, not yet formalised**. The source has 86 non-example declaration environments: 54 definitions, 13 physical laws/model rules, 15 propositions, 2 theorems, and 2 notations.

## Formalisation principle

Newton's laws, gravitation, Coulomb's law, the Lorentz force, and special-relativity postulates are not theorems of mathematics. They will be expressed as hypotheses/predicates of a model or trajectory, with every mathematical consequence proved conditionally. This introduces no new axioms.

## Planned Lean hierarchy

```text
CambridgeNotes/PartIA/DynamicsRelativity/
  Euclidean3.lean
  Calculus.lean
  Newton.lean
  Orbits.lean
  RotatingFrames.lean
  ParticleSystems.lean
  RigidBodies.lean
  Minkowski.lean
  SpecialRelativity.lean
```

## Dependencies and staged closure

1. Euclidean three-space, cross products, finite sums, and trajectory calculus.
2. Newtonian models, energy/work/potential identities, and central-force angular momentum.
3. Finite particle systems, centre-of-mass formulae, and discrete rigid-body identities.
4. Minkowski bilinear form, Lorentz boosts, invariant interval, and proper-time kinematics.
5. Binet/Kepler, rotating frames, continuous densities/Newton potentials, and model-dependent electromagnetic/particle-physics applications.

## Source corrections required

- Energy/work sign: work by `F = -∇V` is `V(start) - V(end)`.
- Radial-gradient and polar-coordinate formulas must exclude the origin; one polar-force sign in the source is wrong.
- The inverse-square potential must be `-mk/r`, not `+mk/r`.
- Kepler's first law applies to bound noncollision inverse-square orbits, not every such trajectory.
- The centre-of-mass-coordinate equation has a sign error.
- Proper time is defined only for timelike worldlines.
- `P = mU` does not define massless-particle momentum; future null momentum needs an independent definition.
- A centre-of-mass frame exists precisely when total four-momentum is future timelike.
- The particle-decay and Higgs-momentum examples contain index/sign typos.

## Closure policy

Course statements are formalised only as Mathlib reuse or complete local proofs. Empirical laws remain parameters of formally specified models; no `sorry`, axiom, or opaque proof-hiding declaration is permitted.
