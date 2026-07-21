# Part IA — Vectors and Matrices: source audit

Source: [vectors_and_matrices.tex](https://dec41.user.srcf.net/notes/IA_M/vectors_and_matrices.tex)

Status: **audited, not yet formalised**. This file records the 99 non-example declaration environments identified in the notes and the implementation order. It does not claim that any new Lean theorem has been proved.

## Coverage

| Area | Formalisation route |
|---|---|
| Complex numbers, complex exponential/trigonometry, roots of unity | Mathlib wrappers around `ℂ`, `Complex.exp`, `Complex.sin`, `Complex.cos`, `IsPrimitiveRoot` |
| Inner products, bases, spans, rank/nullity, linear maps | Mathlib finite-dimensional linear algebra |
| Cross product, scalar triple product, Levi-Civita calculations | Course-facing `Fin 3` coordinate layer over Euclidean-space and determinant APIs |
| Matrices, determinants, cofactors, inverses | Mathlib `Matrix`, determinant, adjugate and linear-map APIs |
| Eigenvalues, Cayley--Hamilton, spectral theorems | Mathlib wrappers; Jordan normal form is a separate substantial dependency |
| Quadratic forms, conics, orthogonal and Lorentz groups | Local finite-dimensional layer over spectral/matrix APIs |

## Planned Lean hierarchy

```text
CambridgeNotes/PartIA/VectorsMatrices/
  Complex.lean
  InnerProduct.lean
  CrossProduct.lean
  LeviCivita.lean
  Geometry.lean
  LinearMaps.lean
  MatrixAlgebra.lean
  Determinant.lean
  LinearEquations.lean
  Eigen.lean
  ChangeOfBasis.lean
  Diagonalization.lean
  QuadraticForms.lean
  Conics.lean
  OrthogonalGroups.lean
  Lorentz.lean
```

## Source corrections required

- The double-series diagonal rearrangement needs absolute summability (or nonnegative terms).
- The roots-of-unity geometric sum needs `n > 1`; it is false for `n = 1`.
- Complex logarithm statements must distinguish the principal logarithm from a multivalued logarithm and exclude zero where required.
- The determinant proof’s row-scaling explanation is wrong, although the stated theorem is correct.
- “Every 3x3 orthogonal matrix is a rotation or reflection” is false: determinant `-1` also permits rotoreflections.
- A sesquilinear form is two-variable; `x†Ax` is its associated quadratic expression.
- The Lorentz-boost set in the notes is the proper orthochronous 1+1 boost subgroup, not the full Lorentz group.

## Closure policy

Every course declaration will become either an exact Mathlib alias/wrapper, a locally proved theorem, or an explicitly recorded duplicate. No `sorry`, axiom, or opaque proof-hiding declaration is permitted.
