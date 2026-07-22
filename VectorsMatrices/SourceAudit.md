# Part IA Vectors and Matrices — source audit

Source: `IA_M/vectors_and_matrices.tex`, retrieved from Dexter Chua's lecture notes on 2026-07-21.

The earlier audit stopped at the 99th environment (minor and cofactor, TeX line 1568). That was not the end of the file. A fresh mechanical scan of every non-example mathematical environment gives **144** entries:

| TeX environment | Count |
|---|---:|
| `defi` | 78 |
| `thm` | 32 |
| `prop` | 25 |
| `cor` | 4 |
| `notation` | 3 |
| `lemma` | 2 |
| **Total** | **144** |

The stable, source-ordered inventory is the numbered `#check` table in `DeclarationAudit.lean`. Every integer from `001` through `144` occurs exactly once. The module split is:

| IDs | TeX material | Lean module |
|---:|---|---|
| 001–061 | complex numbers; real and complex vectors; suffix notation; vector geometry; linear maps | `ComplexVectors.lean` |
| 062–106 | matrix operations; transpose; matrix classes; permutations; determinant; inverse; rank | `Matrices.lean` |
| 107–144 | fundamental theorem of algebra; eigenvalues; similarity; canonical forms; Hermitian and normal matrices; quadrics; orthogonal and Lorentz groups | `EigenGeometry.lean` |

Examples, worked calculations, exercises, remarks, and unnumbered prose claims were excluded. Definitions containing several inseparable introduced notions (for example modulus/argument and orthogonal/unitary) have one audit ID, matching their single TeX environment, while Lean may introduce more than one declaration.

## Coverage invariant

`DeclarationAudit.lean` is the authoritative declaration-level closure table. It imports all implementation modules and has exactly 144 source-ID comments. Consequently a successful build checks both that every mapped declaration exists and that every proof term elaborates without `sorry`.
