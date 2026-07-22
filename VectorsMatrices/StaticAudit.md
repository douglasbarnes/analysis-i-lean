# Static proof audit

Scope: `VectorsMatrices/**/*.lean` and `VectorsMatrices.lean`.

Forbidden proof escapes:

```text
sorry      0
admit      0
axiom      0
opaque     0
```

Coverage checks:

```text
source environments                 144
DeclarationAudit source-ID entries  144
missing IDs                           0
duplicate IDs                         0
```

The scan intentionally treats comments as non-code and searches whole words in Lean sources. Existing Mathlib axioms (classical choice, quotient soundness, and propositional extensionality) are dependencies of Lean/Mathlib rather than new axioms introduced by this formalization.
