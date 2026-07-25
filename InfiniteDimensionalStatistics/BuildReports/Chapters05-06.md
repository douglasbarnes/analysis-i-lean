# Chapters 5 and 6 Specification Audit

Date: 2026-07-25  
Pull request: `#60`  
Canonical audit workflow run: `30159743985`

## Chapter 5

- inventory entries: 104
- dependency edges: 141
- canonical migration audit: **pass**
- strict source-transcription audit: **blocked**
- pass semantics: seven declarations in source-starred Section 5.1.3 retain `pass: starred` and record `source_starred: true`

Strict blockers:

- `ch5.def.D_class`
- `ch5.prop.5_1_21`
- `ch5.def.quadratic_white_noise`
- `ch5.thm.5_3_1`
- `ch5.thm.5_3_2`
- `ch5.def.weighted_quadratic`
- `ch5.thm.5_3_3`
- `ch5.def.general_integral_estimator`
- `ch5.thm.5_3_4`
- the exact individual displays `(5.9)–(5.11)` in `ch5.eq.5_9_5_11`

No source blocker was silently repaired. Chapter 5 remains `needs_revision`.

## Chapter 6

- inventory entries: 83
- declarations: 70
- selected exercises: 13
- dependency edges: 140
- numbered-label coverage: complete
- canonical migration audit: **pass**
- strict source-transcription audit: **pass**
- source-starred entries: 0
- central-review flags: 22

`Chapter06.Inventory.12.yaml` contained invalid YAML escaping in a double-quoted scalar. The repair changed only transport-level backslash encoding; the mathematical string was not rewritten.

## Validator/schema change

The canonical schema now permits `source_starred: true` when the book stars an enclosing section rather than repeating a star on every declaration label. The validator also reads nested `source_fidelity.transcription_status` values and enforces descriptor-level `blocking_source_transcriptions` in strict mode.
