# Chapter Specification Schema

Schema version: `1.0`

A chapter specification is either:

1. a self-contained YAML file whose top level contains `source`, `inventory` and `chapter_local_dependency_dag`; or
2. a package descriptor whose `package.declaration_inventory.file` and `package.chapter_local_dependency_dag.file` point to those components.

The package loader is part of `scripts/validate_ids_specs.py`. All paths are resolved relative to the descriptor.

## Source metadata

```yaml
schema_version: '1.0'
source:
  title: Mathematical Foundations of Infinite-Dimensional Statistical Models
  authors: [Evarist Giné, Richard Nickl]
  edition: First edition (2016)
  uploaded_file: FULLPDF.pdf
  chapter: 1
  chapter_title: Nonparametric Statistical Models
  book_pages: {start: 1, end: 14}
```

## Inventory entry

Every declaration, operative example, selected exercise and later-used notes result is an inventory entry.

```yaml
inventory:
  - id: ch1.example_identifier
    kind: theorem
    book:
      number: '1.2.3'
      pages: [8, 9]
      section: '1.2.3'
      equations: []
    title: Descriptive title
    statement: Precise mathematical statement with quantifiers and constants preserved.
    hypotheses:
      explicit: []
      implicit: []
    quantifier_order: []
    constants: []
    dependencies:
      earlier_book: []
      chapter_local: []
      later_book_uses: []
    proof_status:
      delegates_to_exercises: []
      contains_omitted_steps: false
      comment: ''
    notes_status:
      discussed_or_extended_in_notes: false
      note_summary: ''
      used_later_in_book: false
    equivalents:
      mathlib:
        status: not-found
        candidates: []
        exact_equivalent: false
      repository:
        status: not-found
        candidates: []
        exact_equivalent: false
    likely_lean_representation:
      sketch: ''
      blockers: []
    difficulty: substantial
    pass: core
    issues_for_central_review: []
```

### Required entry fields

- `id`: unique stable identifier within the chapter;
- `kind`: definition, notation, construction, operative example, lemma, proposition, theorem, corollary, remark, note result or exercise;
- `book.number`, `book.pages`, `book.section`;
- `title`;
- `statement`;
- `hypotheses.explicit`, `hypotheses.implicit`;
- `quantifier_order` and `constants`;
- `dependencies.earlier_book`, `dependencies.chapter_local`, `dependencies.later_book_uses`;
- `proof_status.delegates_to_exercises`, `proof_status.contains_omitted_steps`, `proof_status.comment`;
- `notes_status.discussed_or_extended_in_notes`, `notes_status.note_summary`, `notes_status.used_later_in_book`;
- declaration-specific `equivalents.mathlib` and `equivalents.repository`, each with `status`, `candidates`, and Boolean `exact_equivalent`;
- `likely_lean_representation.sketch`, `likely_lean_representation.blockers`;
- `difficulty`;
- `pass`;
- `issues_for_central_review`.

Chapter-specific names such as `discussed_or_extended_in_section_4_5` are accepted only by the package loader as legacy aliases. New or repaired files use `discussed_or_extended_in_notes`.

## Pass and difficulty enums

```yaml
pass: core | starred | exercise
difficulty: routine | substantial | major-library | research-level
```

Pass semantics are source-based:

- `core`: unstarred main-text material;
- `starred`: material explicitly starred by the book;
- `exercise`: extracted exercise declarations.

Difficulty must not alter the pass.

## Exercise selection

An exercise entry must include at least one of:

- completes a proof omitted from the main text;
- is cited by a later result;
- establishes a required reusable lemma or counterexample.

The reasons may be recorded in `selection_reasons`; downstream declarations are recorded in `used_by` and in the DAG.

## Dependency DAG

The authoritative DAG uses inventory identifiers.

```yaml
chapter_local_dependency_dag:
  nodes: [ch1.example_identifier]
  edges:
    - from: ch1.prerequisite
      to: ch1.example_identifier
  acyclic: true
```

Every node must be an inventory identifier. Every edge endpoint must resolve. Self-loops and directed cycles are forbidden.

A separate DAG file may use JSON-compatible YAML, provided the package descriptor identifies the file and the loader produces the canonical `nodes` and `edges` view.

## Completeness metadata

Each chapter should record:

- expected and found numbered labels;
- missing numbered labels;
- duplicate identifiers;
- selected-exercise coverage;
- central-review issue count;
- inventory and DAG counts.

The validator treats any missing numbered label, duplicate identifier, dangling dependency, invalid enum, unresolved local reference or cycle as an error.
