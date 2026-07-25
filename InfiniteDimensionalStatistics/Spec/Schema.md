# Chapter Specification Schema

Schema version: `1.0`

A chapter specification is either:

1. a self-contained YAML file whose top level contains `source`, `inventory` and `chapter_local_dependency_dag`; or
2. a package descriptor whose `package.declaration_inventory.file` and `package.chapter_local_dependency_dag.file` point to those components.

The package loader is implemented by `scripts/validate_ids_specs.py`. All component paths are resolved relative to the descriptor.

## Readable inventory packages

A package inventory component may itself be an index. An inventory index has the same source, policy, summary and completeness metadata as a normal inventory file, and adds:

```yaml
inventory_files:
  - Chapter02.Section2_1.Part1.yaml
  - Chapter02.Section2_1.Part2.yaml
```

Each listed fragment must be YAML with a top-level `inventory` list. The loader concatenates the fragments in listed order. Fragmentation is permitted only to improve reviewability; identifiers, dependency references and completeness checks remain chapter-global. A package descriptor may repeat the fragment list as non-authoritative human-readable metadata, but the inventory index is authoritative.

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

Every definition, notation, construction, lemma, proposition, theorem, corollary, mathematically operative example or remark, selected exercise, and later-used notes result is an inventory entry.

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
- `kind`;
- `book.number`, `book.pages`, `book.section`;
- `title` and a precise `statement`;
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

Chapter-specific legacy names such as `discussed_or_extended_in_section_4_5` are accepted only by the package loader. New and repaired files use `discussed_or_extended_in_notes`.

## Pass and difficulty enums

```yaml
pass: core | starred | exercise
difficulty: routine | substantial | major-library | research-level
```

Pass semantics are source-based:

- `core`: unstarred main-text material;
- `starred`: material explicitly starred in the book;
- `exercise`: extracted exercise declarations.

Difficulty must not alter the pass.

## Exercise selection

An exercise entry must include at least one selection reason:

- completes a proof omitted from the main text;
- is cited by a later result;
- establishes a required reusable lemma or counterexample.

Record the reasons in `selection_reasons`; record downstream declarations in `used_by` and in the DAG.

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

Every DAG node must be an inventory identifier. The node set must equal the inventory identifier set. Every edge endpoint must resolve. Self-loops and directed cycles are forbidden. A separate DAG file may use JSON-compatible YAML if the package descriptor identifies it and the loader produces the canonical view.

## Completeness metadata

Every chapter inventory, including an inventory index, records:

- expected and found numbered labels;
- missing numbered labels;
- duplicate identifiers;
- selected-exercise coverage;
- central-review issue count;
- inventory and DAG counts.

The validator rejects missing chapter files, missing required fields, duplicate identifiers, invalid pass or difficulty values, unresolved local references, incomplete DAG node sets, dangling edges, self-loops, cycles, missing numbered labels, or exercises without a documented selection reason.
