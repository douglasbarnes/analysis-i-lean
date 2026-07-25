# Chapter Specification Schema

## Canonical entry point

Every chapter has `ChapterNN.yaml`. The preferred form is a readable multiline document containing the inventory and dependency DAG. A package descriptor may point to separate inventory and DAG files; the common validator resolves both forms.

## Canonical declaration record

Each declaration or selected exercise must expose, directly or through the loader:

- unique `id`;
- kind;
- exact book label/number, page and section;
- precise statement;
- explicit and implicit hypotheses;
- constants and quantifier order;
- earlier-book, chapter-local and later dependencies;
- proof delegation and omitted steps;
- notes status and later use;
- declaration-specific mathlib and repository audits, each with `status`, `candidates`, and `exact_equivalent`;
- likely Lean representation;
- difficulty;
- source pass (`core`, `starred`, or `exercise`);
- central-review issues.

Exercise IDs use the `ex.` prefix. Difficulty never determines pass.

## Dependency DAG

The DAG contains every inventory ID exactly once. Edges are directed prerequisite-to-dependent. Every endpoint must exist and the graph must be acyclic.

## Accepted package forms

1. **Self-contained readable YAML:** `declarations` plus optional `exercises`, and `dependency_dag`.
2. **Chapter 4 package:** descriptor fields under `package`, inventory under the configured key, and a separate DAG file.
3. **Legacy compact Chapter 2:** readable by the loader for diagnostics only. It does not pass acceptance until converted because declaration-specific equivalence results and exact unresolved statements are required.

The validator deliberately rejects unresolved source placeholders and legacy profile-only equivalence audits.
