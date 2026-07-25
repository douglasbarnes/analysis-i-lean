# Chapter specification package loader

Every canonical chapter entry uses the readable declaration schema documented in `Schema.md`. A chapter may be stored in either of two equivalent forms.

## Self-contained form

`ChapterNN.yaml` contains a top-level `inventory` list and a top-level `chapter_local_dependency_dag` mapping.

## Descriptor form

`ChapterNN.yaml` contains a `package` mapping with:

```yaml
package:
  declaration_inventory:
    file: ChapterNN.Inventory.yaml
    entry_count: 132
  chapter_local_dependency_dag:
    file: ChapterNN.DependencyDAG.yaml
    node_count: 132
    edge_count: 262
```

For a large inventory, `declaration_inventory.files` may replace `file`:

```yaml
package:
  declaration_inventory:
    files:
      - ChapterNN.Inventory.01.yaml
      - ChapterNN.Inventory.02.yaml
    entry_count: 104
```

The loader reads inventory fragments in the listed order and concatenates their top-level `inventory` lists. Each fragment must independently be valid YAML and must contain only canonical readable declaration mappings. YAML anchors may remove repeated boilerplate inside a fragment, but they do not change the loaded schema.

The validator rejects descriptors that provide both `file` and `files`, missing components, entry-count mismatches, compact declaration/profile arrays, invalid dependency references, duplicate identifiers or cyclic DAGs.

This packaging distinction is storage-only. Acceptance criteria and declaration semantics are identical for self-contained and descriptor packages.
