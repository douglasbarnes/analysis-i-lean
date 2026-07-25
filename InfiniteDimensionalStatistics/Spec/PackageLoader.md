# Chapter specification package loader

Chapter specifications use the canonical declaration schema documented in `Schema.md`.

A chapter may be stored either as a self-contained YAML document containing top-level `inventory` and `chapter_local_dependency_dag` fields, or as a descriptor whose `package` mapping identifies inventory and DAG components.

For a multipart inventory, `package.declaration_inventory.files` lists the canonical YAML fragments in source order. The loader concatenates each fragment's top-level `inventory` list. The DAG component is identified by `package.chapter_local_dependency_dag.file` and resolves its `chapter_local_dependency_dag` mapping.

The package distinction is storage-only. Every loaded entry must satisfy the same declaration-level schema, pass semantics and source-fidelity requirements. Compact positional arrays are not accepted.

The repository validator checks component existence, declared counts, required fields, unique identifiers, pass and difficulty enums, local dependency resolution, DAG endpoints, self-loops and acyclicity.
