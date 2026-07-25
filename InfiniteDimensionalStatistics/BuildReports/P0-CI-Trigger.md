# P0 Clean-Build Trigger

This branch is based on the current `main` and exists solely to run the repository's standard Lean workflow:

1. install the pinned Lean toolchain;
2. `lake update`;
3. retrieve the mathlib cache;
4. run the full `lake build`;
5. run `scripts/check_audit.py`;
6. run the Analysis II baseline correctness audit.

The result will be recorded in `InfiniteDimensionalStatistics/BuildReports/P0.md`; this trigger file is not intended for the final project tree.
