# SuperEulerian Lean Agent Guide

This guide applies to `/workspace/lean/RealRooted/SuperEulerian`.

## Scope

- This is the project-specific Lean package for the super-recurrence Eulerian
  proof.
- The paper blueprint and manuscript draft now live in this directory:
  `super-recurrence-eulerian.md` and `super-eulerian-real-rootedness.tex`.
- Reusable real-rootedness infrastructure belongs in the parent `RealRooted`
  package; the dependency path is `..`, and source modules live under
  `../RealRooted`.
- Project-specific definitions and proof obligations belong under the
  `SuperEulerian` namespace in this package.

## Build

For CI or a local checkout where project-local `.lake` output is acceptable,
run from this directory:

```bash
lake build SuperEulerian
```

Inside the shared Docker workspace, follow `/workspace/lean/AGENTS.md` and use
external package/build overrides instead of materializing a large local
`.lake/` tree.  Use `grind`, `simp_all`, `lia`, and `positivity` where
appropriate, and do not use `omega`.
