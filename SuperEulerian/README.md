# SuperEulerian

Lean project for the project-specific formalization of the super-recurrence
Eulerian proof.

This directory is tracked inside the `RealRooted` repository.  It contains the
nested Lean package, the proof blueprint, and the manuscript draft:

- `SuperEulerian/SuperRecurrenceEulerian.lean`
- `super-recurrence-eulerian.md`
- `super-eulerian-real-rootedness.tex`

The package depends on the parent reusable library:

```text
..
```

Keep general real-rootedness, interlacing, PF-polynomial, Hadamard, and
Euler-operator lemmas in the parent `RealRooted` package.  Keep the
super-recurrence rows, normalizations, kernels, manuscript notes, and final
theorem statements here.

Build from this directory in a normal checkout:

```bash
lake build SuperEulerian
```

In the shared Docker workspace, prefer the cache-aware `--packages` override
workflow from `/workspace/lean/AGENTS.md` so large dependency and build
artifacts stay under `/lake-cache`.
