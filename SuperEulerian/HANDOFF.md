# SuperEulerian Handoff

## 2026-07-09 In-Repo Move

- The active Lean package has been moved from `/workspace/lean/SuperEulerian`
  to `/workspace/lean/RealRooted/SuperEulerian`.
- Manuscript assets from `/workspace/projects/DRAFT-SuperEulerian` have been
  merged into this directory: `README.md`, `super-recurrence-eulerian.md`,
  `super-eulerian-real-rootedness.tex`, `bibliography.bib`, the generated
  `.bbl`, and the checked PDF.
- The older duplicate Lean files in `/workspace/projects/DRAFT-SuperEulerian`
  were stale; that outside draft tree has been removed.  The authoritative
  Lean files are the ones now under this in-repo package.
- The nested Lake package depends on the parent `RealRooted` package by
  `path = ".."` and uses `leanprover/lean4:v4.31.0-rc2`.
- The committed manifest keeps `packagesDir = ".lake/packages"` for portable
  checkouts.  In the shared Docker workspace, use the `/workspace/lean/AGENTS.md`
  external `--packages` override workflow and a build directory under
  `/lake-cache/ai-projects/build`.

## Current Status

This package stages the Lean formalization of the proof in
`super-eulerian-real-rootedness.tex`.  The active module is:

```text
SuperEulerian/SuperRecurrenceEulerian.lean
```

The current formalization contains:

- definitions for the coefficients, row polynomials, normalized rows,
  Hadamard kernels, boundary terms, and closed-form prefixes;
- coefficient support and palindromicity lemmas for `superEulerianCoeff`;
- project-specific coefficient identities including
  `row_hadamardFactorization`, `boundary_hadamardFactorization`,
  `reciprocalBoundary_hadamardFactorization`,
  `reciprocalShift_normalizedRow_eq_X_mul`, and
  `row_succ_boundaryDecomposition`;
- kernel PF reductions for `binomialKernel` and `diagonalKernel`;
- normalized-transfer machinery proving `normalizedRow_isPF`;
- reciprocal diagonal kernel PF and kernel interlacing reductions by the
  explicit `l = 1` factorizations plus Hadamard induction;
- final reductions for row PF, consecutive interlacing, the boundary endpoint,
  and prefix interlacing.

The local `StandardFacts` type is now only an empty compatibility token.  The
Garloff-Wagner, derivative, theta-plus-one, polar-theta, and Hadamard inputs
used by the SuperEulerian proof are supplied by proved declarations in the
parent `RealRooted` package.

## Verification

Focused nested build after the in-repo move passed:

```text
ELAN_TOOLCHAIN=leanprover/lean4:v4.31.0-rc2 LAKE_JOBS=2 \
  lake -f /tmp/SuperEulerian-lakefile...toml \
  --packages /tmp/SuperEulerian-package-overrides...json \
  -KbuildDir=/lake-cache/ai-projects/build/SuperEulerian-nested-1783599318 \
  build SuperEulerian
```

The build replayed the existing `RealRooted` warning modules with known
`sorry` warnings, then built:

```text
SuperEulerian.SuperRecurrenceEulerian
SuperEulerian
```

The current source scan found no line-level `sorry`, `admit`, `omega`, or
`axiom` tokens in the active SuperEulerian module.

## Next Safe Actions

- If continuing cleanup, remove or inline the now-empty `StandardFacts`
  parameter only after the nested build is green.
