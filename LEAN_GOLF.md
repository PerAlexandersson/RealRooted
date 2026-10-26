# Lean Golfing Rules

This file records the local proof-golfing style for the `RealRooted` Lean
project.  Treat it as the rulebook for cleanup passes, especially when the task
is to shorten proofs without changing mathematics.

The main sources for these rules are older cleanup PRs by Yael Dillies and
sqrt-of-2, especially the PRs that removed `omega`, adopted upstream-shaped
derivative APIs, shortened proofs with `grind`, squeezed identical branches
with `<;>`, removed redundant constructors, and cleaned unused hypotheses.

## Priorities

1. Keep the statement and proof intent clear.
2. Prefer small local changes over broad rewrites.
3. Reuse existing Mathlib/project APIs instead of introducing wrappers.
4. Avoid public API churn unless the signature cleanup is clearly useful.
5. Follow the [README verification policy](README.md#ci-and-pull-requests):
   distinguish source-checked draft checkpoints from build-verified changes.

## Good Golfing Targets

- Replace `:= by exact term` with a direct term proof:
  ```lean
  have h : P := lemma_name args
  ```
  or, for declarations with no tactic work:
  ```lean
  theorem foo : P :=
    lemma_name args
  ```
- Replace `apply lemma` plus simple bullets with a direct lemma application:
  ```lean
  exact lemma_name
    (by ...)
    h1
    h2
  ```
- Collapse repeated branches when the same tactic closes all branches:
  ```lean
  rcases h with h1 | h2 <;> simp_all
  by_cases hp : P <;> simp [hp]
  refine some_lemma ?_ ?_ ?_ <;> simp_all
  ```
- Use `grind` for local plumbing: simple contradictions, field projections,
  equality rewrites, constructor goals, and small algebraic rearrangements.
- Use `simp_all` when hypotheses and local definitions are meant to be consumed
  together.
- Use `lia` for linear arithmetic.  Do not use `omega`.
- Use `positivity` for routine positivity goals when it is stable and shorter.
- Remove redundant `left`/`right` when the remaining tactic can infer the
  disjunct from local hypotheses:
  ```lean
  rcases h with hleft | hright
  · have hscaled := ...
    lia
  · have hscaled := ...
    lia
  ```
- Remove unused variables and pattern names:
  ```lean
  rcases h with ⟨_, hg, _, _, _, _, hss_eq, hrs_eq, hshape⟩
  ```
- Split conjunction hypotheses in private/internal helpers when it removes
  repeated `.1`/`.2` projections and makes call sites clearer.
- Remove unused private hypotheses from theorem signatures when downstream
  breakage is small and the proof becomes clearer.

## API Preferences

- Prefer upstream-shaped and receiver-style APIs:
  ```lean
  p.natDegree_derivative
  (p.derivative_ne_zero).mpr h
  hp_pos.derivative h
  hnn.iterate_derivative n
  ```
  rather than project-local compatibility wrappers, when the upstream-shaped
  API is available.
- Prefer canonical list/interleaving APIs and bridge lemmas already centralized
  in `RealRooted/Basic.lean`.
- Prefer canonical iff/simp lemmas when both directions are useful; derive
  negated or one-way forms from them.
- Prefer weaker natural hypotheses such as `n ≠ 0` over `1 ≤ n` when that is
  the real condition.

## What Not To Golf

- Do not replace a readable structured proof by opaque automation if the local
  mathematical argument becomes hard to see.
- Do not add a new helper just to save one or two lines.  Add helpers only when
  they remove real duplication or match a Mathlib-shaped API.
- Do not churn public theorem signatures merely to save projections, unless the
  change is clearly internal or coordinated with the API direction.
- Do not mix unrelated formatting cleanup with proof changes.
- Do not silence linters as a golfing tactic.  Prefer fixing the issue.

## Modules

Every source file is a Lean module; README describes the layout.  When golfing or moving code:

- Keep the section header right: `public section` for a file with only theorems, notation or
  syntax, `@[expose] public section` (or `@[expose]` on single definitions) once it declares
  definitions that importers unfold.  `python3 scripts/check_module_system.py --fix` repairs a
  theorem-only header.
- Do not expose more to make a proof go through.  If a proof unfolds another file's definition,
  prefer an API lemma there (`foo_def`, `foo_apply`, a `simp` lemma) to exposing its body.
- Moving a helper into another file and keeping it `private` hides it from the old users; make it
  public under a proper name or keep it where it is used.
- Import tactic modules with plain `import`; `public import` leaks their syntax into importers.

## Build Discipline

- For a touched Lean file, run the focused module build first:
  ```bash
  lake build RealRooted.SomeModule
  ```
- For cross-module or public API changes, build the downstream target set if it
  is obvious.
- Before merging, the exact candidate revision must pass the full default
  build and the source and axiom checks required by the README:
  ```bash
  lake build
  ```
- A source-checked draft checkpoint may be pushed before compilation under the
  README's CI-first policy. Draft PRs do not automatically run the full build;
  state what remains unverified. Use the prescribed build wrapper in managed
  workspaces and serialize access to shared caches.
- Keep `git diff --check` clean.  Avoid introducing new long lines or tabs.

## Finding Slow Proofs

- `scripts/ci_module_times.py --run <id>` ranks modules by compile time from the
  build log of a CI run that rebuilt the project; `--group 1` sums by directory.
  CI times include contention between parallel jobs, so use them to rank, not to
  compare with local timings.
- `scripts/profile_heartbeats.py <file>` elaborates a temporary copy with
  `#count_heartbeats in` before each declaration and ranks the declarations.
  Set `LEAN_CMD` if the project is not built with plain `lake env lean`.
- For one slow tactic call, `set_option trace.profiler true in` on a scratch copy
  of the declaration shows which strategy attempts fail and what they cost.
  Expensive failed attempts in a search loop are the usual target.
  Never commit that instrumentation: source `set_option` remains forbidden.
