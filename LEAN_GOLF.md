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
5. Build focused targets, then run full `lake build` before pushing Lean edits.

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
  p.natDegree_derivative h
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

## Build Discipline

- For a touched Lean file, run the focused module build first:
  ```bash
  lake build RealRooted.SomeModule
  ```
- For cross-module or public API changes, build the downstream target set if it
  is obvious.
- Before committing or pushing Lean changes, run:
  ```bash
  lake build
  ```
- Keep `git diff --check` clean.  Avoid introducing new long lines or tabs.
