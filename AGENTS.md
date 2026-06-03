# RealRooted Agent Guide

This guide applies to the `RealRooted` Lean project.  It supplements the
workspace Lean guide in `/workspace/lean/AGENTS.md`.

## Mathlib-Upstream Style

- The long-term goal is to upstream reusable pieces to Mathlib.  When a lemma is
  generally useful, prefer a Mathlib-shaped statement over a project-specific
  wrapper.
- Before adding a reusable lemma, ask where it would live in Mathlib, what its
  namespace-qualified name should be, and how general the statement can be
  without making the proof brittle.
- Put upstreamable compatibility lemmas in `RealRooted/Mathlib/...` using the
  corresponding Mathlib namespace and typeclass generality when practical.
  Lemmas in `RealRooted.Mathlib.X` are meant to be upstreamed to file
  `Mathlib.X` in Mathlib.
- Import the shim and use the upstream-shaped theorem instead of re-proving a
  local `RealRooted` copy.
- Prefer the owning namespace and receiver-style use, for example
  `p.natDegree_derivative h`, over bare project-local helper names.
- Prefer canonical `↔` and `[simp]` lemmas when both directions are useful, and
  derive negated forms such as `_ne_zero` from them when possible.
- Prefer weaker natural hypotheses, such as `p.natDegree ≠ 0`, over stronger
  arithmetic wrappers such as `1 ≤ p.natDegree` when the weaker form is the real
  condition.
- Avoid adding private duplicate helper lemmas across files.  If the same proof
  is needed twice, centralize it in the lowest sensible module.
- Prefer `n ≠ 0` over `1 ≤ n` when `n : Nat`.
- Mark declaration `Foo.bar` as `protected` if it is more auxiliary than
  another declaration named `Baz.bar`.

## Polynomial Derivatives

Follow Yael's `Polynomial.natDegree_derivative` extraction pattern from the
open derivative-refactor PR.

- Once the upstream-shaped shim is available, prefer
  `p.natDegree_derivative h` from
  `RealRooted.Mathlib.Algebra.Polynomial.Derivative`, where
  `h : p.natDegree ≠ 0`.
- Once the upstream-shaped shim is available, prefer
  `(p.derivative_ne_zero).mpr h`, where `h : p.natDegree ≠ 0`; derive `h`
  with `by lia` from stronger degree assumptions when needed.
- Do not reintroduce new local copies of the old
  `RealRooted.natDegree_derivative_eq`; migrate touched code toward the
  `Polynomial` namespace API when the PR is merged or checked out.
- Keep coefficient/leading-coefficient derivative positivity centralized in
  `RealRooted/Derivative.lean`:
  `HasNonnegCoeffs.derivative`, `nonnegCoeffs_derivative`, and
  `hasPosLeadingCoeff_derivative`.

## List Interleaving

- For new root-list interleaving code, prefer Mathlib's `List.Interleaves` plus
  explicit length hypotheses.
- Use the bridge lemmas in `RealRooted/Basic.lean` when interacting with the
  legacy predicates `ListInterlaces` and `ListAlternates`.

## Automation

- Do not use `omega`; use `lia` for linear arithmetic.
- Use `grind`, `simp_all`, and `positivity` for routine local plumbing when they
  keep the proof shorter and stable.

## Workflow

- Before changing files touched by an open Yael PR, inspect the PR diff and
  avoid fighting the intended API direction.
- Run focused `lake build` targets for touched Lean modules, then run full
  `lake build` before pushing Lean changes.
