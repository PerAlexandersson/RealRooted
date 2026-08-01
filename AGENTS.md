# RealRooted Agent Guide

> [!IMPORTANT]
> **Precedence and Guidelines:**
> 1. Before reading or acting on this guide, read [README.md](README.md) first.
>    The instructions and guidelines in [README.md](README.md) take absolute
>    precedence over this file.
> 2. Do **not** add any of the following to this guide (`AGENTS.md`):
>    * Environment-specific paths (e.g., references to directories outside
>      the repository like `/workspace/` or `/lake-cache/`).
>    * System environment files or variables (e.g., sourcing `/usr/local/lib/`
>      files or referencing API keys).
>    * API key handling instructions, security warnings, or credentials.
>    * Sandbox/Docker-specific workarounds or parallel worker tag settings.
>    * Highly specific references to individual contributors or specific
>      transient pull request branches.
> Keep this document generic, clean, and focused solely on development
> guidelines for agentic coding assistants.

This guide applies to the `RealRooted` Lean project.

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

## Proof Status and Statement Scaffolds

- A declaration `def FooStatement : Prop := ...` defines a proposition; it does
  not prove that proposition.
- Do not introduce a new `...Statement : Prop` as a substitute for proving a
  theorem. If a temporary statement scaffold is genuinely needed, its docstring
  must call it an unproved target and the same change must link an open GitHub
  issue that tracks the missing proof.
- Never report a statement scaffold as proved merely because it compiles or is
  consumed by conditional theorems. A proof-status claim must name a checked
  witness such as `theorem foo : FooStatement := by ...` that does not assume
  `FooStatement` itself.
- When a scaffold is discharged, document the witness theorem next to the
  scaffold or replace the scaffold with a direct theorem API when practical.
  Downstream interfaces should use the checked witness rather than continue to
  require the proved statement as a caller-supplied hypothesis.

## Polynomial Derivatives

Follow the `Polynomial.natDegree_derivative` extraction pattern.

- Prefer using `p.natDegree_derivative` from
  `RealRooted.Mathlib.Algebra.Polynomial.Derivative` (which has the signature
  `p.derivative.natDegree = p.natDegree - 1` and does not require a degree
  non-zero hypothesis).
- Prefer using `(p.derivative_ne_zero).mpr h` (or
  `Polynomial.derivative_ne_zero.mpr h`), where `h : p.natDegree ≠ 0`; derive
  `h` with `by lia` from stronger degree assumptions when needed.
- Do not reintroduce new local copies of the old
  `RealRooted.natDegree_derivative_eq`; migrate touched code toward the
  `Polynomial` namespace API.
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

- For proof-golfing and cleanup passes, follow `LEAN_GOLF.md` as the local
  rulebook.
- Do not use `omega`; use `lia` for linear arithmetic.
- Use `grind`, `simp_all`, and `positivity` for routine local plumbing when they
  keep the proof shorter and stable.

## External Proving Assistants

When using Lean-specific external proving assistants (such as Aristotle,
Leanstral, or Axle) to help with proof-golfing, deduplication reviews,
theorem-shape suggestions, or proof repairs:
- Keep assistant queries and requests small and self-contained.
- Review and verify all suggested proof patches manually before applying them
  to the codebase.
- Test isolated snippets and candidate proof steps within the assistant's
  scratch environment first.
- All suggested results are advisory; every proof modification must be fully
  validated locally using Lake.

## Workflow

- Before changing files touched by open PRs, inspect the PR diffs to avoid
  conflicting with the intended API direction.
- Run focused Lake builds for touched Lean modules to verify changes quickly.
- Run a full Lake build and check for warnings before pushing or committing
  Lean changes.
