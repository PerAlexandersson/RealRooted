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

## Names, Hypotheses and Deprecation

- Name a theorem after its conclusion, in snake_case built from the conclusion's
  constants, with hypotheses after `_of_`.  Put closure and preservation lemmas
  in the predicate's namespace for dot notation (`IsPFPolynomial.thetaPlusOne`,
  `Interl.derivative`) rather than `fooPreservesPF` or `foo_preserves_pf`.
- Spell predicates as they are defined (`hasNonnegCoeffs`,
  `hasPosLeadingCoeff`, `isPolyaFreqSeq`, `strictInterl`); in names,
  `isRealRooted` means `p ≠ 0 ∧ p.Splits`.  Prop-valued definitions are
  UpperCamelCase and data-valued definitions lowerCamelCase (`tDeriv`,
  `idTransform`); a composite definition keeps its own camel case inside other
  names (`iterateTDeriv`).
- Keep paper, author, and theorem-number tags (`_mw_`, `_lw_`, `gw`,
  `theorem21`, `Theorem26`) and workflow words (`Internal`, `Backend`, `Legacy`,
  `Hyp`, `Bridge`, `Statement`, `_aux`, `_core`) out of public names.  Use a
  namespace named after the paper or object (`RealRooted.MaWang`,
  `RealRooted.BrandenSolus`), cite the source in the docstring, and make
  genuine helpers `private`.
- Do not open a Mathlib namespace inside `RealRooted` or add another root
  namespace; upstream-shaped lemmas go in their Mathlib namespaces under
  `RealRooted/Mathlib/`.
- Keep public leaf names to roughly 60 characters; introduce a predicate or a
  namespace instead of a longer name.
- Do not keep an explicit hypothesis the proof does not use, and do not silence
  the unused-variable linter by renaming it `_h`: drop it and update the
  callers.  If downstream code uses the old signature, add the new statement
  under a new name and deprecate the old one.
- When a general theorem lands, delete its finite-case versions
  (`foo_of_le_three`) and routes that only fed them, unless a caller, the
  catalog, or a result stated on symmetricfunctions.com needs them.
- A rename updates every in-repository caller in the same change, including
  macro quotations and `export` lists, which do not trigger deprecation
  warnings.  Add `@[deprecated (since := "YYYY-MM-DD")] alias` only for names
  used by downstream projects, and remove those aliases once the downstream
  pins have moved past them.

## Proof Status, Scaffolds and Assumption Boundaries

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
- A theorem containing `sorry`, or obtained from an added axiom with the same
  content, is still unproved.  Do not present such a declaration as resolving a
  proof issue.
- Do not remove an explicit backend hypothesis from tactics or downstream
  theorems until a checked, assumption-free witness has replaced it.
- When an external mathematical fact is intentionally left as an explicit
  hypothesis, add a nearby comment explaining why that boundary is acceptable.
  Typical acceptable boundaries are a documented combinatorial model identity
  whose full model is out of scope, or a clearly cited classical theorem whose
  formalization is tracked separately.  The comment should also make clear that
  the desired real-rootedness conclusion is derived from formalized recurrences
  or stability lemmas rather than assumed directly.
- In issues, pull requests, and handoffs, distinguish explicitly between a
  statement scaffold, an admitted theorem, and a fully checked proof.

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
  `RealRooted/Derivative/Algebra.lean`: `HasNonnegCoeffs.derivative` and
  `HasPosLeadingCoeff.derivative`.

## List Interleaving

- For new root-list interleaving code, prefer Mathlib's `List.Interleaves` plus
  explicit length hypotheses.
- Use the bridge lemmas in `RealRooted/Basic.lean` when interacting with the
  legacy predicates `ListInterlaces` and `ListAlternates`.

## Automation

- For proof-golfing and cleanup passes, follow `LEAN_GOLF.md` as the local
  rulebook.  The batch helpers live in `scripts/golf/`: `dupscan.py` and
  `dupbody.py` find duplicate statements and proof bodies, `grind_candidates.py`
  lists small tactic proofs, and `golf_driver.sh` trials a replacement tactic
  file by file and keeps only what still elaborates.
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
  validated using Lake, locally or in the README's CI-first draft-PR workflow.

## Workflow

- Before changing files touched by open PRs, inspect the PR diffs to avoid
  conflicting with the intended API direction.
- Prefer focused Lake builds for touched Lean modules when a local build owner
  is available; never contend for a shared build cache.
- Follow README's CI-first draft-PR policy: source-checked feature-branch
  commits may precede remote compilation, but must be labeled unverified until
  the exact revision passes the full default build and applicable axiom audits.
- Keep parallel workers on disjoint files and isolated branches. One integrator
  reviews and merges verified work; a draft checkpoint is not proof completion.
