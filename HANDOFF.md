# RealRooted Handoff

## Active: mixed Euler compatibility for derangement descents, 2026-09-01

- Sole Lean/Lake worker: the current Codex derangement formalization session,
  as explicitly confirmed by the user.
- Isolated worktree: this directory, on branch
  `proof/derangement-mixed-euler-20260901`, based at public `41ce000a`.
- Exact owned source files:
  `RealRooted/EulerianMixedCompatibility.lean`, the corresponding single
  import line in `RealRooted.lean`, and this handoff file.
- Mathematical target: an assumption-free, common-root-safe proof that the
  adjacent Euler operators `T_n` and `U_(n+1)` send a nonnegative
  nonpositive-root `Prec` pair to a compatible output pair.  Supporting
  zero/positive-constant Euler preservation and any general closure theorem
  required by the proof also belong in the new module.
- No other shared or architecture-worktree file is owned.  No push or PR is
  authorized.

### Verified progress

- Checkpoint `4a372384` introduced the Euler insertion operator, coefficient
  formulas, degree and positive-leading-coefficient control, nonnegative
  coefficient preservation, and `Prec`/`Splits`/compatibility preservation.
- The current increment formalizes the partial-fraction comparison underlying
  the mixed `T`/`U` lemma and proves the no-common-root case, including the
  degree-one boundary where the candidate paper's strict limit argument does
  not apply verbatim.
- Focused verification: `lake-workspace build
  RealRooted.EulerianMixedCompatibility` succeeds without source warnings.
- Remaining general-theory task: discharge common roots and package the mixed
  result as output compatibility.  Then the OEIS worktree can import this
  module for the sequence-specific induction.
