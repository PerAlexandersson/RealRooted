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
