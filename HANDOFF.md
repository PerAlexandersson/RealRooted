# RealRooted Handoff

## Active: mixed Euler compatibility for derangement descents, 2026-09-01

- Sole Lean/Lake worker: the current Codex derangement formalization session,
  as explicitly confirmed by the user.
- Isolated worktree: this directory, on branch
  `proof/derangement-mixed-euler-20260901`, based at public `41ce000a`.
- Exact owned source files:
  `RealRooted/EulerianMixedCompatibility.lean`, the corresponding single
  import line in `RealRooted.lean`, and this handoff file.  For the final
  repository-boundary cleanup, this worker additionally owns the new general
  modules
  `RealRooted/BorceaBranden/Applications/AffineFiniteSymbol.lean`,
  `RealRooted/BorceaBranden/Applications/EulerFiniteSymbol.lean`, and
  `RealRooted/EulerianCompletion.lean`, plus their umbrella imports.
- Mathematical target: an assumption-free, common-root-safe proof that the
  adjacent Euler operators `T_n` and `U_(n+1)` send a nonnegative
  nonpositive-root `Prec` pair to a compatible output pair.  Supporting
  zero/positive-constant Euler preservation and any general closure theorem
  required by the proof also belong in the new module.
- No other shared or architecture-worktree file is owned.  The user explicitly
  authorized committing and pushing this RealRooted branch on 2026-09-01; no
  PR creation or merge is authorized by that instruction.

- Completion-audit correction, 2026-09-01: the checked crossed-completion
  theorem is reusable operator theory and therefore must not remain
  implemented in the OEIS repository.  The finite-symbol bridge, Euler
  finite-symbol theory, and crossed-completion theorem have now been promoted
  to this worktree; the OEIS copies are thin compatibility imports and retain
  only sequence-specific induction code.

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
- The common-root case is now discharged without a genericity hypothesis.
  `mixedEulerStep_splits` uses nonnegative derivative regularization plus the
  monic coefficient-limit theorem, and
  `compatible_eulerInsertionStep_one_zero_succ` packages all nonnegative
  mixtures, including both endpoint cases.
- Focused verification after this increment: `lake-workspace build
  RealRooted.EulerianMixedCompatibility` succeeds without source warnings;
  the module contains no `sorry`, `admit`, or added axiom.
- The exported compatibility theorem is complete, but the candidate paper's
  crossed-completion proof has a separate orientation gap.  It treats
  compatibility of `T_n h'` with each target as if it proved that the
  *specific polynomial* `T_n h'` is a common left interlacer.  Compatibility
  alone does not imply this: `1 + X` is compatible with
  `6 + 5*X + X^2`, since every nonnegative combination has discriminant
  `alpha^2 + 6*alpha*beta + beta^2 >= 0`, but the roots `-1` and `-2,-3` do
  not interlace in the required orientation.  Thus the sequence proof needs a
  new theorem exploiting its special derivative/Euler structure; it cannot be
  completed merely by invoking `compatible_eulerInsertionStep_one_zero_succ`.
  This is not a defect in the checked mixed compatibility theorem and not a
  counterexample to the derangement theorem.
- The orientation gap is now closed in `RealRooted/EulerianCompletion.lean`.
  For `L_M p = M p + (1-X)p'`, its genuine degree-`D` finite symbol is
  `(x+y)^(D-1) ((M-D)x + M y + D)`, which is stable for `D < M`.
  This directly proves oriented preservation of `L_M`, the derivative-to-zero
  Euler relation, and the four-output common-left-interleaver theorem without
  a reciprocal boundary split.  `lake-workspace build
  RealRooted.EulerianCompletion` succeeds for all 8742 jobs; direct Lean checks
  of the three promoted modules also succeed.
