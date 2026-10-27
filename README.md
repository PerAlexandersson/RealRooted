# RealRooted

`RealRooted` is a Lean 4 library about real-rooted univariate polynomials and
the tools used to prove real-rootedness: interlacing, compatibility and common
interleavers, Pólya-frequency sequences, stability, and linear preservers. It
also contains many combinatorial applications.

**[Browse the theorem catalog](https://peralexandersson.github.io/RealRooted/)**
for readable statements of the completed results, with their Lean names,
references, and source links.

It is a research formalization workspace rather than a polished Mathlib
contribution. Every named theorem is checked by Lean. We aim to upstream stable,
reusable pieces to Mathlib over time.

- [`ARCHITECTURE.md`](ARCHITECTURE.md) describes the module layers, import
  budgets, and module-splitting rules.
- [`AGENTS.md`](AGENTS.md) and [`LEAN_GOLF.md`](LEAN_GOLF.md) give development
  and proof-cleanup conventions.
- [`docs/WORKHORSES.md`](docs/WORKHORSES.md) is a generated lemma-search aid;
  regenerate it with `python3 scripts/lemma_index.py` when needed.
- [`website/README.md`](website/README.md) documents catalog maintenance.

## Build

The toolchain and dependency versions are pinned in
[`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), and
[`lake-manifest.json`](lake-manifest.json). The commands below apply to a
standalone checkout; managed workspaces should use their prescribed build
wrapper and shared-cache policy.

```bash
lake exe cache get
lake build                              # default target, as in CI
lake build RealRooted.Production        # library without tactic regressions
lake build RealRooted.Tactic.Examples   # tactic regression suite
lake build RealRooted.Hadamard          # any single module
```

The default build covers the broad `RealRooted` umbrella, `Production`, and the
tactic regressions. For an independent kernel re-check and axiom audit of the
comparator theorem surface, run `./verify.sh` on x86_64 Linux or
`./verify_docker.sh` elsewhere. Pinned tool versions are in
`comparator/versions.env`. These scripts complement `lake build`; they do not
replace it.

## Layout

- `RealRooted.lean` is the broad compatibility umbrella. `RealRooted/Production.lean`
  imports every non-regression module, and `RealRooted/Tactic/Examples.lean`
  is the mandatory tactic regression umbrella.
- `RealRooted/Mathlib/` holds upstream-shaped lemmas. `RealRooted.Mathlib.X`
  is meant for Mathlib's `Mathlib.X`.
- `RealRooted/Challenges/` holds short entry points, one per completed result,
  in topical subfolders (`Interlacing`, `Roots`, `Preservers`, `Stability`,
  `PolyaFrequency`, `Matrices`, `Orthogonal`, `Graphs`, `Combinatorial`). The Lean
  namespace stays `RealRooted.Challenges.<Name>`. They feed the public catalog (see
  [Documentation](#documentation)).
- `RealRooted/Tactic/` holds the real-rootedness and interlacing tactics.
  [`RealRooted/Tactic/ROUTES.md`](RealRooted/Tactic/ROUTES.md) lists the row-tactic routes,
  their theorems, and side conditions.  Use `set_option rr.row.explain true` to print the
  attempted routes and `rr.row.explain.heartbeats false` to hide heartbeat counts.
  [`RealRooted/Tactic/OEIS_COVERAGE.md`](RealRooted/Tactic/OEIS_COVERAGE.md)
  is the generated ledger of OEIS certificate coverage.
- Theory lives in topic directories such as `CommonInterleaver/`,
  `Hadamard/`, `BorceaBranden/`, `MultiplierSequence/`, `LGV/`, and
  `Wronskian/`. Concrete families live in `CombinatorialExamples/` and
  `Applications/`.

## Main concepts

- `Interlaces f g`: nonzero real-rooted polynomials with degree gap one and
  weakly interleaving roots.
- `StrictInterl f g`: oriented interlacing for nonzero real-rooted polynomials,
  allowing equal degrees or a degree gap of one. Despite the name, repeated
  and shared roots are allowed.
- `Interl f g`: the zero-aware extension of `StrictInterl`.
- `p = 0 ∨ p.Splits`: the zero-aware real-rootedness convention for closure
  statements.
- `IsGeneralizedSturmSeq`, `IsInterlacingSeq`, `IsInterlacingSeq0`:
  list-level Sturm and interlacing sequences.
- `Compatible`, `PairwiseCompatible`, `FamilyCompatible`: compatibility in the
  sense of Chudnovsky and Seymour.
- `HasCommonInterleaver`, `HasCommonLeftInterleaver`: common interleavers of
  finite families.
- `AllComboRealRooted f g`: every real linear combination is zero or
  real-rooted.
- `IsPolyaFreqSeq a`: the Toeplitz matrix of `a` is totally nonnegative.

## Selected results

The [catalog](https://peralexandersson.github.io/RealRooted/) is the full,
curated list. Some representative checked theorems:

- **Interlacing basics.** Rolle (`derivative_interlaces`), Wagner's lemmas
  (`Challenges.Wagner`), Obreschkoff's theorem
  (`allComboRealRooted_of_strictInterl`, `strictInterl_of_allComboRealRooted`),
  and Favard sequences (`favardInterlacing`).
- **Matrices.** Cauchy interlacing (`cauchy_interlacing`), principal
  interlacing for totally nonnegative matrices
  (`Matrix.IsTotallyNonneg.leading_charpoly_interlaces`), and the Bezoutian
  criterion (`strictInterlSameDegree_iff_bezoutMatrix_posDef`).
- **Preservers.** Interlacing preservers (`operatorPreservesInterlacingPairsUpToOrder`),
  matrix preservers (`matrix_preserves_interlacing_seq`), the finite
  Borcea–Brändén classification (`Challenges.BorceaBranden`), Garloff–Wagner
  Hadamard products (`Challenges.Hadamard.interl_hadamardProduct_of_strictInterl`), and the
  Mao–Wang Narayana transformation (`narayanaTransformPreservesPF`).
- **Pólya frequency.** The reverse Aissen–Schoenberg–Whitney theorem
  (`aissenSchoenbergWhitney_reverse`), Veronese sections
  (`isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`),
  and the Type-I Pólya–Schur classification
  (`isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction`).
- **Compatibility.** Liu's opposite-leading-sign theorem
  (`compatible_iff_rootCountBranchesWithCommon`) and the Chudnovsky–Seymour
  common-interleaver theory (`Challenges.ChudnovskySeymour`).
- **Graphs.** Claw-free independence polynomials
  (`Graph.clawFree_indepPoly_splits`), acyclic sink polynomials
  (`UnitIntervalGraph.acyclicSinkPolynomial_splits`,
  `Graph.allOrientationSinkPolynomial_splits_of_clawFree`), and minima
  polynomials (`Graph.minimaPolynomial_splits`).
- **Eulerian compendium.** `Challenges.EulerianCompendium` collects all eight
  main theorems in paper order, with public enumeration definitions and proofs
  for derangement descents, balanced cyclic words, even-top descents,
  super-Eulerian polynomials, ternary runs, peaks and zig-zag swaps.
- **Zig-zag Eulerian polynomials.** The actual alternating-permutation swap
  enumerators have exact degree and distinct negative roots
  (`ZigzagEulerian.zigzagEulerianPolynomial_roots`). The word recurrence,
  standardization identity, centered root bound and differential-operator
  transfer are proved in the library.
- **Combinatorial families.** Eulerian and type-B Eulerian polynomials
  (`Challenges.Eulerian`), generalized snake posets
  (`snakeInterlacing_generalizedSnakeRookModel`), peak-value enumerators
  (`peakValuePolynomial_mvRealStable`), the A16634x gamma pencil
  (`gammaU_strictInterl_gammaV`), and the Jacobi deformation and OEIS A132885
  (`JacobiDeformation.polynomial_strict_package`).

Open problems and proof tasks are tracked in
[GitHub issues](https://github.com/PerAlexandersson/RealRooted/issues), not in
this file.

## Contributing

### Proof status

- `sorry`, `admit`, and source `axiom` commands are not accepted as proofs.
  Track an unproved result in a GitHub issue.
- A temporary `...Statement : Prop` interface is allowed only when it is
  genuinely useful. Its docstring must identify it as an unproved target and
  link the tracking GitHub issue. Keep it out of production theorem dependencies.
- Keep a known-false candidate interface only when it helps diagnosis, and
  then only next to its checked negation. Any reduction through such an
  interface must take it as an explicit hypothesis and document that the route
  is uninhabited.

### Code rules

- Follow the Lean community style guide and Mathlib naming conventions. Keep
  declarations explicit, prefer small reusable lemmas, and keep top-level
  declarations flush-left.
- Code on the default branch must build without warnings. The lakefile sets
  `warningAsError`.
- `set_option` is forbidden. Fix warnings, lint errors, and resource limits in
  the proofs and definitions instead of suppressing them.
- `try`, `all_goals`, and `any_goals` are forbidden in proofs. They remain
  allowed inside `macro`, `macro_rules`, `elab`, and `elab_rules` tactic
  implementations. Use structured case analysis or sequential composition.
- `simp +decide` and `simp_all +decide` are forbidden.
- Use `lia`, not `omega`. A goal that `lia` cannot close may use `omega` only
  when its declaration is listed in `ALLOWED_OMEGA` in
  `scripts/check_proof_status.py`.
- Keep `lakefile.toml` and `lake-manifest.json` free of absolute paths. The
  relative `.lake/packages` and `.lake/build` paths must keep working
  out of the box.

### Checks

```bash
python3 scripts/check_root_imports.py --fix        # register a new module (imports stay sorted)
python3 scripts/check_import_architecture.py       # import graph, layers, budgets
python3 scripts/check_proof_status.py --self-test
python3 scripts/check_proof_status.py              # sorry/axiom/tactic rules, open statements
python3 scripts/check_upstream_headers.py          # Mathlib file headers in RealRooted/Mathlib
python3 scripts/check_module_system.py             # every file is a Lean module (allowlist shrinks)
lake exe lint-style                                # Mathlib text style: whitespace, `;`, unicode
lake exe runLinter RealRooted                      # Mathlib environment linters (after `lake build`)
```

Source files use the Lean module system, following Mathlib's conventions:

- After the copyright comment comes `module`, then the `public import`s and the module
  docstring.  `python3 scripts/modularize.py FILE` converts a new file to this layout.
- A file that declares definitions opens `@[expose] public section`, so importers can unfold them
  (`rfl`, `decide`, `simp [foo]`).  If only some bodies need to be visible, use `public section`
  and put `@[expose]` on those definitions.  A file with only theorems, notation or syntax opens
  `public section`: theorem bodies are never exported, so exposing it changes nothing.
  `scripts/check_module_system.py` enforces this (`--fix` rewrites the header).
- Theorem bodies are not exported, so editing a proof does not rebuild the files that import it;
  editing an exposed definition does.  Prefer stating API lemmas (`foo_def`, `foo_apply`, `simp`
  lemmas) over unfolding another file's definitions.
- A `private` declaration is invisible to other files, including tactic expansions there.
  Elaborators, `initialize` and simp-set registrations go in a `public meta section`, and tactic
  modules are imported with plain `import`, so their syntax does not leak into importers.
- Use `public import` only for modules whose declarations appear in the file's public
  statements or exposed definitions; a module needed only inside proofs is a plain `import`.
  Plain imports are not re-exported, so changing the interface of a proof-only dependency does
  not rebuild this file's importers (#2086).  `lake shake` lists imports that can be downgraded
  or dropped.  Shake cannot see names inside syntax quotations: a tactic module whose macro
  expands to a theorem must `public import` the module that declares it.
- A module can only import modules.  Files that cannot be modules yet are listed in
  `scripts/non_module_files.txt` (#2016), and that list may only shrink.

Files under `RealRooted/Mathlib/`, the upstream targets, carry Mathlib's file header: the
copyright block (`Copyright (c) YYYY Names. All rights reserved.`, the Apache 2.0 line and
`Authors: Names`), then `module` and the imports, then the module docstring `/-! ... -/`.

The last two commands are Mathlib's own lint checks, and CI runs both. `lint-style --fix` repairs
whitespace and semicolons. `runLinter` runs the Batteries and Mathlib environment linters
(`docBlame`, `simpNF`, `unusedArguments`, `defsWithUnderscore`, …) on every declaration.
Existing findings are listed in the baseline `scripts/nolints.json`. New code must not add
entries; when you fix a listed declaration, remove its entry (`lake exe runLinter --update
RealRooted` rewrites the file; check that the diff only removes lines).

The import guards check the broad, production, and regression umbrellas
separately, and reject production closures that contain tactic examples. The
proof-status guard also reports theorem-shaped propositions referenced only by
their definition for review. Document assumptions and checked counterexamples
beside their declarations; track missing proofs in GitHub issues.

### CI and pull requests

- A small, independently owned change may use a **CI-first draft PR**: run the
  applicable source checks, push the branch, and open a draft PR. Drafts run
  the catalog job, but the main workflow skips the full build until the PR is
  ready for review or the workflow is explicitly dispatched. A local full
  build is not required for a draft checkpoint. State which checks have and
  have not run; opening a draft is not proof validation. The current triggers
  are in [the CI workflow](.github/workflows/lean_action_ci.yml).
- Parallel workers use isolated branches or worktrees with disjoint file
  ownership. Builds against a shared local Lake cache must be serialized.
  GitHub runners can validate PRs independently. One integrator reviews the
  statements, assumptions, source changes, and verification results.
- Before merging, the exact candidate revision must pass all source guards,
  the ordinary default build (including `Production` and the tactic
  regressions), and the applicable transitive-axiom checks. The Comparator
  audit covers only its listed theorem surface.
- After a rebase or integration change, rerun the relevant checks. Cancelled,
  skipped, stale, or missing checks never count as success. Fix failed draft
  checks before marking a PR ready.
- Do not push unverified changes directly to the default branch, and do not
  enable automatic merging to bypass review.

### Documentation

Routine CI does not generate full API documentation. Public documentation is
curated in the `RealRooted/Challenges/` entry points and rendered by
`scripts/build_challenge_pages.py`. Pull requests get a review artifact.

- Every challenge module needs an unconditional checked witness. Incomplete
  targets belong in GitHub issues, not in challenge modules.
- An explicit metadata block opts a module into the catalog. Only selected
  definitions and checked theorems are published, never conjectures, examples,
  or statement scaffolds.
- Each catalog metadata block requires `formalized = "YYYY-MM-DD"`, the date its
  selected headline result (or first theorem) was first formalized.
- The bounded module comment holds the explanatory prose. References come from
  the shared symmetricfunctions.com bibliography: list keys in the metadata
  (`references = [...]`), cite inline with `[@Key]` or `[@Key, Thm. 2.4]`, and
  link SymCat statements with `sf:label`. `scripts/symcat_sync.py` refreshes the
  snapshot in `website/symcat/` (see `website/README.md`). Works without a
  bibliography entry stay in prose until one is added to the SymCat
  `bibliography.bib`.
- After the ordinary build, `scripts/audit_challenge_catalog.py` verifies the
  selected declaration kinds and transitive axioms. Only that validated `main`
  revision deploys to GitHub Pages. Documentation never replaces proof
  validation, and the required `build` check does not depend on publication.

### Repository cleanliness

- Do not commit build logs (`*.log`), patch files (`*.patch`), backups (`*~`),
  or scratch files. Keep new kinds of temporary files local, or add them to
  `.gitignore`.
- `.gitignore` ignores new Markdown files by default, but ignored files can
  still become stale. Keep durable research progress, failed approaches, and
  open questions in the relevant GitHub issue, rather than maintaining a
  second research ledger in Markdown. Remove local scratch notes after their
  useful content is recorded there.
- Keep any local handoff short: active ownership, blockers, verification, and
  issue/PR links. It is not a proof-status ledger or a transcript archive.
- Maintained Markdown consists of development guides, topic navigation, and
  generated indexes. Update generated files through their generators, not by
  hand; use Git history for superseded documentation.

## License

Apache License, Version 2.0. See [`LICENSE`](LICENSE).

Related surveys: the Symmetric Functions Catalog pages on
[real-rooted polynomials](https://www.symmetricfunctions.com/realRooted.htm),
[interlacing](https://www.symmetricfunctions.com/realRootedInterlacing.htm),
[Pólya frequency](https://www.symmetricfunctions.com/polyaFrequency.htm), and
[real-rooted words](https://www.symmetricfunctions.com/realRootedWords.htm).
