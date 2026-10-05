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

- [`PROOF_STATUS.md`](PROOF_STATUS.md) lists proof assumptions, open statement
  targets, and refuted legacy interfaces.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) describes the module layers, import
  budgets, and module-splitting rules.

## Build

The project uses Lean 4.34.0 and Mathlib v4.34.0.

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
- `RealRooted/Challenges/` holds short entry points, one per completed result.
  They feed the public catalog (see [Documentation](#documentation)).
- `RealRooted/Tactic/` holds the real-rootedness and interlacing tactics.
  `Tactic/OEIS_COVERAGE.md` is the generated ledger of OEIS certificate
  coverage.
- Theory lives in topic directories such as `CommonInterleaver/`,
  `Hadamard/`, `BorceaBranden/`, `MultiplierSequence/`, `LGV/`, and
  `Wronskian/`. Concrete families live in `CombinatorialExamples/` and
  `Applications/`.

## Main concepts

- `Interlaces f g`, `StrictInterl f g`, `Interl f g`: interlacing in the
  strict, oriented, and zero-aware forms.
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
  (`compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant`) and the
  Chudnovsky–Seymour common-interleaver theory (`Challenges.ChudnovskySeymour`).
- **Graphs.** Claw-free independence polynomials
  (`Graph.clawFree_indepPoly_splits`), acyclic sink polynomials
  (`UnitIntervalGraph.acyclicSinkPolynomial_splits`,
  `Graph.allOrientationSinkPolynomial_splits_of_clawFree`), and minima
  polynomials (`Graph.minimaPolynomial_splits`).
- **Combinatorial families.** Eulerian and type-B Eulerian polynomials
  (`Challenges.Eulerian`), generalized snake posets
  (`snakeInterlacing_generalizedSnakeRookModel`), peak-value enumerators
  (`peakValuePolynomial_mvRealStable`), the A16634x gamma pencil
  (`gammaU_strictInterl_gammaV`), the Jacobi deformation and OEIS A132885
  (`JacobiDeformation.polynomial_strict_package`), and the weighted deco
  Eulerian transform
  (`Challenges.DecoEulerian.weightedDecoTransform_splits_hasSimpleRoots_roots_neg`).

Open problems and proof tasks are tracked in
[GitHub issues](https://github.com/PerAlexandersson/RealRooted/issues), not in
this file.

## Contributing

### Proof status

- `sorry`, `admit`, and source `axiom` commands are not accepted as proofs.
  Track an unproved result in a GitHub issue.
- A temporary `...Statement : Prop` interface is allowed only when it is
  genuinely useful. List it in `PROOF_STATUS.md`, document that it is an
  unproved target, and keep it out of production theorem dependencies.
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
python3 scripts/check_root_imports.py --fix        # register a new module in its umbrellas
python3 scripts/check_import_architecture.py       # import graph, layers, budgets
python3 scripts/check_proof_status.py --self-test
python3 scripts/check_proof_status.py              # sorry/axiom/tactic rules, open statements
```

The import guards check the broad, production, and regression umbrellas
separately, and reject production closures that contain tactic examples. The
proof-status guard also reports low-use theorem-shaped propositions that still
need an explicit entry in `PROOF_STATUS.md`.

### CI and pull requests

- A small, independently owned change may use a **CI-first draft PR**: run the
  applicable source checks, push the branch, and open a draft PR so GitHub
  compiles it. A local full build is not required for that draft. State which
  checks have and have not run. A draft commit is not a verified theorem
  milestone.
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
- The bounded module comment holds the explanatory prose and the primary
  references.
- After the ordinary build, `scripts/audit_challenge_catalog.py` verifies the
  selected declaration kinds and transitive axioms. Only that validated `main`
  revision deploys to GitHub Pages. Documentation never replaces proof
  validation, and the required `build` check does not depend on publication.

### Repository cleanliness

- Do not commit build logs (`*.log`), patch files (`*.patch`), backups (`*~`),
  or scratch files. Keep new kinds of temporary files local, or add them to
  `.gitignore`.
- Keep issue-specific notes local. `.gitignore` ignores new Markdown files by
  default. It allows only the maintained top-level guides, the
  architecture and status ledgers, the generated tactic coverage, and the public
  `SuperEulerian/` subtree.

## License

Apache License, Version 2.0. See [`LICENSE`](LICENSE).

Related surveys: the Symmetric Functions Catalog pages on
[real-rooted polynomials](https://www.symmetricfunctions.com/realRooted.htm),
[interlacing](https://www.symmetricfunctions.com/realRootedInterlacing.htm),
[Pólya frequency](https://www.symmetricfunctions.com/polyaFrequency.htm), and
[real-rooted words](https://www.symmetricfunctions.com/realRootedWords.htm).
