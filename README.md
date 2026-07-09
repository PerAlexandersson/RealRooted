# RealRooted

`RealRooted` is an experimental Lean 4 library for real-rooted univariate
polynomials, interlacing, compatibility, Polya-frequency sequences, and related
combinatorial applications.

The repository is a research formalization workspace rather than a polished
mathlib contribution.  The useful part is that the named theorem declarations
below are checked by Lean, and the surrounding files give searchable proof
infrastructure for real-rootedness and interlacing arguments.  The long-term
goal is to extract stable, reusable components for eventual upstreaming.

## Table of Contents

- [Build](#build)
- [Repository Layout](#repository-layout)
- [Main Concepts](#main-concepts)
- [Checked Highlights](#checked-highlights)
- [Current Roadmap](#current-roadmap)
- [Development Notes](#development-notes)
- [Bibliography and Links](#bibliography-and-links)

## Build

The project uses Lean 4 and Mathlib through Lake.

```bash
lake exe cache get
lake build
```

Useful focused checks for recent theorem areas are:

```bash
lake build RealRooted.CommonInterleaverTwo
lake build RealRooted.ChudnovskySeymour
lake build RealRooted.Hadamard
lake build RealRooted.VeroneseMatrix
lake build RealRooted.VeroneseSection
lake build RealRooted.Bezoutian
lake build RealRooted.HeilmannLieb
```

## Repository Layout

- `RealRooted.lean` is the umbrella import for the public development.
- `RealRooted/Basic.lean`, `Derivative.lean`, `Wagner*.lean`, and
  `InterlacingSequence*.lean` contain the core interlacing API.
- `RealRooted/CommonInterleaver*.lean` and `ChudnovskySeymour.lean` contain the
  compatibility and common-interleaver work.
- `RealRooted/AissenSchoenbergWhitney.lean`, `PFPolynomial.lean`,
  `VeroneseSection.lean`, and `VeroneseMatrix.lean` contain the PF, Toeplitz,
  and Veronese-section material.
- `RealRooted/SymmetricDecomposition.lean`, `Bezoutian.lean`, and
  `Hadamard.lean` contain larger theorem packages and classical interfaces.
- `RealRooted/HeilmannLieb.lean` contains the graph-theoretic
  Chudnovsky-Seymour and Heilmann-Lieb matching-polynomial corollaries.
- `RealRooted/CombinatorialExamples/` contains examples such as Eulerian,
  type B Eulerian, simsun, Touchard, Narayana, Motzkin, and related families.
- `RealRooted/Mathlib/` contains local compatibility lemmas intended to look
  like future Mathlib additions.

## Main Concepts

- `Interlaces f g`, `Prec f g`, and `Prec0 f g`: the main interlacing and
  proper-position relations.  `Prec0` is the zero-aware version.
- `p = 0 ∨ p.Splits`: the zero-aware real-rootedness convention used in closure
  statements where the zero polynomial is a natural exceptional case.
- `IsGeneralizedSturmSeq ps`, `IsInterlacingSeq fs`, and `IsInterlacingSeq0 fs`:
  list-level Sturm and interlacing predicates.
- `Compatible f g`, `PairwiseCompatible fs`, and `FamilyCompatible fs`:
  Chudnovsky-Seymour style compatibility predicates.
- `HasCommonInterleaver fs` and `HasCommonLeftInterleaver fs`: common
  interleaver data for finite families.
- `AllComboRealRooted f g`: every real linear combination of `f` and `g` is
  zero or real-rooted.
- `IsPolyaFreqSeq a`: total nonnegativity of the Toeplitz matrix of a sequence.
- `veroneseSectionPolynomial r k p`: the fixed-residue Veronese section of a
  polynomial.
- `FullyInterlacingPair a b`: the two-row Lace total-nonnegativity interface
  used by the Veronese and Hurwitz-matrix route.

## Checked Highlights

Every declaration named in this section is a checked Lean declaration, unless
it is explicitly described as an unproved target theorem with a `sorry` stub.

### Interlacing And Preservers

- `derivative_interlaces`: Rolle-style derivative interlacing for real-rooted
  polynomials.
- `prec_ma_wang` and `generalizedLiuWangCriterion`: Ma-Wang and Liu-Wang style
  criteria for interlacing recurrences and weighted sums.
- `favardInterlacing` and `isRealRooted_of_favard`: a Favard recurrence
  interface for orthogonal-polynomial style Sturm sequences.
- `matrix_preserves_interlacing_seq` and
  `matrix_preserves_interlacing_seq0_of_2x2`: matrix preservers from finite
  two-by-two interlacing checks.
- `operatorPreservesInterlacingPairsUpToOrder`: a general operator-preserver
  interface for interlacing pairs.

### Compatibility And Common Interleavers

- `hasCommonInterleaver_of_pairwiseHasCommonInterleaver`: pairwise common
  interleavers imply a global common interleaver.
- `isRealRooted_sum_of_commonInterleaver` and
  `isRealRooted_sum_of_commonLeftInterleaver`: nonnegative sums are real-rooted
  when a family has common interleaver data.
- `familyCompatible_of_commonInterleaver` and
  `pairwiseCompatible_of_familyCompatible`: the easy directions relating
  common interleavers and compatibility.
- Declarations with prefix `chudnovskySeymour_fourWay_of_`: several checked
  Chudnovsky-Seymour four-way packages under formalized bridge hypotheses.
- `pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one`: the complete
  low-degree compatibility equivalence.

### Symmetric Decomposition And Bezoutians

- `idDecompositionExistsUnique` and `rdDecompositionExistsUnique`: existence
  and uniqueness of the Branden-Solus symmetric decompositions.
- `brandenSolusTheorem26`: the formalized Branden-Solus Theorem 2.6 package in
  the local `Prec` language.
- `isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs`: real-rootedness
  preservation for the `h -> f` transform in the nonnegative setting.
- `strictPrecSameDegree_iff_bezoutMatrix_posDef`: strict same-degree
  Bezoutian characterization.

### Polya Frequency, ASW, And Veronese Sections

- `aissenSchoenbergWhitney_reverse`: the reverse Aissen-Schoenberg-Whitney
  direction, from real-rooted nonpositive roots and nonnegative coefficients to
  a Polya-frequency coefficient sequence.
- `aissenSchoenbergWhitneyForward`: the target theorem for the opposite ASW
  direction.
- `IsPolyaFreqSeq.veroneseSectionSeq` and
  `IsPolyaFreqSeq_veroneseSectionPolynomial_coeff`: Veronese subsequences and
  Veronese section coefficients preserve Toeplitz total nonnegativity.
- `isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`:
  the completed cyclic-matrix proof that Veronese sections of a real-rooted
  nonnegative-coefficient polynomial are zero or real-rooted.
- `not_isUpperHalfPlaneStable_hermiteBiehlerPolynomial_X_neg_one`: a checked
  counterexample documenting why the Hermite-Biehler forward route is exposed
  only in sign-normalized form.

### Graph Theorems

- `clawFree_indepPoly_splits`: the graph-form Chudnovsky-Seymour theorem for
  independence polynomials of finite claw-free graphs.
- `matchingGeneratingPolynomial_splits`: Heilmann-Lieb real-rootedness for the
  matching-generating polynomial.
- `matchingPolynomialByEdges_splits`: the same Heilmann-Lieb theorem for the
  intrinsic edge-matching polynomial.

### Combinatorial Examples

The example files prove real-rootedness and, in many cases, Sturm or interlacing
sequence statements for standard combinatorial families.  Representative
declarations include:

- `isRealRooted_eulerianTilde`
- `isRealRooted_typeBEulerian`
- `isRealRooted_simsun`
- `isRealRooted_touchard`
- `isRealRooted_coloredSetPartitions`
- `isRealRooted_narayana_of_nonnegCoeffs`
- `isRealRooted_motzkin`

## Current Roadmap

The main open flagship theorem is the Chudnovsky-Seymour compatibility theorem:
pairwise compatibility should be equivalent to common interleaver data under
the usual nonzero, real-rooted, and positive-leading hypotheses.  The
finite-family upgrades are now named and packaged in `CommonInterleaverSeq`;
the remaining work is concentrated in the two-polynomial pair endpoints in
`CommonInterleaverTwo` and the final wrappers in `ChudnovskySeymour`.

The graph-form Chudnovsky-Seymour route through claw-free independence
polynomials is formalized in `RealRooted.HeilmannLieb`, including the
Heilmann-Lieb matching-polynomial corollaries.

The Garloff-Wagner Hadamard proper-position theorem is now formalized as
`garloffWagnerHadamardNonnegPrec`, with the direct proof route in
`RealRooted/GarloffWagner.lean`.

New formalization target: Braun-Jal, *Order polytopes of generalized snake
posets are h^*-real-rooted*, arXiv:2607.00922v1.  The immediate Lean todo is
their Theorem 4.1: for a generalized snake word `w` of length `n >= 1`, the
non-nesting rook polynomial `M_{epsilon w}` is real-rooted and the polynomial
for the word with the final letter deleted interlaces it.  Concrete subtasks:
define generalized snake words, deletion of the final letter, and prefix
operations; define the associated squarecase/non-nesting rook polynomials;
formalize the modified Narayana polynomials `P_n`, the auxiliary sums `G_n`,
and the interlacing inputs behind Lemmas 3.3 and 3.4; prove the positive
non-nesting recurrence of Theorem 3.5; expose the Branden matrix interlacing
preserver used in the induction; prove Theorem 4.1 by strong induction; then
package the resulting h^*-real-rootedness statement for order polytopes via the
Stanley / Alexandersson-Jal width-two correspondence.

Short-term documentation/onboarding work is tracked by the challenge-file issue:
small Lean entry-point files for Branden-Solus, Aissen-Schoenberg-Whitney, and
Chudnovsky-Seymour theorem targets.

Longer term, a Borcea-Branden direction would be a substantial expansion toward
stability theory.  A realistic path would first build the Hermite-Biehler and
Hurwitz-matrix total-nonnegativity interfaces into proved theorems, then add the
multivariate stability infrastructure needed for algebraic-symbol preserver
theorems.

Current GitHub tracking:

- #34: Garloff-Wagner Hadamard proper-position.
- #41 and #42: Chudnovsky-Seymour pair endpoints.
- #51: challenge files.

Recently closed:

- #44 and #45: Chudnovsky-Seymour family theorem and wrapper.
- #52: Heilmann-Lieb as a Chudnovsky-Seymour corollary.

## Development Notes

For unproved conjectures and target theorem interfaces, the project may use
standard Lean theorem declarations with `sorry` proofs. This keeps downstream
signatures uncluttered while preserving searchable names for the classical
inputs that still need formal proofs.

New Lean code should follow the Lean community style guidelines and Mathlib
naming conventions where practical.  In particular, keep declarations explicit,
prefer small reusable lemmas, keep top-level declarations flush-left, and make
sure public modules are imported by `RealRooted.lean`. New committed Lean code
should not add `admit`, `axiom`, or avoidable warnings; intentional `sorry`
stubs should mark explicit theorem targets.

Please keep repository configuration files (like `lakefile.toml` and
`lake-manifest.json`) free of hardcoded absolute paths such as
`/lake-cache/projects/...`. Reusable relative repository paths such as
`.lake/packages` and `.lake/build` ensure that the builds work out of the box
in local developer environments.

## Bibliography and Links

- M. Aissen, I. J. Schoenberg, and A. M. Whitney, *On the generating functions
  of totally positive sequences. I*, J. Analyse Math. 2 (1952), 93--103.
- C. A. Athanasiadis and C. H. Wagner, *Veronese sections and interlacing
  matrices of polynomials and formal power series*, arXiv:2404.12989.
- J. Borcea and P. Branden, *The Lee-Yang and Polya-Schur programs. I. Linear
  operators preserving stability*, Invent. Math. 177 (2009), 541--569.
- P. Branden and L. Solus, *Symmetric decompositions and real-rootedness*,
  Int. Math. Res. Not. (2019), doi:10.1093/imrn/rnz059.
- M. Chudnovsky and P. Seymour, *The roots of the independence polynomial of a
  clawfree graph*, J. Combin. Theory Ser. B 97 (2007), 350--357.
- J. Garloff and D. G. Wagner, *Hadamard Products of Stable Polynomials Are
  Stable*, J. Math. Anal. Appl. 202 (1996), 797--809.
- O. J. Heilmann and E. H. Lieb, *Theory of monomer-dimer systems*, Comm. Math.
  Phys. 25 (1972), 190--232.
- Symmetric Functions Catalog:
  <https://www.symmetricfunctions.com/realRooted.htm>.
