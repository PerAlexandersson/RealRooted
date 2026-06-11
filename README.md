# RealRooted

`RealRooted` is an experimental Lean 4 library for real-rooted polynomials,
interlacing, compatibility, and related combinatorial applications.

This repository is deliberately **vibe-coded**: much of the library was built
interactively with AI assistance, exploratory theorem packaging, and frequent
Lean feedback.  It is not a polished mathlib contribution.  The useful part is
that the statements below are checked Lean declarations, and the project gives
a searchable playground for real-rootedness and interlacing arguments.
The long-term goal is to extract the stable, reusable core and upstream those
parts to mathlib.

## Build

The project uses Lean 4 and Mathlib through Lake.

```bash
lake exe cache get
lake build
```

For a quicker check of recent Veronese and Hurwitz-related work:

```bash
lake build RealRooted.VeroneseMatrix
lake build RealRooted.VeroneseSection
lake build RealRooted.HurwitzMatrix
```

## Contributors

- Per Alexandersson
- Yaël Dillies
- √2 (`sqrt-of-2`)

## Lean Style

New Lean code should generally follow the Lean community
[Library Style Guidelines](https://leanprover-community.github.io/contribute/style.html)
and
[Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html).
The most relevant local conventions are: keep lines at or below 100 characters,
use two-space indentation, keep top-level declarations flush-left, prefer
explicit declaration types, put `:= by` on the theorem statement line for tactic
proofs, and use mathlib-style declaration names.  Every Lean module in the
project should be imported, directly or indirectly, by the root file
`RealRooted.lean`. Avoid orphan modules that are not covered by the umbrella
build.

## Catalog References

The external mathematical guide is the Symmetric Functions Catalog.  The README
is organized around these pages and anchors:

- [Interlacing and interleaving roots](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacingPolynomials):
  derivative interlacing, Sturm sequences, Ma-Wang and Liu-Wang style criteria.
- [Interlacing sequences](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacingSequences)
  and [matrices preserving interlacing sequences](https://www.symmetricfunctions.com/realRootedInterlacing.htm#realMatrixRecursion):
  finite interlacing lists and matrix preservers.
- [Compatible polynomials](https://www.symmetricfunctions.com/realRootedInterlacing.htm#compatiblePolynomials):
  common interlacings and Chudnovsky-Seymour compatibility.
- [Symmetric decompositions](https://www.symmetricfunctions.com/realRootedInterlacing.htm#symmetricDecompInterlacing)
  and [operators preserving real-rootedness](https://www.symmetricfunctions.com/realRootedInterlacing.htm#realRootedPreservers):
  transforms, gamma bases, and operator interfaces.
- [Sturm sequences: permutations, set partitions and more](https://www.symmetricfunctions.com/realRootedWords.htm#realRootedWords):
  Eulerian, type B Eulerian, simsun, derangement, Touchard, singleton-free
  set-partition, colored set-partition, and Stirling-permutation examples.
- [Sturm sequences: Catalan families](https://www.symmetricfunctions.com/realRootedCatalan.htm#realRootedCatalan):
  Narayana and Motzkin polynomial examples.
- [Real-rooted and stable polynomials (overview)](https://www.symmetricfunctions.com/realRooted.htm):
  top-level map for interlacing, PF sequences, and real-rootedness techniques.
- [Real-rooted polynomials: tableaux and polytopes](https://www.symmetricfunctions.com/realRootedTableaux.htm):
  Sturm-sequence examples adjacent to the combinatorial families formalized
  here.
- Athanasiadis--Wagner,
  [*Veronese sections and interlacing matrices of polynomials and formal power
  series*](https://doi.org/10.48550/arXiv.2404.12989):
  the main reference for fully interlacing matrices and Veronese sections.  In
  this repository, the Athanasiadis--Wagner material is treated as reference
  context; the completed Veronese real-rootedness theorem below uses a separate
  cyclic-matrix/interlacing-preserver proof.

Useful statement-level jump points in SymCat:

- [Sturm sequences](https://www.symmetricfunctions.com/realRootedInterlacing.htm#sturmSequence):
  context for `prec_ma_wang`, `generalizedLiuWangCriterion`, and Sturm-family
  combinatorial files.
- [Matrices preserving interlacing sequences](https://www.symmetricfunctions.com/realRootedInterlacing.htm#realMatrixRecursion):
  context for `matrix_preserves_interlacing_seq`,
  `matrix_preserves_interlacing_seq0_of_2x2`, and row-threshold variants.
- [Compatible polynomials (Chudnovsky-Seymour)](https://www.symmetricfunctions.com/realRootedInterlacing.htm#compatiblePolynomials):
  context for the four-way compatibility wrappers and common-interleaver theorems.
- [Operators preserving real-rootedness](https://www.symmetricfunctions.com/realRootedInterlacing.htm#realRootedPreservers):
  context for `operatorPreservesInterlacingPairsUpToOrder`.
- [Symmetric decompositions](https://www.symmetricfunctions.com/realRootedInterlacing.htm#symmetricDecompInterlacing):
  context for `idDecompositionExistsUnique`, `rdDecompositionExistsUnique`, and
  gamma/`h -> f` transfer declarations.

Combinatorial sequence modules are collected under
`RealRooted/CombinatorialExamples/`.

## Main Definitions

- `p = 0 ∨ p.Splits`: the zero-aware real-rootedness convention used for
  closure statements where the zero polynomial is a natural exceptional case.
- `Interlaces f g`, `Prec f g`, and `Prec0 f g`: the main interlacing
  relations.  `Prec0` is the zero-aware version.
- `IsGeneralizedSturmSeq ps`: a list-level Sturm sequence predicate using
  consecutive `Prec` relations.
- `IsInterlacingSeq fs` and `IsInterlacingSeq0 fs`: pairwise interlacing
  sequence predicates for finite lists.
- `Compatible f g`, `PairwiseCompatible fs`, and `FamilyCompatible fs`:
  Chudnovsky-Seymour style compatibility predicates.
- `AllComboRealRooted f g`: every real linear combination of `f` and `g` is
  zero or splits over `ℝ`.
- `HasCommonInterleaver fs` and `PairwiseHasCommonInterleaver fs`: common
  right-interleaver predicates for finite families.
- `IsPolyaFrequencySequence a`: total nonnegativity of the Toeplitz matrix of a
  sequence.
- `veroneseSectionPolynomial r k p`: the fixed residue section of `p`.
- `FullyInterlacingPair a b`: two-row Lace total nonnegativity for coefficient
  sequences.

## Theorem Highlights

Every Lean declaration named in this section is checked.

**Interlacing Core**

Catalog context:
[interlacing roots](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacingPolynomials)
and [Sturm sequences](https://www.symmetricfunctions.com/realRootedInterlacing.htm#sturmSequence).

- `derivative_interlaces`: Rolle-style theorem that the derivative interlaces a
  real-rooted polynomial.
- `exists_root_derivative_between` and
  `isRoot_derivative_of_rootMultiplicity_ge_two`: root-location facts behind
  derivative interlacing.
- `prec_ma_wang`: Ma-Wang style derivative recurrence criterion.
- `generalizedLiuWangCriterion`: Liu-Wang style weighted-sum criterion.
- `favardInterlacing`, `isRealRooted_of_favard`, and
  `isGeneralizedSturmSeq_reverse_range_map_of_favard`: Favard recurrence
  interface for orthogonal-polynomial style Sturm sequences.

**Compatible Polynomials**

Catalog context:
[compatible polynomials](https://www.symmetricfunctions.com/realRootedInterlacing.htm#compatiblePolynomials).

- `hasCommonInterleaver_of_pairwiseHasCommonInterleaver`: pairwise common
  interleavers imply a global common interleaver.
- `isRealRooted_sum_of_commonInterleaver` and
  `isRealRooted_sum_of_commonLeftInterleaver`: nonnegative sums of a family with
  a common interleaver are real-rooted.
- `familyCompatible_of_commonInterleaver` and
  `pairwiseCompatible_of_familyCompatible`: the common-interleaver to
  compatibility direction and the easy reverse implication.
- `chudnovskySeymour_fourWay_of_compatibleDegreeSplit`,
  `chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs`, and
  `chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs`: packaged
  Chudnovsky-Seymour four-way equivalences under formalized bridge hypotheses.
- `pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one`: complete
  low-degree compatibility equivalence.

**Interlacing Sequences And Preservers**

Catalog context:
[interlacing sequences](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacingSequences),
[matrix preservers](https://www.symmetricfunctions.com/realRootedInterlacing.htm#realMatrixRecursion),
and [operators preserving real-rootedness](https://www.symmetricfunctions.com/realRootedInterlacing.htm#realRootedPreservers).

- `matrix_preserves_interlacing_seq` and
  `matrix_preserves_interlacing_seq0_of_2x2`: list-matrix interlacing
  preservers from 2-by-2 conditions.
- `rowThreshold_matrix_preserves_interlacing_seq_of_2x2`: row-threshold
  specialization of the matrix-preserver theorem.
- `PreservesRealRootedOrZero` and
  `operatorPreservesInterlacingPairsUpToOrder`: an operator preserving
  zero-or-splits real-rootedness on strict real-rooted inputs preserves interlacing pairs
  up to order.
- `gammaRealRootedIffPolynomialRealRootedNonpos`: gamma-transform
  real-rootedness criterion with nonpositive roots.

**Symmetric Decompositions**

Catalog context:
[symmetric decompositions](https://www.symmetricfunctions.com/realRootedInterlacing.htm#symmetricDecompInterlacing).

- `isIdDecomposition_formula` and `idDecompositionExistsUnique`: existence,
  formula, and uniqueness of the symmetric `I_d`-decomposition.
- `isRdDecomposition_formula` and `rdDecompositionExistsUnique`: analogous
  facts for the `R_d`-decomposition.
- `isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs`: the
  `h -> f` transform preserves real-rootedness in the nonnegative setting.
- `prec_iff_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs`:
  interlacing transfer through the transform under the minimal-degree
  hypotheses used by the decomposition machinery.

**Veronese Sections**

Reference context: Athanasiadis--Wagner,
[*Veronese sections and interlacing matrices of polynomials and formal power
series*](https://doi.org/10.48550/arXiv.2404.12989), especially the Veronese
section preservation results around Corollary 5.6.  The fully interlacing
matrix theorem from that paper is not packaged here as one final theorem; the
library instead contains coefficient-level submatrix statements, conditional
interfaces for the fully interlacing route, and a completed cyclic-matrix proof
of the real-rootedness consequence.

- `veroneseSectionPolynomial r k p`: the fixed residue section of `p`.
- `veroneseSectionPolynomialListDesc`,
  `veroneseLinearFactorMatrixDesc`, and
  `matPolyAction_veroneseLinearFactorMatrixDesc`: descending-order matrix
  form of the linear-factor recursion.  The order
  `S_{r-1}, S_{r-2}, ..., S_0` puts the cyclic `X` entry in the lower-left
  corner, which matches the matrix-preserver theorem.
- `veroneseLinearFactorMatrixDesc_has2x2`: the finite 2-by-2 affine check for
  the cyclic matrix attached to multiplication by `X + C a`, for `a ≥ 0`.
- `isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_X_add_C_mul`:
  the iterable linear-factor step.  If the current descending Veronese sections
  are weakly interlacing, have nonnegative coefficients, and all nonzero
  sections are real-rooted, then the same package holds after multiplying by
  `X + C a`.
- `isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_of_realRooted_nonneg`:
  a real-rooted polynomial with nonnegative coefficients has weakly interlacing
  descending Veronese sections, and every nonzero section is real-rooted.
- `isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`:
  the main zero-aware Veronese real-rootedness corollary from the matrix proof.
  This is the completed theorem corresponding to the Veronese idea that
  motivated the recent formalization pass.

**Polya Frequency And Fully Interlacing Background**

- `nonneg_of_isPolyaFrequencySequence` and
  `hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff`: basic PF consequences.
- `toeplitzTotallyNonnegative_zero`, `isPolyaFrequencySequence_zero`, and
  `not_aissenSchoenbergWhitneyForward_without_nonzero`: the zero sequence is
  PF, so the forward ASW-to-`IsRealRooted` interface must explicitly exclude
  the zero polynomial.
- `aissenSchoenbergWhitneyForwardOrZeroStatement` and
  `aissenSchoenbergWhitneyForward_iff_orZero`: zero-aware and strict forward
  ASW interfaces are equivalent.
- `isPolyaFrequencySequence_veroneseSectionSeq`: fixed-residue subsequences of
  a PF sequence are PF.  This is the Toeplitz submatrix version of the
  Veronese-section idea.
- `isPolyaFrequencySequence_veroneseSectionPolynomial_coeff` and
  `hasNonnegCoeffs_veroneseSectionPolynomial`: coefficient-level facts for
  Veronese section polynomials.
- `veroneseSectionPolynomial_ne_zero_of_coeff_ne_zero`: a selected nonzero
  coefficient gives a nonzero section.
- `veroneseSectionPolynomial_X_mul_zero`,
  `veroneseSectionPolynomial_X_mul_succ`,
  `veroneseSectionPolynomial_X_add_C_mul_zero`, and
  `veroneseSectionPolynomial_X_add_C_mul_succ`: recurrence formulas for
  Veronese sections under multiplication by `X` and by a linear factor
  `X + C a`.
- A direct Borcea-Branden algebraic-symbol proof would need a more refined
  stability domain than ordinary upper-half-plane stability: for the even
  section `T(a0 + a1 X + a2 X^2) = a0 + a2 X`, the degree-two symbol is
  `X + Y^2`, which vanishes at `X = 2 * I`, `Y = -1 + I`.  Thus the raw
  Veronese section is not a full stability-preserver in the usual finite-degree
  symbol sense, even though it is still expected to preserve the
  nonnegative-real-rooted cone.
- `isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg`,
  `veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_realRooted_nonneg`,
  and `isRealRooted_veroneseSectionPolynomial_of_realRooted_nonneg`: a
  real-rooted polynomial with nonnegative coefficients has zero-or-real-rooted
  Veronese sections, and strictly real-rooted nonzero sections, conditional on
  the forward and reverse Aissen-Schoenberg-Whitney interfaces.
- `VeronesePairFullyInterlacing.section`,
  `VeronesePairFullyInterlacing.sectionPair`, and
  `VeronesePairFullyInterlacing.sectionPair_fin`: Veronese sections preserve
  the two-row fully interlacing pair interface.
- `prec_veroneseSectionPolynomial_of_prec` and the related pairwise-section
  declarations are conditional bridge theorems: they assume polynomial-to-Lace
  and Lace-to-polynomial interlacing interfaces.
- `hermiteBiehlerForwardPosStatement`,
  `pfPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix`, and
  `nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix`:
  sign-normalized replacements for the false sign-free Hermite-Biehler route.
- `prec_veroneseSectionPolynomial_of_hermiteBiehlerPosHurwitzMatrix` and
  `prec_veroneseSectionPolynomial_of_nonneg_hermiteBiehlerPosHurwitzMatrix`:
  fixed-section Veronese interlacing wrappers through the corrected
  Hermite-Biehler/Hurwitz-matrix route.

**Permutation And Word Examples**

Catalog context:
[real-rooted words](https://www.symmetricfunctions.com/realRootedWords.htm#realRootedWords),
[Eulerian variations](https://www.symmetricfunctions.com/realRootedWords.htm#sturmEulerian),
[permutation statistics](https://www.symmetricfunctions.com/realRootedWords.htm#sturmPermutations),
and [Stirling permutations](https://www.symmetricfunctions.com/realRootedWords.htm#sturmOther).

- `isRealRooted_eulerianTilde`, `interlaces_eulerianTilde_succ`, and
  `isSturmSeq_eulerianTildePrefix`.
- `isRealRooted_typeBEulerian`, `interlaces_typeBEulerian_succ`, and
  `isSturmSeq_typeBEulerianPrefix`.
- `isRealRooted_simsun`, `interlaces_simsun_succ_of_odd`, and
  `isGeneralizedSturmSeq_simsunPrefix`.
- `isRealRooted_sturmDerangementsExc`, `interlaces_sturmDerangementsExc_succ`,
  and `isSturmSeq_sturmDerangementsExcPrefix`.
- `isRealRooted_stirlingPermutations`, `interlaces_stirlingPermutations_succ`,
  and `isSturmSeq_stirlingPermutationsPrefix`.

**Set-Partition Examples**

Catalog context:
[set partitions](https://www.symmetricfunctions.com/realRootedWords.htm#sturmSetPartitions).

- `isRealRooted_touchard`, `interlaces_touchard_succ`, and
  `isSturmSeq_touchardPrefix`.
- `isRealRooted_singletonFreeSetPartitions`,
  `interlaces_singletonFreeSetPartitions_succ_of_odd`, and
  `isGeneralizedSturmSeq_singletonFreeSetPartitionsPrefix`.
- `isRealRooted_coloredSetPartitions`,
  `interlaces_coloredSetPartitions_succ`, and
  `isSturmSeq_coloredSetPartitionsPrefix`.
- `isRealRooted_typeBSetPartitions` and
  `interlaces_typeBSetPartitions_succ`.
- `oneDescentGamma_one_isRealRooted` and
  `oneDescentQ_one_isRealRooted`.

**Catalan-Family Examples**

Catalog context:
[real-rooted Catalan families](https://www.symmetricfunctions.com/realRootedCatalan.htm#realRootedCatalan).

- `isRealRooted_narayanaQuot_of_nonnegCoeffs`,
  `interlaces_narayanaQuot_succ_of_nonnegCoeffs`, and
  `isSturmSeq_narayanaPrefix_of_nonnegCoeffs`.
- `isRealRooted_narayana_of_nonnegCoeffs` and
  `interlaces_narayana_succ_of_nonnegCoeffs`.
- `isRealRooted_motzkin`, `prec_motzkin_succ`, and
  `isGeneralizedSturmSeq_motzkinPrefix`.

**Regression And Counterexample Declarations**

- `scaledLinearFamily_pairwiseCompatible_iff_familyCompatible`: concrete
  sanity-check family for compatibility.
- `not_hermiteBiehlerForwardStatement`: checked counterexample to an overly
  sign-free Hermite-Biehler forward interface.
- `not_posComboNoCommonAffineFamilyStatement`,
  `not_posComboNoCommonBoundaryRightPairOrientationStatement`,
  `not_posComboNoCommonSameDegreeShiftedPairOrientationStatement`,
  `not_posComboNoCommonSameDegreeOrientationNonnegStatement`, and
  `not_posComboNoCommonSuccDegreeOrientationNonnegStatement`: counterexamples
  documenting false strengthening attempts.

## Current Caveats

Several declarations are intentionally statement-level interfaces for classical
theorems that are not yet fully formalized here.  Recent work also found that a
sign-free Hermite-Biehler forward interface was false as stated; the theorem
`not_hermiteBiehlerForwardStatement` records the checked counterexample.  The
forward Aissen-Schoenberg-Whitney interface is also stated for nonzero
polynomials, since PF includes the zero sequence while `IsRealRooted` is strict
in this library.

TODO T9 is the Garloff-Wagner Hadamard proper-position theorem, currently
recorded as `garloffWagnerHadamardNonnegPrecStatement` in
`RealRooted.Hadamard`.  This is the remaining standard theorem input used by
the `SuperEulerian` proof through its `StandardFacts` bundle; the implementation
should live in RealRooted.  Reference: J. Garloff and D. G. Wagner, *Hadamard
Products of Stable Polynomials Are Stable*, J. Math. Anal. Appl. 202 (1996),
797--809, Theorem 4(b).

TODO T10 is the reverse Aissen-Schoenberg-Whitney theorem, recorded as
`aissenSchoenbergWhitneyReverseStatement` in
`RealRooted.AissenSchoenbergWhitney`.  This is the useful ASW direction for
turning real-rooted polynomials with nonnegative coefficients and nonpositive
roots into Pólya-frequency coefficient sequences.  Reference: M. Aissen,
I. J. Schoenberg, and A. M. Whitney, *On the generating functions of totally
positive sequences. I*, J. Analyse Math. 2 (1952), 93--103.

The Veronese-section file is in this category.  It fully formalizes the
coefficient definitions, Toeplitz-total-nonnegativity submatrix argument, and
two-row Lace submatrix argument.  The simple proof idea is exactly this:
Veronese sectioning selects an arithmetic progression of columns in a Toeplitz
or Lace matrix, and total nonnegativity is inherited by submatrices.  The
headline polynomial consequences still depend on statement-level interfaces
such as
`aissenSchoenbergWhitneyForwardStatement`,
`aissenSchoenbergWhitneyReverseStatement`,
`FullyInterlacingPairToPrecStatement`, and
`FullyInterlacingPairToPrec0Statement`.  The preferred Hermite-Biehler route
now uses the sign-normalized `hermiteBiehlerForwardPosStatement`, since the
sign-free forward statement is false.

The separate cyclic-matrix route in `RealRooted.VeroneseMatrix` is no longer
only a plan.  It proves the finite `2×2` affine check for the sparse cyclic
matrix, iterates the linear-factor step, and derives the zero-aware theorem
`isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`.
This proves the Veronese real-rootedness consequence for real-rooted
polynomials with nonnegative coefficients without invoking the full
Athanasiadis--Wagner fully interlacing matrix machinery.

### `proof_wanted`

Use `proof_wanted` for intentionally recorded future theorem targets instead of
ending a theorem proof with `sorry`.

In short: this is a working research codebase, not a finished library API.
