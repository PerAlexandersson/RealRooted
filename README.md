# RealRooted

`RealRooted` is an experimental Lean 4 library for real-rooted polynomials,
interlacing, compatibility, and related combinatorial applications.

This repository is deliberately **vibe-coded**: much of the library was built
interactively with AI assistance, exploratory theorem packaging, and frequent
Lean feedback.  It is not a polished mathlib contribution.  The useful part is
that the statements below are checked Lean declarations, and the project gives
a searchable playground for real-rootedness and interlacing arguments.

## Build

The project uses Lean 4 and Mathlib through Lake.

```bash
lake exe cache get
lake build
```

For a quicker check of recent Veronese/Hurwitz work:

```bash
lake build RealRooted.VeroneseSection
lake build RealRooted.HurwitzMatrix
```

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

Combinatorial sequence modules are collected under
`RealRooted/CombinatorialExamples/`.

## Main Definitions

- `IsRealRooted p`: a nonzero real polynomial whose multiset of real roots has
  cardinality equal to `p.natDegree`.
- `Interlaces f g`, `Prec f g`, and `Prec0 f g`: the main interlacing
  relations.  `Prec0` is the zero-aware version.
- `IsGeneralizedSturmSeq ps`: a list-level Sturm sequence predicate using
  consecutive `Prec` relations.
- `IsInterlacingSeq fs` and `IsInterlacingSeq0 fs`: pairwise interlacing
  sequence predicates for finite lists.
- `Compatible f g`, `PairwiseCompatible fs`, and `FamilyCompatible fs`:
  Chudnovsky-Seymour style compatibility predicates.
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
- `operatorPreservesInterlacingPairsUpToOrder`: an operator preserving
  real-rootedness preserves interlacing pairs up to order.
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

**Polya Frequency And Conditional Veronese Sections**

- `nonneg_of_isPolyaFrequencySequence` and
  `hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff`: basic PF consequences.
- `toeplitzTotallyNonnegative_zero`, `isPolyaFrequencySequence_zero`, and
  `not_aissenSchoenbergWhitneyForward_without_nonzero`: the zero sequence is
  PF, so the forward ASW-to-`IsRealRooted` interface must explicitly exclude
  the zero polynomial.
- `isPolyaFrequencySequence_veroneseSectionSeq`: fixed-residue subsequences of
  a PF sequence are PF.
- `isPolyaFrequencySequence_veroneseSectionPolynomial_coeff` and
  `hasNonnegCoeffs_veroneseSectionPolynomial`: coefficient-level facts for
  Veronese section polynomials.
- `veroneseSectionPolynomial_ne_zero_of_coeff_ne_zero`: a selected nonzero
  coefficient gives a nonzero section.
- `veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_realRooted_nonneg` and
  `isRealRooted_veroneseSectionPolynomial_of_realRooted_nonneg`: a real-rooted
  polynomial with nonnegative coefficients has zero-or-real-rooted Veronese
  sections, and strictly real-rooted nonzero sections, conditional on the
  forward and reverse Aissen-Schoenberg-Whitney interfaces.
- `VeronesePairFullyInterlacing.section`,
  `VeronesePairFullyInterlacing.sectionPair`, and
  `VeronesePairFullyInterlacing.sectionPair_fin`: Veronese sections preserve
  the two-row fully interlacing pair interface.
- `prec_veroneseSectionPolynomial_of_prec` and the related pairwise-section
  declarations are conditional bridge theorems: they assume polynomial-to-Lace
  and Lace-to-polynomial interlacing interfaces.

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

The Veronese-section file is in this category.  It fully formalizes the
coefficient definitions, Toeplitz-total-nonnegativity submatrix argument, and
two-row Lace submatrix argument.  The headline polynomial consequences still
depend on statement-level interfaces such as
`aissenSchoenbergWhitneyForwardStatement`,
`aissenSchoenbergWhitneyReverseStatement`,
`FullyInterlacingPairToPrecStatement`, and
`FullyInterlacingPairToPrec0Statement`.

In short: this is a working research codebase, not a finished library API.
