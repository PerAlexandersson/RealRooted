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

## References And Context

The formalization follows the real-rootedness and interlacing terminology used
in the Symmetric Functions Catalog:

- [Interlacing polynomials](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacingPolynomials)
  for interlacing, Sturm sequences, compatible polynomials, and preservers.
- [Real-rooted words](https://www.symmetricfunctions.com/realRootedWords.htm#realRootedWords)
  for permutation, set-partition, and Stirling-permutation polynomial
  examples.
- [Real-rooted Catalan families](https://www.symmetricfunctions.com/realRootedCatalan.htm#realRootedCatalan)
  for Catalan-family examples such as Motzkin and Narayana polynomials.

Combinatorial sequence modules are collected under
`RealRooted/CombinatorialExamples/`.

## Main Definitions

- `IsRealRooted p`: a nonzero real polynomial whose multiset of real roots has
  cardinality equal to `p.natDegree`.
- `Interlaces f g`, `Prec f g`, and `Prec0 f g`: the main interlacing
  relations.  `Prec0` is the zero-aware version.
- `Compatible f g`, `PairwiseCompatible fs`, and `FamilyCompatible fs`:
  Chudnovsky-Seymour style compatibility predicates.
- `HasCommonInterleaver fs` and `PairwiseHasCommonInterleaver fs`: common
  right-interleaver predicates for finite families.
- `IsPolyaFrequencySequence a`: total nonnegativity of the Toeplitz matrix of a
  sequence.
- `veroneseSectionPolynomial r k p`: the fixed residue section of `p`.
- `FullyInterlacingPair a b`: two-row Lace total nonnegativity for coefficient
  sequences.

## Selected Checked Theorems

Core interlacing and derivatives:

- `derivative_interlaces`
- `exists_root_derivative_between`
- `isRoot_derivative_of_rootMultiplicity_ge_two`

Common interleavers and compatibility:

- `hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver`
- `hasCommonInterleaver_of_pairwiseHasCommonInterleaver`
- `isRealRooted_sum_of_commonInterleaver`
- `isRealRooted_sum_of_commonLeftInterleaver`
- `pairHasCommonInterleaver_of_sameDegree_slotIntersections`
- `pairwiseCompatible_of_commonInterleaver`
- `pairwiseHasCommonInterleaver_of_pairwiseCompatible`
- `familyCompatible_of_commonInterleaver`
- `pairwiseCompatible_of_familyCompatible`
- `allComboRealRooted_of_natDegree_le_one`
- `pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one`

Chudnovsky-Seymour and positive-combination packaging:

- `chudnovskySeymour_fourWay_of_compatibleDegreeSplit`
- `chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs`
- `chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs`
- `pairwiseCompatible_iff_familyCompatible_of_pairBridgePos`
- `pairwiseCompatible_iff_familyCompatible_of_degreeSplit_and_nonnegCoeffs`
- `pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_and_nonnegCoeffs`
- `posComboNoCommonBridge_iff_orientation`

Favard, Liu-Wang, and gamma transforms:

- `favardInterlacing`
- `isRealRooted_of_favard`
- `isGeneralizedSturmSeq_reverse_range_map_of_favard`
- `prec_generalizedLiuWang_strict`
- `prec_generalizedLiuWang_of_no_common`
- `generalizedLiuWangCriterion`
- `gammaRealRootedIffPolynomialRealRootedNonpos`

Pólya-frequency and Veronese sections:

- `nonneg_of_isPolyaFrequencySequence`
- `hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff`
- `isPolyaFrequencySequence_veroneseSectionSeq`
- `isPolyaFrequencySequence_veroneseSectionPolynomial_coeff`
- `isPolyaFrequencySequence_veroneseSectionPolynomial_of_realRooted_nonneg`
- `isRealRooted_veroneseSectionPolynomial_of_realRooted_nonneg`
- `VeronesePairFullyInterlacing.section`
- `VeronesePairFullyInterlacing.sectionPair`
- `VeronesePairFullyInterlacing.sectionPair_fin`

Hermite-Biehler and Hurwitz-matrix interfaces:

- `complexify_oddEvenPolynomial`
- `eval_complexify_oddEvenPolynomial`
- `eval_hermiteBiehlerPolynomial`
- `not_hermiteBiehlerForwardStatement`
- `HermiteBiehlerStableToHurwitzOddEvenStatement`
- `hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair`
- `hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors`
- `HurwitzMatrixCriterionStatement`

Veronese bridge wrappers:

- `pfPrecToFullyInterlacingPair_of_hermiteBiehlerHurwitzMatrix`
- `nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerHurwitzMatrix`
- `prec0_veroneseSectionPolynomial_of_hermiteBiehlerHurwitzMatrix`
- `prec_veroneseSectionPolynomial_of_hermiteBiehlerHurwitzMatrix`
- `prec0_veronesePairSectionPolynomial_fin_of_hermiteBiehlerHurwitzMatrix`
- `prec_veronesePairSectionPolynomial_fin_of_hermiteBiehlerHurwitzMatrix`
- `prec0_veroneseSectionPolynomial_of_nonneg_hermiteBiehlerHurwitzMatrix`
- `prec_veroneseSectionPolynomial_of_nonneg_hermiteBiehlerHurwitzMatrix`
- `prec0_veronesePairSectionPolynomial_fin_of_nonneg_hermiteBiehlerHurwitzMatrix`
- `prec_veronesePairSectionPolynomial_fin_of_nonneg_hermiteBiehlerHurwitzMatrix`

Concrete regression and counterexample declarations:

- `scaledLinearFamily_pairwiseCompatible_iff_familyCompatible`
- `not_posComboNoCommonAffineFamilyStatement`
- `not_posComboNoCommonBoundaryRightPairOrientationStatement`
- `not_posComboNoCommonSameDegreeShiftedPairOrientationStatement`
- `not_posComboNoCommonSameDegreeOrientationNonnegStatement`
- `not_posComboNoCommonSuccDegreeOrientationNonnegStatement`

## Current Caveats

Several declarations are intentionally statement-level interfaces for classical
theorems that are not yet fully formalized here.  Recent work also found that a
sign-free Hermite-Biehler forward interface was false as stated; the theorem
`not_hermiteBiehlerForwardStatement` records the checked counterexample.

In short: this is a working research codebase, not a finished library API.
