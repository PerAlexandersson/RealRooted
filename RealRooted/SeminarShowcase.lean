/-
# Real-rooted and interlacing polynomials: seminar showcase

This file is meant to be opened during a Lean seminar.  It contains no new
proofs; the `#check` commands display the formalized statements already
available in the RealRooted library.

Run from the project root with:

  lake env lean RealRooted/SeminarShowcase.lean

or open the file in an editor with Lean support and hover over the declarations.
-/

import RealRooted

set_option linter.style.whitespace false

open Polynomial

noncomputable section

namespace RealRooted

/- ## Core vocabulary -/

/- A polynomial over `ℝ` is real-rooted if it is nonzero and its multiset of
roots has cardinality equal to its degree. -/
#check IsRealRooted

/- `Prec f g` is the strict interlacing/proper-position relation used in this
library.  The zero-aware version is `Prec0`. -/
#check Prec
#check Prec0
#check Interlaces

/- List-level root interlacing and Sturm-sequence packages. -/
#check ListInterlaces
#check ListAlternates
#check IsSturmSeq
#check IsGeneralizedSturmSeq

/- Coefficient-side hypotheses used in the nonnegative-coefficient theory. -/
#check HasNonnegCoeffs
#check HasPosLeadingCoeff

/- ## Rolle theorem / derivatives -/

/- The derivative of a real-rooted polynomial interlaces the polynomial. -/
#check derivative_interlaces

/- Between two distinct roots of a polynomial, there is a derivative root. -/
#check exists_root_derivative_between

/- Multiple roots remain roots after differentiation. -/
#check isRoot_derivative_of_rootMultiplicity_ge_two

/- ## Obreschkoff and Wagner addition -/

/- All real linear combinations of two polynomials are real-rooted or zero. -/
#check AllComboRealRooted

/- Obreschkoff, forward direction: interlacing implies all real combinations
are real-rooted or zero. -/
#check allComboRealRooted_of_prec

/- Obreschkoff, converse direction under the expected degree alternatives. -/
#check prec_of_allComboRealRooted

/- Wagner-style addition from a common left interleaver. -/
#check prec_add_of_prec_left
#check prec_sum_of_compatible_left

/- Wagner-style addition from a common right interleaver. -/
#check prec_add_of_prec_right

/- Multiplication by a common real-rooted factor preserves interlacing. -/
#check prec_mul_common_factor

/- For real-rooted polynomials with nonnegative coefficients, the roots are
nonpositive, and multiplying both sides by `X` preserves and reflects
interlacing. -/
#check hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos
#check prec_mul_X_both_of_roots_nonpos
#check prec_of_prec_mul_X_both_of_roots_nonpos

/- ## Compatibility and common interleavers -/

/- Chudnovsky--Seymour compatibility: all nonnegative combinations of a pair
are real-rooted or zero. -/
#check Compatible
#check PairwiseCompatible
#check FamilyCompatible

/- Compatibility is preserved by differentiation. -/
#check Compatible.derivative

/- Compatible positive-leading pairs have degree gap at most one. -/
#check Compatible.natDegree_close

/- Common interleavers give compatibility, and pairwise common interleavers
can be promoted to a common interleaver for a finite family. -/
#check Compatible.of_commonInterleaver
#check pairwiseCompatible_of_commonInterleaver
#check hasCommonInterleaver_of_pairwiseHasCommonInterleaver

/- A finite family with a common interleaver has a real-rooted sum. -/
#check isRealRooted_sum_of_commonInterleaver
#check isRealRooted_sum_of_commonLeftInterleaver

/- ## Interlacing sequences and matrix preservers -/

/- Branden-style interlacing sequences, with a nonnegative-coefficient package. -/
#check IsInterlacingSeq
#check IsInterlacingSeqNonneg
#check IsInterlacingSeq0Nonneg

/- The list package agrees with pairwise `Prec` and is stable under basic list
operations. -/
#check isInterlacingSeq_iff_pairwise
#check IsInterlacingSeq.sublist
#check IsInterlacingSeq.append
#check IsInterlacingSeq.reverse

/- Matrix preservers for interlacing sequences: the formalized forward
direction from the two-by-two affine test. -/
#check matrix_preserves_interlacing_seq
#check matrix_preserves_interlacing_seq0_of_2x2

/- Zero-aware necessary conditions for a matrix preserving interlacing
sequences. -/
#check matrix_preserves_interlacing_seq0_necessary_conditions

/- ## Linear operators preserving interlacing -/

/- A linear operator preserving real-rootedness or zero preserves interlacing
pairs up to order. -/
#check PreservesRealRootedOrZero
#check PreservesInterlacingPairsUpToOrder0
#check operatorPreservesInterlacingPairsUpToOrder

/- ## Favard and recurrence criteria -/

/- Favard-type three-term recurrences give interlacing orthogonal-polynomial
families. -/
#check SatisfiesFavardRecurrence
#check favardInterlacing
#check isRealRooted_of_favard
#check isGeneralizedSturmSeq_reverse_range_map_of_favard

/- Liu-Wang and Ma-Wang style criteria for producing a new interlacing
polynomial from an old one. -/
#check generalizedLiuWangCriterion
#check prec_ma_wang

/- ## Pólya frequency sequences and Veronese sections -/

/- Toeplitz total nonnegativity and Pólya-frequency sequences. -/
#check ToeplitzTotallyNonnegative
#check IsPolyaFrequencySequence
#check nonneg_of_isPolyaFrequencySequence
#check hasNonnegCoeffs_of_isPolyaFrequencySequence_coeff

/- Veronese subsequences preserve Toeplitz total nonnegativity and the
Pólya-frequency property. -/
#check veroneseSectionSeq
#check veroneseSectionPolynomial
#check toeplitzTotallyNonnegative_veroneseSectionSeq
#check isPolyaFrequencySequence_veroneseSectionSeq
#check isPolyaFrequencySequence_veroneseSectionPolynomial_coeff

/- With the Aissen--Schoenberg--Whitney equivalence supplied as hypotheses, a
real-rooted polynomial with nonnegative coefficients has real-rooted Veronese
sections. -/
#check isRealRooted_veroneseSectionPolynomial_of_realRooted_nonneg

/- The lace-matrix formulation of fully interlacing pairs is stable under
Veronese subsections. -/
#check FullyInterlacingPair
#check VeronesePairFullyInterlacing
#check FullyInterlacingPair.left_pf
#check FullyInterlacingPair.right_pf
#check fullyInterlacingPair_veronesePair
#check fullyInterlacingPair_veroneseSectionPair
#check veronesePairSectionSeq
#check veronesePairSectionPolynomial
#check VeronesePairFullyInterlacing.sectionPair
#check VeronesePairFullyInterlacing.sectionPair_fin
#check fullyInterlacingPair_veroneseSectionPairwise
#check fullyInterlacingPair_veroneseSectionPairwise_fin
#check prec0_veroneseSectionPolynomial_of_prec
#check prec_veroneseSectionPolynomial_of_prec
#check prec0_veronesePairSectionPolynomial_of_prec
#check prec_veronesePairSectionPolynomial_of_prec
#check prec0_veronesePairSectionPolynomial_fin_of_prec
#check prec_veronesePairSectionPolynomial_fin_of_prec

end RealRooted
