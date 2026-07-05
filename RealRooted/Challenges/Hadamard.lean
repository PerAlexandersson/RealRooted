import RealRooted.CubicDiscriminant
import RealRooted.Hadamard

/-!
# Hadamard and Hurwitz-matrix challenge entry point

This module exposes the Garloff--Wagner, Schur--Szego, finite Polya--Schur,
and Hurwitz-matrix targets as stable names for theorem-proving sessions.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace Hadamard

/-! ## Schur--Szego and finite Polya--Schur targets -/

/-- Challenge-facing target for the fixed-degree Schur--Szego theorem. -/
abbrev finiteSchurSzegoTarget : Prop :=
  finiteSchurSzegoCompositionStatement

/-- Challenge-facing nonzero core of the fixed-degree Schur--Szego theorem. -/
abbrev finiteSchurSzegoNonzeroTarget : Prop :=
  finiteSchurSzegoCompositionNonzeroStatement

/-- Challenge-facing target for the backward finite Polya--Schur theorem. -/
abbrev finitePolyaSchurBackwardTarget : Prop :=
  finitePolyaSchurNonnegBackwardStatement

/-- Challenge-facing target for the finite Polya--Schur theorem. -/
abbrev finitePolyaSchurTarget : Prop :=
  finitePolyaSchurNonnegStatement

/-- The full fixed-degree Schur--Szego target is equivalent to its nonzero
core; zero input cases are bookkeeping. -/
theorem finiteSchurSzegoTarget_iff_nonzero :
    finiteSchurSzegoTarget ↔ finiteSchurSzegoNonzeroTarget :=
  finiteSchurSzegoCompositionStatement_iff_nonzero

/-- Challenge-facing reduction from the nonzero Schur--Szego core to the full
fixed-degree Schur--Szego target. -/
theorem finiteSchurSzegoTarget_of_nonzero
    (h : finiteSchurSzegoNonzeroTarget) :
    finiteSchurSzegoTarget :=
  finiteSchurSzegoComposition_of_nonzero h

/-- Challenge-facing reduction from the nonzero Schur--Szego core to the
backward finite Polya--Schur target. -/
theorem finitePolyaSchurBackwardTarget_of_schurSzegoNonzero
    (h : finiteSchurSzegoNonzeroTarget) :
    finitePolyaSchurBackwardTarget :=
  finitePolyaSchurNonnegBackward_of_schurSzegoNonzero h

/-- Challenge-facing reduction from the nonzero Schur--Szego core to the full
finite Polya--Schur target. -/
theorem finitePolyaSchurTarget_of_schurSzegoNonzero
    (h : finiteSchurSzegoNonzeroTarget) :
    finitePolyaSchurTarget :=
  finitePolyaSchur_nonneg_of_schurSzegoNonzero h

/-- Challenge-facing reduction from the finite Pólya--Schur theorem to the
full fixed-degree Schur--Szegő target. -/
theorem finiteSchurSzegoTarget_of_finitePolyaSchur
    (h : finitePolyaSchurTarget) :
    finiteSchurSzegoTarget :=
  finiteSchurSzegoComposition_of_finitePolyaSchur h

/-- Challenge-facing reduction from finite Pólya--Schur to the nonzero
fixed-degree Schur--Szegő core. -/
theorem finiteSchurSzegoNonzeroTarget_of_finitePolyaSchur
    (h : finitePolyaSchurTarget) :
    finiteSchurSzegoNonzeroTarget :=
  finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur h

/-- Challenge-facing equivalence between fixed-degree Schur--Szegő and finite
Pólya--Schur in the local nonnegative-coefficient convention. -/
theorem finiteSchurSzegoTarget_iff_finitePolyaSchurTarget :
    finiteSchurSzegoTarget ↔ finitePolyaSchurTarget :=
  finiteSchurSzegoCompositionStatement_iff_finitePolyaSchur

/-- Challenge-facing equivalence between the nonzero Schur--Szegő core and
finite Pólya--Schur. -/
theorem finiteSchurSzegoNonzeroTarget_iff_finitePolyaSchurTarget :
    finiteSchurSzegoNonzeroTarget ↔ finitePolyaSchurTarget :=
  finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchur

/-- Challenge-facing equivalence between the nonzero Schur--Szegő core and
the backward finite Pólya--Schur target. -/
theorem finiteSchurSzegoNonzeroTarget_iff_finitePolyaSchurBackwardTarget :
    finiteSchurSzegoNonzeroTarget ↔ finitePolyaSchurBackwardTarget :=
  finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchurBackward

/-- Challenge-facing equivalence between the full finite Pólya--Schur theorem
and its hard backward direction. -/
theorem finitePolyaSchurTarget_iff_backwardTarget :
    finitePolyaSchurTarget ↔ finitePolyaSchurBackwardTarget :=
  finitePolyaSchurNonnegStatement_iff_backward

/-- Challenge-facing reduction from the backward finite Pólya--Schur direction
to the full finite Pólya--Schur theorem. -/
theorem finitePolyaSchurTarget_of_backward
    (h : finitePolyaSchurBackwardTarget) :
    finitePolyaSchurTarget :=
  finitePolyaSchur_nonneg_of_backward h

/-- Challenge-facing extraction of the backward finite Pólya--Schur direction
from the full finite Pólya--Schur theorem. -/
theorem finitePolyaSchurBackwardTarget_of_target
    (h : finitePolyaSchurTarget) :
    finitePolyaSchurBackwardTarget :=
  finitePolyaSchur_backward_of_nonneg h

/-- Challenge-facing finite multiplier-sequence criterion from the full finite
Pólya--Schur theorem. -/
theorem finiteMultiplierSequencePair_of_jensenPolynomial
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_jensenPolynomial hFPS hgamma hjensen

/-- Challenge-facing finite multiplier-sequence criterion from the backward
finite Pólya--Schur direction. -/
theorem finiteMultiplierSequencePair_of_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_jensenPolynomial_of_backward hBack hgamma hjensen

/-- Challenge-facing PF multiplier-sequence criterion from the full finite
Pólya--Schur theorem. -/
theorem finitePFMultiplierSequencePair_of_jensenPolynomial
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_jensenPolynomial hFPS hgamma hjensen

/-- Challenge-facing PF multiplier-sequence criterion from the backward finite
Pólya--Schur direction. -/
theorem finitePFMultiplierSequencePair_of_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_jensenPolynomial_of_backward
    hBack hgamma hjensen

/-- Challenge-facing PF-preservation form of finite Pólya--Schur. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial hFPS hgamma

/-- Challenge-facing PF-preservation form of the backward finite Pólya--Schur
direction. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_of_backward hBack hgamma

/-- Challenge-facing checked low-degree Schur--Szegő base case, through
degree `2`. -/
theorem finiteSchurSzegoPair_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_two hn hf hfdeg hpdeg hsplit

/-- Challenge-facing checked low-degree nonzero Schur--Szegő base case, through
degree `2`. -/
theorem finiteSchurSzegoNonzeroPair_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ n)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_natDegree_le_two
    hn hf hf0 hfdeg hp0 hpdeg hsplit

/-- Challenge-facing checked low-degree Schur--Szegő base case for arbitrary
level when both factors have degree at most `2`. -/
theorem finiteSchurSzegoPair_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_factors_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Challenge-facing checked Schur--Szegő composition with a degree-`≤ 2` PF
factor and an arbitrary-degree splitting factor.  This strictly extends
`finiteSchurSzegoPair_of_factors_natDegree_le_two`: the splitting factor `p`
may have any degree up to the level `n`. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Challenge-facing checked low-degree nonzero Schur--Szegő base case for
arbitrary level when both factors have degree at most `2`. -/
theorem finiteSchurSzegoNonzeroPair_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_factors_natDegree_le_two
    hf hf0 hfdeg hp0 hpdeg hsplit

/-- Challenge-facing nonzero Schur--Szegő base case with a degree-`≤ 2` PF
factor and an arbitrary-degree splitting factor. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_two
    hf hf0 hfdeg hp0 hpdeg hsplit

/-- Challenge-facing checked low-degree backward finite Pólya--Schur base case,
through degree `2`. -/
theorem finitePolyaSchurBackwardPair_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  finitePolyaSchurNonnegBackward_of_natDegree_le_two hn hgamma hjensen

/-- Challenge-facing checked low-degree finite Pólya--Schur classification,
through degree `2`. -/
theorem finitePolyaSchurPair_iff_jensenPolynomial_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  finitePolyaSchur_nonneg_of_natDegree_le_two hn hgamma

/-- Challenge-facing checked low-degree PF multiplier-sequence classification,
through degree `2`. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_natDegree_le_two hn hgamma

/-- Challenge-facing finite multiplier-sequence criterion when the Jensen
polynomial itself has degree at most `2`. -/
theorem finiteMultiplierSequencePair_of_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    hjensen hjdeg

/-- Challenge-facing PF multiplier-sequence criterion when the Jensen
polynomial itself has degree at most `2`. -/
theorem finitePFMultiplierSequencePair_of_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    hgamma hjensen hjdeg

/-- Challenge-facing finite Pólya--Schur classification when the Jensen
polynomial itself has degree at most `2`. -/
theorem finitePolyaSchurPair_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFiniteMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    hgamma hjdeg

/-- Challenge-facing PF-preservation classification when the Jensen polynomial
itself has degree at most `2`. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    hgamma hjdeg

/-- Challenge-facing cubic discriminant splitting target. -/
abbrev cubicDiscriminantSplittingTarget : Prop :=
  ∀ {p : ℝ[X]}, p.natDegree = 3 → 0 ≤ cubicDiscr p → p.Splits

/-- The checked cubic discriminant criterion proves the challenge target. -/
theorem cubicDiscriminantSplittingTarget_proved :
    cubicDiscriminantSplittingTarget :=
  fun hdeg hdisc => splits_of_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing cubic discriminant splitting target through degree three. -/
abbrev cubicDiscriminantNatDegreeLeThreeTarget : Prop :=
  ∀ {p : ℝ[X]}, p.natDegree ≤ 3 → 0 ≤ cubicDiscr p → p.Splits

/-- The checked cubic discriminant criterion proves the degree-`≤ 3`
challenge target. -/
theorem cubicDiscriminantNatDegreeLeThreeTarget_proved :
    cubicDiscriminantNatDegreeLeThreeTarget :=
  fun hdeg hdisc => splits_of_natDegree_le_three_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing target for the exact-degree-three diagonal-operator
output, once its cubic discriminant is known to be nonnegative. -/
abbrev diagonalOperatorCubicDiscriminantTarget : Prop :=
  ∀ {gamma : ℕ → ℝ} {p : ℝ[X]},
    (diagonalOperator gamma p).natDegree = 3 →
    0 ≤ cubicDiscr (diagonalOperator gamma p) →
    (diagonalOperator gamma p).Splits

/-- The cubic discriminant criterion proves the exact-degree-three diagonal
operator target. -/
theorem diagonalOperatorCubicDiscriminantTarget_proved :
    diagonalOperatorCubicDiscriminantTarget :=
  fun hdeg hdisc =>
    diagonalOperator_splits_of_natDegree_three_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing target for degree-`≤ 3` diagonal-operator outputs, once
their cubic discriminant is known to be nonnegative. -/
abbrev diagonalOperatorCubicDiscriminantLeThreeTarget : Prop :=
  ∀ {gamma : ℕ → ℝ} {p : ℝ[X]},
    (diagonalOperator gamma p).natDegree ≤ 3 →
    0 ≤ cubicDiscr (diagonalOperator gamma p) →
    (diagonalOperator gamma p).Splits

/-- The degree-`≤ 3` cubic discriminant criterion proves the diagonal-operator
target. -/
theorem diagonalOperatorCubicDiscriminantLeThreeTarget_proved :
    diagonalOperatorCubicDiscriminantLeThreeTarget :=
  fun hdeg hdisc =>
    diagonalOperator_splits_of_natDegree_le_three_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing cubic Newton inequalities for an exact-degree splitting
Jensen polynomial. -/
theorem jensenPolynomialThree_logConcave_of_splits_natDegree_three
    {gamma : ℕ → ℝ}
    (hdeg : (jensenPolynomial 3 gamma).natDegree = 3)
    (hs : (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  jensenPolynomial_three_logConcave_of_splits_natDegree_three hdeg hs

/-- Challenge-facing cubic log-concavity for a Jensen polynomial that is zero
or splits. -/
theorem jensenPolynomialThree_logConcave_of_eq_zero_or_splits
    {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  jensenPolynomial_three_logConcave_of_eq_zero_or_splits hs

/-- Challenge-facing cubic log-concavity inequalities from the PF Jensen
polynomial hypothesis. -/
theorem jensenPolynomialThree_logConcave_of_isPF
    {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  hj.jensenPolynomial_three_logConcave

/-- Challenge-facing cubic log-concavity necessary condition for finite
multiplier sequences. -/
theorem finiteMultiplierSequenceThree_logConcave
    {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  finiteMultiplierSequence_three_logConcave hgamma hmult

/-- Challenge-facing cubic log-concavity necessary condition for finite PF
multiplier sequences. -/
theorem finitePFMultiplierSequenceThree_logConcave
    {gamma : ℕ → ℝ}
    (hmult : IsFinitePFMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  finitePFMultiplierSequence_three_logConcave hmult

/-! ## Garloff--Wagner and Hurwitz-matrix targets -/

/-- Challenge-facing target for Garloff--Wagner, Theorem 4(b), in the
nonnegative-coefficient proper-position form used by RealRooted. -/
abbrev garloffWagnerNonnegPrecTarget : Prop :=
  garloffWagnerHadamardNonnegPrecStatement

/-- Challenge-facing PF-polynomial strict proper-position Garloff--Wagner
target. -/
abbrev garloffWagnerPFPrecTarget : Prop :=
  garloffWagnerHadamardPFPrecStatement

/-- Challenge-facing zero-aware PF-polynomial proper-position
Garloff--Wagner target. -/
abbrev garloffWagnerPFPrec0Target : Prop :=
  garloffWagnerHadamardPFPrec0Statement

/-- Challenge-facing one-polynomial nonnegative real-rooted Hadamard target. -/
abbrev garloffWagnerNonnegRealRootedTarget : Prop :=
  garloffWagnerHadamardNonnegRealRootedStatement

/-- Challenge-facing PF-polynomial Schur--Pólya--Wagner Hadamard target. -/
abbrev schurPolyaWagnerHadamardPFTarget : Prop :=
  schurPolyaWagnerHadamardPFStatement

/-- Challenge-facing Hadamard closure target for the reciprocal-interlacing
cone. -/
abbrev hadamardReciprocalConeClosureTarget : Prop :=
  hadamardReciprocalConeClosureStatement

/-- Challenge-facing Pólya-frequency coefficientwise Hadamard closure target. -/
abbrev polyaFrequencyHadamardCoeffTarget : Prop :=
  polyaFrequencyHadamardCoeffStatement

/-- Challenge-facing target for Garloff--Wagner, Theorem 1, in the
Hurwitz-stability form. -/
abbrev hurwitzStableHadamardTarget : Prop :=
  hadamardPreservesHurwitzStableStatement

/-- Challenge-facing right-half-plane analytic core for Garloff--Wagner,
Theorem 1. -/
abbrev rightHalfPlaneStableHadamardTarget : Prop :=
  hadamardPreservesRightHalfPlaneStableStatement

/-- Challenge-facing matrix Hadamard target for Hurwitz matrices. -/
abbrev hurwitzMatrixHadamardTarget : Prop :=
  hadamardPreservesHurwitzMatrixTNStatement

/-- Challenge-facing pure Hurwitz Schur-product target. -/
abbrev hurwitzSchurTarget : Prop :=
  HurwitzMatrixSchurProductTNStatement

/-- Challenge-facing low-order Hurwitz Schur-product target through size
`3`. -/
abbrev hurwitzSchurLeThreeTarget : Prop :=
  HurwitzMatrixSchurProductDetLeThreeStatement

/-- Challenge-facing isolated in-band `3 x 3` Hurwitz Schur-product target. -/
abbrev hurwitzSchurInBandTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeInBandStatement

/-- Challenge-facing triangular-free `3 x 3` Hurwitz Schur-product target. -/
abbrev hurwitzSchurTriangularFreeTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreStatement

/-- Challenge-facing fully in-band top-right subcase of the triangular-free
`3 x 3` target. -/
abbrev hurwitzSchurFullBandTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement

/-- Challenge-facing Pólya-frequency target for the column-zero sequences.

This is the Hurwitz-specific leaf exposed by the staircase/Toeplitz normal
form: for two totally nonnegative Hurwitz matrices, the pointwise product of
their column-zero sequences should be Pólya-frequency. -/
abbrev hurwitzColumnZeroProductPFTarget : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)

/-- Challenge-facing corner-zeroed determinant subtarget for the fully in-band
top-right subcase of the triangular-free `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement

/-- Challenge-facing single-matrix determinant subtarget for the fully in-band
corner-zeroed `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement

/-- Challenge-facing column-normalized form of the single-matrix determinant
subtarget for the fully in-band corner-zeroed `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleColZeroTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement

/-- Challenge-facing first-column normal form of the single-matrix determinant
subtarget for the fully in-band corner-zeroed `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleFirstColTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement

/-- Challenge-facing strict-remainder branch of the first-column normal form. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget :
    Prop :=
  HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement

/-- Challenge-facing corner-zero top-right subcase of the triangular-free
`3 x 3` target. -/
abbrev hurwitzSchurCornerZeroTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement

/-- Challenge-facing low-order Hurwitz-matrix Hadamard target through size
`3`. -/
abbrev hurwitzMatrixHadamardLeThreeTarget : Prop :=
  hadamardPreservesHurwitzMatrixTNDetLeThreeStatement

/-- Challenge-facing odd/even PF consequence of the Hurwitz-matrix Hadamard
target. -/
abbrev hurwitzMatrixHadamardOddEvenPFTarget : Prop :=
  hadamardPreservesHurwitzMatrixOddEvenPFStatement

/-- The full Hurwitz Schur-product target implies the matrix Hadamard target. -/
theorem hurwitzMatrixHadamardTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardTarget :=
  hadamardPreservesHurwitzMatrixTN_of_schur h

/-- The matrix Hadamard target implies its odd/even PF consequence. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_matrixHadamard
    (h : hurwitzMatrixHadamardTarget) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN h

/-- The full Hurwitz Schur-product target implies the odd/even PF consequence
for Hadamard products. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_schur h

/-- Challenge-facing odd/even PF consequence from Garloff--Wagner Theorem 1
plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_stableRoute hBwd hThm1 hFwd

/-- Challenge-facing odd/even PF consequence from the right-half-plane
analytic core plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_rightHalfPlaneRoute hBwd hRHP hFwd

/-- The triangular-free `3 x 3` target is equivalent to the conjunction of
the full-band and corner-zero top-right subcases. -/
theorem hurwitzSchurTriangularFreeTarget_iff_fullBand_cornerZero :
    hurwitzSchurTriangularFreeTarget ↔
      hurwitzSchurFullBandTarget ∧ hurwitzSchurCornerZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand_cornerZero

/-- Since the corner-zero subcase is proved, the triangular-free `3 x 3` target
is equivalent to the fully in-band top-right subcase. -/
theorem hurwitzSchurTriangularFreeTarget_iff_fullBand :
    hurwitzSchurTriangularFreeTarget ↔ hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand

/-- Challenge-facing equivalence between the isolated in-band `3 x 3` target
and its triangular-free refinement. -/
theorem hurwitzSchurInBandTarget_iff_triangularFree :
    hurwitzSchurInBandTarget ↔ hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_iff_core

/-- Challenge-facing equivalence between the low-order size-`≤ 3` Hurwitz
Schur-product target and the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurLeThreeTarget_iff_inBand :
    hurwitzSchurLeThreeTarget ↔ hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetLeThree_iff_inBand

/-- Challenge-facing low-order consequence of the full Hurwitz Schur-product
target. -/
theorem hurwitzSchurLeThreeTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_schurProductTN h

/-- Challenge-facing in-band `3 x 3` consequence of the full Hurwitz
Schur-product target. -/
theorem hurwitzSchurInBandTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_schurProductTN h

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
fully in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurFullBandTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_polyaFreq hPF

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
isolated in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurInBandTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_polyaFreq hPF

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
low-order size-`≤ 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurLeThreeTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_polyaFreq hPF

/-- Challenge-facing theorem discharging the corner-zero top-right subcase. -/
theorem hurwitzSchurCornerZeroTarget_proved :
    hurwitzSchurCornerZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreCornerZero

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the fully in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroed h

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_single
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_single h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the general single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleTarget_of_colZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandCornerZeroedSingleTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero h

/-- Challenge-facing specialization from the general single-matrix leaf to the
column-normalized single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleColZeroTarget_of_single
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_single
    h

/-- Challenge-facing reduction from the first-column normal form to the
column-normalized single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleColZeroTarget_of_firstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
    h

/-- Challenge-facing specialization from the column-normalized single-matrix
leaf to the first-column normal form. -/
theorem hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_colZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_colZero
    h

/-- Challenge-facing specialization from the general single-matrix leaf to the
first-column normal form. -/
theorem hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_single
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_single
    h

/-- Challenge-facing reduction from the strict-remainder branch to the
first-column normal form. -/
theorem hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_positiveRemainder
    h

/-- Challenge-facing disproof of the first-column normal form: this branch is
too strong and should not be used as a route to the two-matrix #34 target. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol

/-- The column-normalized single-matrix leaf is false, since it specializes to
the false first-column normal form. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero

/-- The general single-matrix corner-zeroed leaf is false, since it specializes
to the false first-column normal form. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleTarget :=
  not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle

/-- The strict-remainder branch is also false, since it implies the false
first-column normal form. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget := by
  intro h
  exact not_hurwitzSchurFullBandCornerZeroedSingleFirstColTarget
    (hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_singleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_singleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleFirstCol h

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the fully in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzSchurFullBandTarget_of_cornerZeroed
    (hurwitzSchurFullBandCornerZeroedTarget_of_single h)

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the fully in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the fully
in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the two top-right subcases to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand_cornerZero hF hZ

/-- Since the corner-zero subcase is proved, the triangular-free `3 x 3` target
now reduces to the fully in-band top-right subcase alone. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzSchurTriangularFreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the two top-right subcases to the isolated
in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_core
    (hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the fully in-band top-right subcase alone to
the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzSchurInBandTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the two top-right subcases to the
low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_core
    (hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the fully in-band top-right subcase alone to
the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzSchurLeThreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the two top-right subcases to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzSchurInBandTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the isolated in-band `3 x 3` target to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_inBand
    (h : hurwitzSchurInBandTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand h

/-- Challenge-facing reduction from the low-order size-`≤ 3` Hurwitz
Schur-product target to the low-order Hurwitz-matrix Hadamard target. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchurLeThree
    (h : hurwitzSchurLeThreeTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_hurwitzLeThree h

/-- Challenge-facing low-order Hurwitz-matrix Hadamard consequence of the full
Hurwitz Schur-product target. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchurLeThree
    (hurwitzSchurLeThreeTarget_of_hurwitzSchur h)

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchurLeThree
    (hurwitzSchurLeThreeTarget_of_columnZeroProductPF hPF)

/-- Challenge-facing low-order consequence of the full Hurwitz-matrix Hadamard
target. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_matrixHadamard
    (h : hurwitzMatrixHadamardTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN h

/-- Challenge-facing reduction from the fully in-band top-right subcase alone to
the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hurwitzMatrixHadamardLeThreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingleFirstColPositiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstColPositiveRemainder h

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the Hurwitz-matrix Hadamard leaf. -/
theorem garloffWagnerNonnegPrecTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_matrixHadamardBridges
    hToFull hMatHad hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the pure Hurwitz Schur-product target. -/
theorem garloffWagnerNonnegPrecTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_hurwitzSchur
    hToFull hSchur hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the bundled classical inputs. -/
theorem garloffWagnerNonnegPrecTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_classicalInputsBundle h

/-- Challenge-facing reduction from the nonnegative two-pair statement to the
strict PF-polynomial proper-position target. -/
theorem garloffWagnerPFPrecTarget_of_nonnegPrec
    (h : garloffWagnerNonnegPrecTarget) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_nonnegPrec h

/-- Challenge-facing reduction from strict PF proper position to the zero-aware
PF proper-position target. -/
theorem garloffWagnerPFPrec0Target_of_prec
    (h : garloffWagnerPFPrecTarget) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_prec h

/-- Challenge-facing reduction from the nonnegative two-pair statement to the
zero-aware PF proper-position target. -/
theorem garloffWagnerPFPrec0Target_of_nonnegPrec
    (h : garloffWagnerNonnegPrecTarget) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_nonnegPrec h

/-- Challenge-facing reduction of the zero-aware PF target through the
Hurwitz-matrix Hadamard leaf. -/
theorem garloffWagnerPFPrec0Target_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_matrixHadamardBridges
    hToFull hMatHad hFullToPrec0

/-- Challenge-facing reduction of the zero-aware PF target through the pure
Hurwitz Schur-product target. -/
theorem garloffWagnerPFPrec0Target_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_hurwitzSchur
    hToFull hSchur hFullToPrec0

/-- Challenge-facing reduction of the zero-aware PF target through the bundled
classical inputs. -/
theorem garloffWagnerPFPrec0Target_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerPFPrec0Target_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_classicalInputsBundle h)

/-- Challenge-facing reduction from the nonnegative two-pair target to the
one-polynomial real-rooted Hadamard target. -/
theorem garloffWagnerNonnegRealRootedTarget_of_nonnegPrec
    (h : garloffWagnerNonnegPrecTarget) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec h

/-- Challenge-facing PF Schur--Pólya--Wagner target from the zero-aware PF
Garloff--Wagner wrapper. -/
theorem schurPolyaWagnerHadamardPFTarget_of_prec0
    (h : garloffWagnerPFPrec0Target) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_prec0 h

/-- Challenge-facing PF Schur--Pólya--Wagner target from the nonnegative
two-pair Garloff--Wagner target. -/
theorem schurPolyaWagnerHadamardPFTarget_of_nonnegPrec
    (h : garloffWagnerNonnegPrecTarget) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec h

/-- Challenge-facing PF Schur--Pólya--Wagner target through the Hurwitz-matrix
Hadamard leaf. -/
theorem schurPolyaWagnerHadamardPFTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_matrixHadamardBridges
    hToFull hMatHad hFullToPrec0

/-- Challenge-facing PF Schur--Pólya--Wagner target through the pure Hurwitz
Schur-product target. -/
theorem schurPolyaWagnerHadamardPFTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_hurwitzSchur hToFull hSchur hFullToPrec0

/-- Challenge-facing PF Schur--Pólya--Wagner target through the bundled
classical inputs. -/
theorem schurPolyaWagnerHadamardPFTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPFTarget_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_classicalInputsBundle h)

/-- Challenge-facing reciprocal-cone Hadamard closure from the zero-aware PF
Garloff--Wagner wrapper. -/
theorem hadamardReciprocalConeClosureTarget_of_prec0
    (h : garloffWagnerPFPrec0Target) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0 h

/-- Challenge-facing reciprocal-cone Hadamard closure from the nonnegative
two-pair Garloff--Wagner target. -/
theorem hadamardReciprocalConeClosureTarget_of_nonnegPrec
    (h : garloffWagnerNonnegPrecTarget) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_garloffWagner h

/-- Challenge-facing reciprocal-cone Hadamard closure through the
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardReciprocalConeClosureTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_matrixHadamardBridges
    hToFull hMatHad hFullToPrec0

/-- Challenge-facing reciprocal-cone Hadamard closure through the pure Hurwitz
Schur-product target. -/
theorem hadamardReciprocalConeClosureTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_hurwitzSchur hToFull hSchur hFullToPrec0

/-- Challenge-facing reciprocal-cone Hadamard closure through the bundled
classical inputs. -/
theorem hadamardReciprocalConeClosureTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosureTarget_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_classicalInputsBundle h)

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
Schur--Pólya--Wagner PF target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_schurPolyaWagner
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hSPW : schurPolyaWagnerHadamardPFTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW hSPW

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
one-polynomial nonnegative real-rooted Hadamard target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_garloffWagner_nonneg
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerNonnegRealRootedTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_garloffWagner_nonneg hASW hGW

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
nonnegative two-pair Garloff--Wagner target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_garloffWagner_nonnegPrec
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerNonnegPrecTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_garloffWagner_nonnegPrec hASW hGW

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
Hurwitz-matrix Hadamard leaf. -/
theorem polyaFrequencyHadamardCoeffTarget_of_matrixHadamardBridges
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_matrixHadamardBridges
    hASW hToFull hMatHad hFullToPrec0

/-- Challenge-facing coefficientwise Pólya-frequency closure through the pure
Hurwitz Schur-product target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_hurwitzSchur
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_hurwitzSchur
    hASW hToFull hSchur hFullToPrec0

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
bundled classical inputs. -/
theorem polyaFrequencyHadamardCoeffTarget_of_classicalInputsBundle
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (h : GarloffWagnerClassicalInputs) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeffTarget_of_garloffWagner_nonnegPrec hASW
    (garloffWagnerNonnegPrecTarget_of_classicalInputsBundle h)

end Hadamard
end Challenges
end RealRooted
