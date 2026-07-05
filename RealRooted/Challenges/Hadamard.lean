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

/-! ## Garloff--Wagner and Hurwitz-matrix targets -/

/-- Challenge-facing target for Garloff--Wagner, Theorem 4(b), in the
nonnegative-coefficient proper-position form used by RealRooted. -/
abbrev garloffWagnerNonnegPrecTarget : Prop :=
  garloffWagnerHadamardNonnegPrecStatement

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

end Hadamard
end Challenges
end RealRooted
