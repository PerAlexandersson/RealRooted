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

/-- Challenge-facing theorem discharging the corner-zero top-right subcase. -/
theorem hurwitzSchurCornerZeroTarget_proved :
    hurwitzSchurCornerZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreCornerZero

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
  hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero
    hF hurwitzSchurCornerZeroTarget_proved

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
  hurwitzSchurInBandTarget_of_fullBand_cornerZero
    hF hurwitzSchurCornerZeroTarget_proved

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
  hurwitzSchurLeThreeTarget_of_fullBand_cornerZero
    hF hurwitzSchurCornerZeroTarget_proved

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
  hurwitzMatrixHadamardLeThreeTarget_of_fullBand_cornerZero
    hF hurwitzSchurCornerZeroTarget_proved

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
