import RealRooted.Hadamard

/-!
# Hadamard and Hurwitz-matrix challenge entry point

This module exposes the Garloff--Wagner Hadamard target and the current
Hurwitz-matrix reductions as stable names for theorem-proving sessions.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace Hadamard

/-- Challenge-facing target for Garloff--Wagner, Theorem 4(b), in the
nonnegative-coefficient proper-position form used by RealRooted. -/
abbrev garloffWagnerNonnegPrecTarget : Prop :=
  garloffWagnerHadamardNonnegPrecStatement

/-- Challenge-facing target for Garloff--Wagner, Theorem 1, in the
Hurwitz-stability form. -/
abbrev hurwitzStableHadamardTarget : Prop :=
  hadamardPreservesHurwitzStableStatement

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

/-- The full Hurwitz Schur-product target implies the matrix Hadamard target. -/
theorem hurwitzMatrixHadamardTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardTarget :=
  hadamardPreservesHurwitzMatrixTN_of_schur h

/-- The triangular-free `3 x 3` target is equivalent to the conjunction of
the full-band and corner-zero top-right subcases. -/
theorem hurwitzSchurTriangularFreeTarget_iff_fullBand_cornerZero :
    hurwitzSchurTriangularFreeTarget ↔
      hurwitzSchurFullBandTarget ∧ hurwitzSchurCornerZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand_cornerZero

/-- Challenge-facing reduction from the two top-right subcases to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand_cornerZero hF hZ

/-- Challenge-facing reduction from the two top-right subcases to the isolated
in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_core
    (hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the two top-right subcases to the
low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_core
    (hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the two top-right subcases to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzSchurInBandTarget_of_fullBand_cornerZero hF hZ)

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
