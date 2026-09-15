import RealRooted.Applications.OEIS.A144438.LayerTotalAffineStability

/-!
# Exact successor reduction for the Deco companion data

This file expands the successor companion through its fresh-coordinate affine
extension.  Given Rayleighness of the current companion, it identifies exactly
the five remaining conditions needed for the next companion-data bundle.  It
does not assume or assert that these conditions are preserved.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Given Rayleighness of the current companion, the next companion data is
equivalent to the slope endpoint, the affine-extension Wronskians and
discriminants, and the next core/companion Wronskians and discriminants. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_of_companion
    (n : Nat)
    (hcompanion : MvPolynomial.IsRayleigh
      (decoBottomTotalWronskianCompanion n)) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      MvPolynomial.IsRayleigh (decoBottomTotalCompanionSlope n) ∧
      (∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSlope n)
          (decoBottomTotalWronskianCompanion n) i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      (∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0) := by
  constructor
  · intro hnext
    have hcompanionStep :=
      (decoBottomTotalWronskianCompanion_succ_isRayleigh_iff_affine n).1
        hnext.companion_isRayleigh
    exact ⟨hcompanionStep.2.1, hcompanionStep.2.2.1,
      hcompanionStep.2.2.2,
      hnext.coordinateWronskian_nonneg, hnext.affineDiscriminant_nonpos⟩
  · rintro ⟨hslope, hcross, hdisc, hnextCross, hnextDisc⟩
    refine ⟨?_, hnextCross, hnextDisc⟩
    exact
      (decoBottomTotalWronskianCompanion_succ_isRayleigh_iff_affine n).2
        ⟨hcompanion, hslope, hcross, hdisc⟩

/-- Preceding-rank stability discharges the successor-slope endpoint from the
exact next-data criterion. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_of_stable_companion
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hcompanion : MvPolynomial.IsRayleigh
      (decoBottomTotalWronskianCompanion n)) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSlope n)
          (decoBottomTotalWronskianCompanion n) i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      (∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0) := by
  have hslope := decoBottomTotalCompanionSlope_isRayleigh n hstable
  simpa only [hslope, true_and] using
    decoBottomTotalCompanionRayleighData_succ_iff_of_companion n hcompanion

end

end RealRooted.Applications.OEIS
