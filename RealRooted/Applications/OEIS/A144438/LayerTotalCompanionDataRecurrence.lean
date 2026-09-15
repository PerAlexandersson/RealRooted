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

/-- The part of the successor-slope/companion Wronskian not already present
in the current companion-data Wronskian. -/
def decoBottomTotalCompanionWronskianCorrection (n i : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.X 1 * MvPolynomial.coordinateWronskian
      (decoBottomTotal (n + 1))
      (MvPolynomial.rename (fun j : Nat => j + 1) (decoBottomTotal n)) i +
    if i = 1 then
      decoBottomTotal (n + 1) *
        MvPolynomial.rename (fun j : Nat => j + 1) (decoBottomTotal n)
    else 0

/-- At coordinate `1`, the Wronskian correction factors as the shifted prior
total times the zero-section of the latest total. -/
theorem decoBottomTotalCompanionWronskianCorrection_one (n : Nat) :
    decoBottomTotalCompanionWronskianCorrection n 1 =
      MvPolynomial.rename (fun j : Nat => j + 1) (decoBottomTotal n) *
        MvPolynomial.specializeZero 1 (decoBottomTotal (n + 1)) := by
  let R := MvPolynomial.rename (fun j : Nat => j + 1) (decoBottomTotal n)
  let T := decoBottomTotal (n + 1)
  have hR : 1 ∉ R.vars := one_notMem_vars_rename_succ_decoBottomTotal n
  have hT : T = MvPolynomial.specializeZero 1 T +
      MvPolynomial.X 1 * MvPolynomial.pderiv 1 T := by
    exact MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv
      (decoBottomTotal_isMultiaffine (n + 1)) 1
  have hsection : T - MvPolynomial.X 1 * MvPolynomial.pderiv 1 T =
      MvPolynomial.specializeZero 1 T := by
    linear_combination hT
  unfold decoBottomTotalCompanionWronskianCorrection
  simp only [if_pos]
  rw [MvPolynomial.coordinateWronskian,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hR]
  change MvPolynomial.X 1 * (T * 0 - MvPolynomial.pderiv 1 T * R) +
      T * R = R * MvPolynomial.specializeZero 1 T
  calc
    _ = R * (T - MvPolynomial.X 1 * MvPolynomial.pderiv 1 T) := by ring
    _ = R * MvPolynomial.specializeZero 1 T := by rw [hsection]

/-- Away from coordinate `1`, the correction is the coordinate variable times
the Wronskian of the latest total against the shifted prior total. -/
theorem decoBottomTotalCompanionWronskianCorrection_of_ne_one
    (n i : Nat) (hi : i ≠ 1) :
    decoBottomTotalCompanionWronskianCorrection n i =
      MvPolynomial.X 1 * MvPolynomial.coordinateWronskian
        (decoBottomTotal (n + 1))
        (MvPolynomial.rename (fun j : Nat => j + 1) (decoBottomTotal n)) i := by
  unfold decoBottomTotalCompanionWronskianCorrection
  simp only [if_neg hi, add_zero]

/-- At positive recurrence rank, the coordinate-`1` correction is the shift
of the product of the latest total and the preceding companion. -/
theorem decoBottomTotalCompanionWronskianCorrection_succ_one (n : Nat) :
    decoBottomTotalCompanionWronskianCorrection (n + 1) 1 =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotal (n + 1) *
          decoBottomTotalWronskianCompanion n) := by
  rw [decoBottomTotalCompanionWronskianCorrection_one]
  rw [show n + 1 + 1 = n + 2 by lia,
    specializeZero_one_decoBottomTotal_add_two,
    decoBottomTotalAffineBase_eq_rename_wronskianCompanion,
    map_mul]

/-- The initial coordinate-`1` correction is one. -/
@[simp] theorem decoBottomTotalCompanionWronskianCorrection_zero_one :
    decoBottomTotalCompanionWronskianCorrection 0 1 = 1 := by
  rw [decoBottomTotalCompanionWronskianCorrection_one]
  rw [show 0 + 1 = 1 by rfl]
  rw [decoBottomTotal_zero, map_one, decoBottomTotal_one, one_mul,
    MvPolynomial.specializeZero_add,
    MvPolynomial.specializeZero_eq_self_of_notMem_vars 1 1 (by simp)]
  simp

/-- The successor-slope/companion Wronskian is the current data Wronskian
plus an explicit correction from the latest total and shifted prior total. -/
theorem coordinateWronskian_companionSlope_companion_eq_core_add_correction
    (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope n)
        (decoBottomTotalWronskianCompanion n) i =
      MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore n)
          (decoBottomTotalWronskianCompanion n) i +
        decoBottomTotalCompanionWronskianCorrection n i := by
  classical
  unfold decoBottomTotalCompanionSlope
    decoBottomTotalWronskianCompanion
    decoBottomTotalCompanionWronskianCorrection
  simp only [MvPolynomial.coordinateWronskian_add_left,
    MvPolynomial.coordinateWronskian_add_right,
    MvPolynomial.coordinateWronskian_self,
    MvPolynomial.coordinateWronskian_X_mul_right]
  by_cases hi : i = 1 <;> simp [hi] <;> ring

/-- Nonnegativity of every successor-slope/companion Wronskian is exactly the
condition that its explicit correction stay above the negative current-data
Wronskian margin. -/
theorem eval_coordinateWronskian_companionSlope_companion_nonneg_iff_compensation
    (n : Nat) :
    (∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope n)
        (decoBottomTotalWronskianCompanion n) i)) ↔
      ∀ i x,
        -MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalCompanionCore n)
              (decoBottomTotalWronskianCompanion n) i) ≤
          MvPolynomial.eval x
            (decoBottomTotalCompanionWronskianCorrection n i) := by
  constructor <;> intro h i x
  · have hsum := h i x
    rw [coordinateWronskian_companionSlope_companion_eq_core_add_correction,
      map_add] at hsum
    linarith
  · rw [coordinateWronskian_companionSlope_companion_eq_core_add_correction,
      map_add]
    linarith [h i x]

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

/-- Compensation form of the exact next-data criterion under preceding-rank
stability.  The first condition uses precisely the nonnegative margin already
recorded in the current companion data. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_compensation
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hcompanion : MvPolynomial.IsRayleigh
      (decoBottomTotalWronskianCompanion n)) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i x,
        -MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalCompanionCore n)
              (decoBottomTotalWronskianCompanion n) i) ≤
          MvPolynomial.eval x
            (decoBottomTotalCompanionWronskianCorrection n i)) ∧
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
  rw [decoBottomTotalCompanionRayleighData_succ_iff_of_stable_companion
    n hstable hcompanion,
    eval_coordinateWronskian_companionSlope_companion_nonneg_iff_compensation]

end

end RealRooted.Applications.OEIS
