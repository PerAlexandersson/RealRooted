import RealRooted.Applications.OEIS.A144438.LayerTotalStabilityReduction
import RealRooted.Applications.OEIS.A144438.LayerTotalDiscriminantReduction
import RealRooted.MultivariateStability.AffineEulerCore

/-!
# Stability consequences for the affine Deco recurrence

This file applies the stability theory to the algebraic affine recurrence.
Assuming stability at the preceding homogeneous rank, the normal branch is
stable, its two coordinate sections are Rayleigh, and its fresh-coordinate
Wronskians are nonnegative. Thus the first-order obstruction for the full
recurrence is isolated in the exceptional branch's cross term.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- A normal bottom step on a layer total is stable whenever the corresponding
homogeneous layer total is stable. -/
theorem decoNormalBottomStep_total_mvRealStable (n : Nat)
    (hstable : MvRealStable (decoLayerTotal n)) :
    MvRealStable (decoNormalBottomStep n (decoBottomTotal n)) := by
  rw [← rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal n,
    ← rename_dehomogenize_decoNormalLayerStep_eq_decoNormalBottomStep
      (decoLayerTotal_isHomogeneous n)]
  exact ((decoNormalLayerStep_mvRealStable hstable).dehomogenize
    (decoNormalLayerStep_isHomogeneous
      (decoLayerTotal_isHomogeneous n))).rename
        (decoLayerBottomEmbedding (n + 1))

/-- An exceptional bottom step on a layer total is stable whenever the
corresponding homogeneous layer total is stable. -/
theorem decoExceptionalBottomStep_total_mvRealStable (n : Nat)
    (hstable : MvRealStable (decoLayerTotal n)) :
    MvRealStable (decoExceptionalBottomStep (decoBottomTotal n)) := by
  rw [← rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal n,
    ← rename_dehomogenize_decoExceptionalLayerStep_eq_decoExceptionalBottomStep]
  exact ((decoExceptionalLayerStep_mvRealStable hstable).dehomogenize
    (decoExceptionalLayerStep_isHomogeneous
      (decoLayerTotal_isHomogeneous n))).rename
        (decoLayerBottomEmbedding (n + 2))

/-- Under preceding-rank stability, the normal affine branch is Rayleigh. -/
theorem decoNormalBottomStep_total_isRayleigh (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh
      (decoBottomTotalAffineNormalBase n + MvPolynomial.X 1 *
        decoBottomTotalAffineSlope n) := by
  rw [← decoNormalBottomStep_total_eq_affine]
  apply MvRealStable.isRayleigh_of_isMultiaffine
    (decoNormalBottomStep_total_mvRealStable (n + 1) hstable)
  exact (decoBottomTotalAffineNormalBase_isMultiaffine n).add
    ((decoBottomTotalAffineSlope_isMultiaffine n).X_mul_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineSlope n))

/-- Under preceding-rank stability, the zero-specialized normal base is
Rayleigh. -/
theorem decoBottomTotalAffineNormalBase_isRayleigh (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh (decoBottomTotalAffineNormalBase n) := by
  apply MvRealStable.isRayleigh_of_isMultiaffine
  · unfold decoBottomTotalAffineNormalBase
    exact MvRealStable.rename
      ((decoLayerTotal_mvRealStable_iff_bottomTotal (n + 1)).mp hstable)
      (fun i : Nat => i + 1)
  · exact decoBottomTotalAffineNormalBase_isMultiaffine n

/-- Under the earlier-rank stability hypothesis, the exceptional affine base
is Rayleigh. -/
theorem decoBottomTotalAffineExceptionalBase_isRayleigh (n : Nat)
    (hstable : MvRealStable (decoLayerTotal n)) :
    MvPolynomial.IsRayleigh (decoBottomTotalAffineExceptionalBase n) := by
  apply MvRealStable.isRayleigh_of_isMultiaffine
  · simpa [decoBottomTotalAffineExceptionalBase,
      decoBottomTotalAffineExceptionalCore, decoExceptionalBottomStep] using
        decoExceptionalBottomStep_total_mvRealStable n hstable
  · exact decoBottomTotalAffineExceptionalBase_isMultiaffine n

/-- Under preceding-rank stability, the partial-derivative slope of the normal
branch is Rayleigh. -/
theorem decoBottomTotalAffineSlope_isRayleigh (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh (decoBottomTotalAffineSlope n) := by
  have h := MvPolynomial.IsRayleigh.pderiv_of_isMultiaffine
    (decoNormalBottomStep_total_isRayleigh n hstable)
      ((decoBottomTotalAffineNormalBase_isMultiaffine n).add
        ((decoBottomTotalAffineSlope_isMultiaffine n).X_mul_of_notMem_vars
          (one_notMem_vars_decoBottomTotalAffineSlope n))) 1
  rw [← decoNormalBottomStep_total_eq_affine,
    pderiv_one_decoNormalBottomStep_total] at h
  exact h

/-- Under preceding-rank stability, the normal affine slope is zero or real
stable. -/
theorem decoBottomTotalAffineSlope_mvRealStable_zero_or (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvRealStableOrZero (decoBottomTotalAffineSlope n) := by
  have hma : MvPolynomial.IsMultiaffine
      (decoNormalBottomStep (n + 1) (decoBottomTotal (n + 1))) := by
    rw [decoNormalBottomStep_total_eq_affine]
    exact (decoBottomTotalAffineNormalBase_isMultiaffine n).add
      ((decoBottomTotalAffineSlope_isMultiaffine n).X_mul_of_notMem_vars
        (one_notMem_vars_decoBottomTotalAffineSlope n))
  have h := (decoNormalBottomStep_total_mvRealStable
    (n + 1) hstable).pderiv_zero_or hma 1
  rw [pderiv_one_decoNormalBottomStep_total] at h
  exact h

/-- Under preceding-rank stability, the unshifted affine Euler core is zero
or real stable. -/
theorem decoBottomTotalCompanionCore_mvRealStable_zero_or (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvRealStableOrZero (decoBottomTotalCompanionCore n) := by
  have h := decoBottomTotalAffineSlope_mvRealStable_zero_or n hstable
  unfold decoBottomTotalAffineSlope at h
  unfold decoBottomTotalCompanionCore
  exact MvRealStableOrZero.of_rename h (by intro i j hij; lia)

/-- Under preceding-rank stability, specializing the normal affine step at
one makes the companion successor slope zero or real stable. -/
theorem decoBottomTotalCompanionSlope_mvRealStable_zero_or (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvRealStableOrZero (decoBottomTotalCompanionSlope n) := by
  have h := (decoNormalBottomStep_total_mvRealStable
    (n + 1) hstable).specializeAt_zero_or_general 1 1
  rw [decoNormalBottomStep_total_eq_affine,
    specializeAt_one_decoBottomTotalAffineNormal_eq_companionSlope] at h
  exact MvRealStableOrZero.of_rename h (by intro i j hij; lia)

/-- Under preceding-rank stability, the unshifted normal core paired with the
two-rank companion is Rayleigh. -/
theorem decoBottomTotalCompanionCore_isRayleigh (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh (decoBottomTotalCompanionCore n) := by
  have hslope := decoBottomTotalAffineSlope_isRayleigh n hstable
  unfold decoBottomTotalAffineSlope at hslope
  exact (MvPolynomial.isRayleigh_rename_iff
    (by intro i j h; lia)).mp hslope

/-- Under preceding-rank stability, specializing the normal step at one shows
that the companion successor slope is Rayleigh. -/
theorem decoBottomTotalCompanionSlope_isRayleigh (n : Nat)
    (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh (decoBottomTotalCompanionSlope n) := by
  have hspecialize :=
    (decoNormalBottomStep_total_isRayleigh n hstable).specializeAt 1 1
  rw [specializeAt_one_decoBottomTotalAffineNormal_eq_companionSlope] at hspecialize
  exact (MvPolynomial.isRayleigh_rename_iff
    (by intro i j h; lia)).1 hspecialize

/-- Stability of a homogeneous layer total orients its ordinary affine Euler
core against the bottom total.  This is the general-degree replacement for a
multiaffine argument at the homogeneous level. -/
theorem eval_coordinateWronskian_decoNormalBottomCore_total_nonneg
    (n : Nat) (hstable : MvRealStable (decoLayerTotal n)) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoNormalBottomCore n (decoBottomTotal n))
        (decoBottomTotal n) i) := by
  have hsource :=
    hstable.eval_coordinateWronskian_affineEulerCore_nonneg_of_nonnegative
      (decoLayerTotal_hasNonnegCoeffs n)
      (decoLayerTotal_isHomogeneous n) (by lia)
  have hrename := MvPolynomial.eval_coordinateWronskian_rename_nonneg
    (decoLayerBottomEmbedding n) (decoLayerBottomEmbedding n).injective
    (MvPolynomial.affineEulerCore id ((n + 1 : Nat) : Real)
      (MvPolynomial.dehomogenize (decoLayerTotal n)))
    (MvPolynomial.dehomogenize (decoLayerTotal n)) hsource
  rw [MvPolynomial.rename_affineEulerCore
      (decoLayerBottomEmbedding n) (decoLayerBottomEmbedding n).injective,
    rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal] at hrename
  simpa [decoNormalBottomCore_eq_affineEulerCore, Function.comp_def] using
    hrename

/-- Under preceding-rank stability, every coordinate Wronskian between the
normal affine slope and base is nonnegative. -/
theorem eval_coordinateWronskian_affineSlope_normalBase_nonneg
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (i : Nat) (x : Nat → Real) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n)
        (decoBottomTotalAffineNormalBase n) i) := by
  have hsource :=
    eval_coordinateWronskian_decoNormalBottomCore_total_nonneg
      (n + 1) hstable
  have hrename := MvPolynomial.eval_coordinateWronskian_rename_nonneg
    (fun j : Nat => j + 1) (by intro j k h; lia)
    (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
    (decoBottomTotal (n + 1)) hsource
  exact hrename i x

/-- The full affine Wronskians are nonnegative exactly when the exceptional
cross term does not exceed the available normal Wronskian margin. -/
theorem eval_coordinateWronskian_affineSlope_base_nonneg_iff_compensation
    (n : Nat) :
    (∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n) (decoBottomTotalAffineBase n) i)) ↔
      ∀ i x,
        -MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalAffineSlope n)
              (decoBottomTotalAffineNormalBase n) i) ≤
          MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalAffineSlope n)
              (decoBottomTotalAffineExceptionalBase n) i) := by
  constructor <;> intro h i x
  · have hbase := h i x
    rw [decoBottomTotalAffineBase,
      MvPolynomial.coordinateWronskian_add_right, map_add] at hbase
    linarith
  · rw [decoBottomTotalAffineBase,
      MvPolynomial.coordinateWronskian_add_right, map_add]
    linarith [h i x]

/-- The quantitative normal/exceptional compensation condition is exactly
nonnegativity of the lower two-rank companion Wronskians. -/
theorem eval_affineWronskian_compensation_iff_companion (n : Nat) :
    (∀ i x,
      -MvPolynomial.eval x
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalAffineSlope n)
            (decoBottomTotalAffineNormalBase n) i) ≤
        MvPolynomial.eval x
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalAffineSlope n)
            (decoBottomTotalAffineExceptionalBase n) i)) ↔
      ∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
          (decoBottomTotalWronskianCompanion n) i) :=
  (eval_coordinateWronskian_affineSlope_base_nonneg_iff_compensation n).symm.trans
    (eval_coordinateWronskian_affineSlope_base_nonneg_iff_companion n)

/-- Under preceding-rank stability, Rayleighness of the next total is exactly
the companion endpoint, companion Wronskian, and old-coordinate discriminant
package. The slope endpoint has already been discharged by stability. -/
theorem decoBottomTotal_add_two_isRayleigh_iff_stable_affine_companion
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) ↔
      MvPolynomial.IsRayleigh (decoBottomTotalWronskianCompanion n) ∧
      (∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
          (decoBottomTotalWronskianCompanion n) i)) ∧
      (∀ i j x, i ≠ 1 → j ≠ 1 → MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n) i j) ≤ 0) := by
  rw [decoBottomTotal_add_two_isRayleigh_iff_affine,
    decoBottomTotalAffineBase_isRayleigh_iff_companion,
    eval_coordinateWronskian_affineSlope_base_nonneg_iff_companion]
  simp only [decoBottomTotalAffineSlope_isRayleigh n hstable, true_and]

/-- Under preceding-rank stability, the next total is Rayleigh exactly when
the lower two-rank companion data holds.  All shifted affine coordinates have
been removed from this interface. -/
theorem decoBottomTotal_add_two_isRayleigh_iff_stable_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) ↔
      DecoBottomTotalCompanionRayleighData n := by
  constructor
  · intro hnext
    obtain ⟨hcompanion, hcross, hdisc⟩ :=
      (decoBottomTotal_add_two_isRayleigh_iff_stable_affine_companion
        n hstable).1 hnext
    exact ⟨hcompanion, hcross,
      (eval_affineRayleighDiscriminant_nonpos_iff_companion n).1 hdisc⟩
  · intro hdata
    exact (decoBottomTotal_add_two_isRayleigh_iff_stable_affine_companion
      n hstable).2 ⟨hdata.companion_isRayleigh,
        hdata.coordinateWronskian_nonneg,
        (eval_affineRayleighDiscriminant_nonpos_iff_companion n).2
          hdata.affineDiscriminant_nonpos⟩

/-- The initial lower two-rank companion data follows from the checked
rank-one and rank-two stability base cases. -/
theorem decoBottomTotalCompanionRayleighData_zero :
    DecoBottomTotalCompanionRayleighData 0 := by
  have hnext : MvPolynomial.IsRayleigh (decoBottomTotal 2) :=
    (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh 2).1
      decoLayerTotal_two_mvRealStable
  exact (decoBottomTotal_add_two_isRayleigh_iff_stable_companionData
    0 decoLayerTotal_one_mvRealStable).1 (by simpa using hnext)

/-- The lower companion data is a complete one-step Rayleigh certificate once
the preceding homogeneous rank is stable. -/
theorem decoBottomTotal_add_two_isRayleigh_of_stable_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) :=
  (decoBottomTotal_add_two_isRayleigh_iff_stable_companionData n hstable).2 hdata

/-- Preceding-rank stability discharges the slope endpoint and normal
Wronskians in the affine Rayleigh criterion. The remaining assumptions are
exactly stability compatibility of the summed base, quantitative compensation
of the exceptional cross term, and the old-coordinate discriminants. -/
theorem decoBottomTotal_add_two_isRayleigh_of_stable_affine
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hbase : MvPolynomial.IsRayleigh (decoBottomTotalAffineBase n))
    (hcomp : ∀ i x,
      -MvPolynomial.eval x
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalAffineSlope n)
            (decoBottomTotalAffineNormalBase n) i) ≤
        MvPolynomial.eval x
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalAffineSlope n)
            (decoBottomTotalAffineExceptionalBase n) i))
    (hdisc : ∀ i j x, i ≠ 1 → j ≠ 1 → MvPolynomial.eval x
      (MvPolynomial.affineRayleighDiscriminant
        (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n) i j) ≤ 0) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) := by
  exact decoBottomTotal_add_two_isRayleigh_of_affine n hbase
    (decoBottomTotalAffineSlope_isRayleigh n hstable)
    ((eval_coordinateWronskian_affineSlope_base_nonneg_iff_compensation n).mpr
      hcomp) hdisc

/-- Companion form of the stability-assisted affine criterion. It replaces
the shifted affine-base endpoint and split normal/exceptional Wronskian
bookkeeping by two exact conditions on one lower two-rank companion. -/
theorem decoBottomTotal_add_two_isRayleigh_of_stable_affine_companion
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hbase : MvPolynomial.IsRayleigh
      (decoBottomTotalWronskianCompanion n))
    (hcompanion : ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
        (decoBottomTotalWronskianCompanion n) i))
    (hdisc : ∀ i j x, i ≠ 1 → j ≠ 1 → MvPolynomial.eval x
      (MvPolynomial.affineRayleighDiscriminant
        (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n) i j) ≤ 0) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) := by
  exact (decoBottomTotal_add_two_isRayleigh_iff_stable_affine_companion
    n hstable).2 ⟨hbase, hcompanion, hdisc⟩

end

end RealRooted.Applications.OEIS
