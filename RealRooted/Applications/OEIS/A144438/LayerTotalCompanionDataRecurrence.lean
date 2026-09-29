import RealRooted.Applications.OEIS.A144438.LayerTotalAffineStability
import RealRooted.Applications.OEIS.A144438.LayerTotalCompanionCoreQuadratic
import RealRooted.Mathlib.Algebra.MvPolynomial.Degrees
import RealRooted.MultivariateStability.AffineEulerCore
import RealRooted.MultivariateStability.AllCombo
import RealRooted.MultivariateStability.RayleighPencil

/-!
# Exact successor reduction for the Deco companion data

This file expands the successor companion through its fresh-coordinate affine
extension.  Given Rayleighness of the current companion, it identifies exactly
the five remaining conditions needed for the next companion-data bundle.  It
does not assume or assert that these conditions are preserved.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Stability of the next homogeneous layer makes the unshifted companion
extension core Rayleigh. -/
theorem decoBottomTotalCompanionExtensionCore_isRayleigh_of_stable
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 2))) :
    MvPolynomial.IsRayleigh
      (decoBottomTotalCompanionExtensionCore n) := by
  have hcore := decoBottomTotalCompanionCore_isRayleigh (n + 1)
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hstable)
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore] at hcore
  exact (MvPolynomial.isRayleigh_rename_iff
    (by intro i j h; lia)).mp hcore

/-- A completed stability/data step makes the next unshifted extension core
Rayleigh, without adding a new induction hypothesis. -/
theorem
    decoBottomTotalCompanionExtensionCore_isRayleigh_of_stable_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    MvPolynomial.IsRayleigh
      (decoBottomTotalCompanionExtensionCore n) := by
  have hbottom :=
    decoBottomTotal_add_two_isRayleigh_of_stable_companionData
      n hstable hdata
  have hnextStable : MvRealStable (decoLayerTotal (n + 2)) :=
    (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n + 2)).mpr
      hbottom
  exact decoBottomTotalCompanionExtensionCore_isRayleigh_of_stable
    n hnextStable

/-- A completed stability/data step orients the next unshifted companion core
against the total extension from which its affine Euler recurrence is built. -/
theorem
    eval_coordinateWronskian_companionExtensionCore_totalExtension_nonneg_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionExtensionCore n)
        (decoBottomTotalCompanionTotalExtension n) i) := by
  have hbottom :=
    decoBottomTotal_add_two_isRayleigh_of_stable_companionData
      n hstable hdata
  have hnextStable : MvRealStable (decoLayerTotal (n + 2)) :=
    (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n + 2)).mpr
      hbottom
  exact
    eval_coordinateWronskian_companionExtensionCore_totalExtension_nonneg_of_stable
      n hnextStable

/-- A completed stability/data step also supplies the nonnegative
second-derivative reserve in each next quadratic recurrence. -/
theorem
    eval_affineEulerRayleighRow_companionExtensionCore_nonneg_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.affineEulerRayleighRow
        (Fin.valEmbedding : Fin (n + 2) → Nat)
        (decoBottomTotalCompanionExtensionCore n) i) := by
  have hbottom :=
    decoBottomTotal_add_two_isRayleigh_of_stable_companionData
      n hstable hdata
  have hnextStable : MvRealStable (decoLayerTotal (n + 2)) :=
    (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n + 2)).mpr
      hbottom
  exact
    eval_affineEulerRayleighRow_companionExtensionCore_nonneg_of_stable
      n hnextStable

/-- Stability of the next homogeneous layer automatically supplies every
occupied-coordinate quadratic coefficient in the following recurrence. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_nonneg_of_stable
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 2))) :
    ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i) := by
  intro i x
  exact
    eval_coordinateWronskian_successorCoreSlopeRecurrence_successorSlopeRecurrence_nonneg_of_stable
      n hstable (i + 1 : Nat) x

/-- Stability of the associated homogeneous layer automatically supplies all
leading coefficients of the current successor-core row quadratics. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_nonneg_of_stable
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1))) :
    ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i) := by
  let completeOrientation :=
    eval_coordinateWronskian_successorCoreSlopeRecurrence_successorSlopeRecurrence_nonneg_of_stable
  cases n with
  | zero =>
      intro i x
      simp
  | succ n =>
      intro i
      apply
        (eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_nonneg_iff_recurrenceAt
          n i).mpr
      intro x
      simpa [decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrenceAt] using
        completeOrientation n
          (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hstable) (i : Nat) x

/-- A completed stability/data step makes every affine-Euler base-row
discriminant nonpositive, so its negation is an available nonnegative margin. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowBaseDiscriminant_nonpos_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i : Fin (n + 1), ∀ x,
      MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowBaseDiscriminant n i) ≤ 0 := by
  have hbottom :=
    decoBottomTotal_add_two_isRayleigh_of_stable_companionData
      n hstable hdata
  have hnextStable : MvRealStable (decoLayerTotal (n + 2)) :=
    (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n + 2)).mpr
      hbottom
  exact
    eval_decoBottomTotalCompanionSuccessorCoreRowBaseDiscriminant_nonpos_of_stable
      n hnextStable

/-- A completed stability/data step makes the sum of both adjacent-derivative
orientation reserves in a next quadratic recurrence nonnegative. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowOrientationReserveRecurrence_nonneg
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowOrientationReserveRecurrence
        n i) := by
  intro i x
  rw [decoBottomTotalCompanionSuccessorCoreRowOrientationReserveRecurrence,
    map_add]
  exact add_nonneg
    (eval_coordinateWronskian_companionExtensionCore_totalExtension_nonneg_of_companionData
      n hstable hdata (i + 1 : Nat) x)
    (eval_affineEulerRayleighRow_companionExtensionCore_nonneg_of_companionData
      n hstable hdata i.succ x)

/-- Algebraically, nonnegativity of a next quadratic recurrence is equivalent
to its gap-two mixed Wronskian staying above the negative adjacent-orientation
reserve.  The stability theorem above supplies this inequality automatically. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_nonneg_iff_secondMixed
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i)) ↔
      ∀ x,
        -MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowOrientationReserveRecurrence
              n i) ≤
          MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowSecondMixedRecurrence
              n i) := by
  constructor <;> intro h x
  · have hsum := h x
    rw [
      decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_eq_mixed_add_reserve,
      map_add] at hsum
    linarith
  · rw [
      decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_eq_mixed_add_reserve,
      map_add]
    linarith [h x]

/-- Nonnegativity of a next quadratic recurrence is exactly the requirement
that its mixed second-derivative Wronskian not exhaust the affine-Euler row
reserve. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_nonneg_iff
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i)) ↔
      ∀ x,
        -MvPolynomial.eval x
            (MvPolynomial.affineEulerRayleighRow
              (Fin.valEmbedding : Fin (n + 2) → Nat)
              (decoBottomTotalCompanionExtensionCore n) i.succ) ≤
          MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (MvPolynomial.affineEulerCore
                (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 3 : Real)
                (decoBottomTotalCompanionExtensionCore n))
              (decoBottomTotalCompanionTotalExtension n)
              (i + 1 : Nat)) := by
  constructor <;> intro h x
  · have hsum := h x
    rw [decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_eq_add,
      map_add] at hsum
    linarith
  · rw [decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_eq_add,
      map_add]
    linarith [h x]

/-- Thus every affine-Euler row forming the base of a successor core row is
globally nonnegative; only its fresh-coordinate correction remains to be
controlled in the full successor Wronskian. -/
theorem eval_decoBottomTotalCompanionExtensionRayleighRow_nonneg_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionExtensionRayleighRow n i) := by
  intro i x
  rw [← coordinateWronskian_companionExtensionCore_totalExtension]
  exact
    eval_coordinateWronskian_companionExtensionCore_totalExtension_nonneg_of_companionData
      n hstable hdata (i + 1 : Nat) x

/-- A completed stability/data step automatically supplies the constant
coefficient condition for every successor-row quadratic. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowConstant_nonneg_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowConstant n i) := by
  intro i x
  have hbase :=
    eval_decoBottomTotalCompanionExtensionRayleighRow_nonneg_of_companionData
      n hstable hdata i (Function.update x 0 0)
  rw [← MvPolynomial.eval_specializeAt,
    specializeAt_zero_decoBottomTotalCompanionExtensionRayleighRow] at hbase
  exact hbase

/-- With current stability and companion data, the endpoint criterion first
reduces to its quadratic and discriminant conditions; the constant
coefficients are automatic. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff_quadratic_discriminant
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    (∀ i : Fin (n + 1), ∀ x,
      0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      (∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)) ∧
      ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0 := by
  rw [eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff]
  constructor
  · intro h
    exact ⟨h.quadratic_nonneg, h.discriminant_nonpos⟩
  · rintro ⟨hquadratic, hdiscriminant⟩
    exact ⟨hquadratic,
      eval_decoBottomTotalCompanionSuccessorCoreRowConstant_nonneg_of_companionData
        n hstable hdata,
      hdiscriminant⟩

/-- Stability also supplies the leading coefficients, so nonnegativity of all
successor core rows is equivalent to the discriminant bounds alone. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff_discriminant
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    (∀ i : Fin (n + 1), ∀ x,
      0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0 := by
  rw [eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff_quadratic_discriminant
    n hstable hdata]
  constructor
  · exact And.right
  · intro hdiscriminant
    exact ⟨
      eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_nonneg_of_stable
        n hstable,
      hdiscriminant⟩

/-- After the automatic endpoint coefficients are discharged, successor-row
nonnegativity is exactly the requirement that the latest-bottom-total slope
correction fit inside the affine-Euler base-discriminant margin. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff_correction
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    (∀ i : Fin (n + 1), ∀ x,
      0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      ∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantSlopeCorrection
              n i) ≤
          -MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowBaseDiscriminant n i) := by
  rw [eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff_discriminant
    n hstable hdata]
  constructor <;> intro h i x
  · exact
      (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminant_nonpos_iff_correction
        n i x).mp (h i x)
  · exact
      (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminant_nonpos_iff_correction
        n i x).mpr (h i x)

/-- Under a completed stability/data step, the expanded endpoint package also
forgets its automatic constant-coefficient condition. -/
theorem
    decoBottomTotalCompanionSuccessorCoreEndpointData_iff_quadratic_discriminant
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionSuccessorCoreEndpointData n ↔
      (∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)) ∧
      ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0 := by
  rw [← decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_endpointData]
  constructor
  · intro h
    exact ⟨h.quadratic_nonneg, h.discriminant_nonpos⟩
  · rintro ⟨hquadratic, hdiscriminant⟩
    exact ⟨hquadratic,
      eval_decoBottomTotalCompanionSuccessorCoreRowConstant_nonneg_of_companionData
        n hstable hdata,
      hdiscriminant⟩

/-- Under a completed stability/data step, the expanded endpoint package is
equivalent to the successor-row discriminant bounds alone. -/
theorem decoBottomTotalCompanionSuccessorCoreEndpointData_iff_discriminant
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionSuccessorCoreEndpointData n ↔
      ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0 := by
  rw [decoBottomTotalCompanionSuccessorCoreEndpointData_iff_quadratic_discriminant
    n hstable hdata]
  constructor
  · exact And.right
  · intro hdiscriminant
    exact ⟨
      eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_nonneg_of_stable
        n hstable,
      hdiscriminant⟩

/-- A completed stability/data step places the current companion and its
affine Euler core in one weakly stable real span. -/
theorem decoBottomTotalCompanion_allCombo_core_of_stable_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    AllComboMvRealStableOrZero
      (decoBottomTotalWronskianCompanion n)
      (decoBottomTotalCompanionCore n) := by
  have hbottomRayleigh :=
    decoBottomTotal_add_two_isRayleigh_of_stable_companionData
      n hstable hdata
  have hbottomStable : MvRealStable (decoBottomTotal (n + 2)) :=
    (decoBottomTotal_mvRealStable_iff_isRayleigh (n + 2)).mpr
      hbottomRayleigh
  rw [decoBottomTotal_add_two_eq_rename_companionTotalExtension] at hbottomStable
  have hextension : MvRealStable
      (decoBottomTotalCompanionTotalExtension n) :=
    hbottomStable.of_rename (by intro i j hij; lia)
  apply allComboMvRealStableOrZero_of_affine
  · exact decoBottomTotalCompanionCore_mvRealStable_zero_or n hstable
  · intro t
    have hspecialize := hextension.specializeAt_zero_or_general 0 t
    unfold decoBottomTotalCompanionTotalExtension at hspecialize
    rw [MvPolynomial.specializeAt_add,
      MvPolynomial.specializeAt_eq_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalWronskianCompanion n),
      MvPolynomial.specializeAt_mul, MvPolynomial.specializeAt_X,
      MvPolynomial.specializeAt_eq_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionCore n)] at hspecialize
    exact hspecialize

/-- Stability of the finite homogeneous layer total places its unshifted
dehomogenized total extension and affine Euler core in one weakly stable
real span. -/
theorem decoBottomTotalCompanionTotalExtension_allCombo_extensionCore
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 2))) :
    AllComboMvRealStableOrZero
      (decoBottomTotalCompanionTotalExtension n)
      (decoBottomTotalCompanionExtensionCore n) := by
  let Q := MvPolynomial.dehomogenize (decoLayerTotal (n + 2))
  have hQstable : MvRealStable Q :=
    hstable.dehomogenize (decoLayerTotal_isHomogeneous (n + 2))
  have hQnn : MvPolynomial.HasNonnegCoeffs Q :=
    (decoLayerTotal_hasNonnegCoeffs (n + 2)).dehomogenize
  have hQma : MvPolynomial.IsMultiaffine Q := by
    apply MvPolynomial.IsMultiaffine.of_rename
      (f := decoLayerBottomEmbedding (n + 2))
    · rw [rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal]
      exact decoBottomTotal_isMultiaffine (n + 2)
    · exact (decoLayerBottomEmbedding (n + 2)).injective
  have hQdeg : Q.totalDegree ≤ n + 3 := by
    calc
      Q.totalDegree ≤ ∑ i, Q.degreeOf i :=
        MvPolynomial.totalDegree_le_sum_degreeOf Q
      _ ≤ ∑ _i : Fin (n + 2), 1 :=
        Finset.sum_le_sum fun i _ => hQma i
      _ ≤ n + 3 := by simp
  have hall := hQstable.allCombo_affineEulerCore hQnn hQdeg
  have hallRename := hall.rename
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
  rw [← decoBottomTotalCompanionTotalExtension_eq_rename_dehomogenize]
    at hallRename
  have hcore :
      MvPolynomial.rename (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
          (MvPolynomial.affineEulerCore id ((n + 3 : Nat) : Real) Q) =
        MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) ((n + 3 : Nat) : Real)
          (MvPolynomial.rename (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Q) := by
    simpa only [Function.comp_id] using
      MvPolynomial.rename_affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
        Fin.valEmbedding.injective id ((n + 3 : Nat) : Real) Q
  rw [hcore,
    ← decoBottomTotalCompanionTotalExtension_eq_rename_dehomogenize]
    at hallRename
  unfold decoBottomTotalCompanionExtensionCore
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hallRename

/-- A completed stability/data step transports the stable span through the
affine Euler operator to the current total extension and the next unshifted
companion core. -/
theorem
    decoBottomTotalCompanionTotalExtension_allCombo_extensionCore_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    AllComboMvRealStableOrZero
      (decoBottomTotalCompanionTotalExtension n)
      (decoBottomTotalCompanionExtensionCore n) := by
  have hbottom :=
    decoBottomTotal_add_two_isRayleigh_of_stable_companionData
      n hstable hdata
  have hnextStable : MvRealStable (decoLayerTotal (n + 2)) :=
    (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n + 2)).mpr
      hbottom
  exact decoBottomTotalCompanionTotalExtension_allCombo_extensionCore
    n hnextStable

/-- After a completed step, the next unshifted companion core and successor
slope recurrence lie in the same weakly stable real span. -/
theorem
    decoBottomTotalCompanionExtensionCore_allCombo_successorSlope_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    AllComboMvRealStableOrZero
      (decoBottomTotalCompanionExtensionCore n)
      (decoBottomTotalCompanionSuccessorSlopeRecurrence n) := by
  have hall :=
    decoBottomTotalCompanionTotalExtension_allCombo_extensionCore_of_companionData
      n hstable hdata
  apply hall.linearRecombination (a := 0) (b := 1) (c := 1) (d := 1)
  · simp
  · unfold decoBottomTotalCompanionSuccessorSlopeRecurrence
    simp

/-- In the actual positive-coordinate recurrence, a completed step places
the next companion core and next companion slope in one weakly stable real
span. -/
theorem decoBottomTotalCompanionCore_allCombo_slope_succ_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    AllComboMvRealStableOrZero
      (decoBottomTotalCompanionCore (n + 1))
      (decoBottomTotalCompanionSlope (n + 1)) := by
  have hall :=
    (decoBottomTotalCompanionExtensionCore_allCombo_successorSlope_of_companionData
      n hstable hdata).rename (fun j : Nat => j + 1)
  rw [← decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
    ← decoBottomTotalCompanionSlope_succ_eq_rename] at hall
  exact hall

/-- The stable next-core/next-slope span automatically discharges all of its
affine Rayleigh discriminants.  An oriented Wronskian condition is the only
additional datum needed to glue this pair along a fresh coordinate. -/
theorem
    eval_affineRayleighDiscriminant_companionCore_slope_succ_nonpos_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i j x, MvPolynomial.eval x
      (MvPolynomial.affineRayleighDiscriminant
        (decoBottomTotalCompanionCore (n + 1))
        (decoBottomTotalCompanionSlope (n + 1)) i j) ≤ 0 := by
  exact
    (decoBottomTotalCompanionCore_allCombo_slope_succ_of_companionData
      n hstable hdata).eval_affineRayleighDiscriminant_nonpos
        (decoBottomTotalCompanionCore_isMultiaffine (n + 1))
        (decoBottomTotalCompanionSlope_isMultiaffine (n + 1))

/-- After one completed stability/data step, every current core-pair
cross-Wronskian has the sign required by the fresh-coordinate Rayleigh
criterion. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreCoreCross_nonneg_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross n i) := by
  have hcore :=
    decoBottomTotalCompanionExtensionCore_isRayleigh_of_stable_companionData
      n hstable hdata
  have hcriterion :=
    (decoBottomTotalCompanionExtensionCore_isRayleigh_iff_affine n).mp hcore
  intro i x
  exact hcriterion.2.2.1 (i + 1 : Nat) x

/-- Equivalently, after one completed stability/data step every current
core-pair Plücker factor is nonpositive. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreCoreFactor_nonpos_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreFactor n i) ≤
        0 := by
  intro i x
  exact
    (eval_decoBottomTotalCompanionSuccessorCoreCoreFactor_nonpos_iff_cross
      n i x).mpr
        (eval_decoBottomTotalCompanionSuccessorCoreCoreCross_nonneg_of_companionData
          n hstable hdata i x)

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
  have hR : 1 ∉ R.vars := one_notMem_vars_rename_succ_decoBottomTotal n
  have hRma : R.IsMultiaffine :=
    (decoBottomTotal_isMultiaffine n).rename
      (f := fun j : Nat => j + 1) (by intro i j hij; lia)
  have hTdecomp :=
    MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv
      (decoBottomTotal_isMultiaffine (n + 1)) 1
  unfold decoBottomTotalCompanionWronskianCorrection
  simp only [ite_eq_left]
  rw [MvPolynomial.IsMultiaffine.coordinateWronskian_eq_specializeZero
      (decoBottomTotal_isMultiaffine (n + 1)) hRma 1,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hR,
    MvPolynomial.specializeZero_eq_self_of_notMem_vars 1 R hR]
  simp only [mul_zero, zero_sub, mul_neg]
  linear_combination R * hTdecomp

/-- The coordinate-`1` correction is itself independent of coordinate `1`. -/
theorem one_notMem_vars_decoBottomTotalCompanionWronskianCorrection
    (n : Nat) :
    1 ∉ (decoBottomTotalCompanionWronskianCorrection n 1).vars := by
  rw [decoBottomTotalCompanionWronskianCorrection_one]
  intro hi
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hi) with
    hiRename | hiSection
  · exact one_notMem_vars_rename_succ_decoBottomTotal n hiRename
  · have hiErase := MvPolynomial.vars_specializeZero_subset_erase
      (decoBottomTotal (n + 1)) 1 hiSection
    exact (Finset.mem_erase.mp hiErase).1 rfl

/-- Away from coordinate `1`, the correction is the coordinate variable times
the Wronskian of the latest total against the shifted prior total. -/
theorem decoBottomTotalCompanionWronskianCorrection_of_ne_one
    (n i : Nat) (hi : i ≠ 1) :
    decoBottomTotalCompanionWronskianCorrection n i =
      MvPolynomial.X 1 * MvPolynomial.coordinateWronskian
        (decoBottomTotal (n + 1))
        (MvPolynomial.rename (fun j : Nat => j + 1) (decoBottomTotal n)) i := by
  unfold decoBottomTotalCompanionWronskianCorrection
  simp only [ite_eq_right hi, add_zero]

/-- At rank zero, every correction in coordinates `2, 3, ...` vanishes. -/
@[simp] theorem decoBottomTotalCompanionWronskianCorrection_zero_add_two
    (i : Nat) :
    decoBottomTotalCompanionWronskianCorrection 0 (i + 2) = 0 := by
  rw [decoBottomTotalCompanionWronskianCorrection_of_ne_one 0 (i + 2)
    (by lia)]
  simp [decoBottomTotal_zero, decoBottomTotal_one,
    MvPolynomial.coordinateWronskian]

/-- At positive rank, every coordinate `i + 2` correction is `X 1` times
the shifted lower Wronskian of the prior companion-total extension against
the latest total. -/
theorem decoBottomTotalCompanionWronskianCorrection_succ_add_two
    (n i : Nat) :
    decoBottomTotalCompanionWronskianCorrection (n + 1) (i + 2) =
      MvPolynomial.X 1 * MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionTotalExtension n)
          (decoBottomTotal (n + 1)) (i + 1)) := by
  rw [decoBottomTotalCompanionWronskianCorrection_of_ne_one
    (n + 1) (i + 2) (by lia)]
  rw [show n + 1 + 1 = n + 2 by lia,
    decoBottomTotal_add_two_eq_rename_companionTotalExtension]
  simpa only [Nat.add_assoc] using congrArg (MvPolynomial.X 1 * ·)
    (MvPolynomial.coordinateWronskian_rename (fun j : Nat => j + 1)
      (by intro j k hjk; lia)
      (decoBottomTotalCompanionTotalExtension n)
      (decoBottomTotal (n + 1)) (i + 1))

/-- Evaluation of a positive-rank coordinate-`i+2` correction is the value of
`X 1` times the lower Wronskian under the shifted assignment. -/
theorem eval_decoBottomTotalCompanionWronskianCorrection_succ_add_two
    (n i : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (decoBottomTotalCompanionWronskianCorrection (n + 1) (i + 2)) =
      x 1 * MvPolynomial.eval (fun j => x (j + 1))
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionTotalExtension n)
          (decoBottomTotal (n + 1)) (i + 1)) := by
  rw [decoBottomTotalCompanionWronskianCorrection_succ_add_two,
    MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename]
  rfl

/-- The lower Wronskian governing coordinate `i + 2` splits along the fresh
coordinate-`0` companion-total extension. -/
theorem coordinateWronskian_companionTotalExtension_total_succ_add_one
    (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionTotalExtension n)
        (decoBottomTotal (n + 1)) (i + 1) =
      MvPolynomial.coordinateWronskian
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotal (n + 1)) (i + 1) +
        MvPolynomial.X 0 * MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore n)
          (decoBottomTotal (n + 1)) (i + 1) := by
  unfold decoBottomTotalCompanionTotalExtension
  rw [MvPolynomial.coordinateWronskian_add_left,
    MvPolynomial.coordinateWronskian_X_mul_left]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    sub_zero]

/-- Consequently, a positive-rank coordinate-`i + 2` correction is a
quadratic in `X 1` whose coefficients are lower companion/total and
core/total Wronskians. -/
theorem decoBottomTotalCompanionWronskianCorrection_succ_add_two_eq_split
    (n i : Nat) :
    decoBottomTotalCompanionWronskianCorrection (n + 1) (i + 2) =
      MvPolynomial.X 1 *
        (MvPolynomial.rename (fun j : Nat => j + 1)
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalWronskianCompanion n)
              (decoBottomTotal (n + 1)) (i + 1)) +
          MvPolynomial.X 1 *
            MvPolynomial.rename (fun j : Nat => j + 1)
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalCompanionCore n)
                (decoBottomTotal (n + 1)) (i + 1))) := by
  rw [decoBottomTotalCompanionWronskianCorrection_succ_add_two,
    coordinateWronskian_companionTotalExtension_total_succ_add_one]
  simp only [map_add, map_mul, MvPolynomial.rename_X, zero_add]

/-- Evaluation exposes the same correction as `x 1` times an affine function
of `x 1`, with both coefficients evaluated at the shifted assignment. -/
theorem eval_decoBottomTotalCompanionWronskianCorrection_succ_add_two_eq_split
    (n i : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (decoBottomTotalCompanionWronskianCorrection (n + 1) (i + 2)) =
      x 1 *
        (MvPolynomial.eval (fun j => x (j + 1))
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalWronskianCompanion n)
              (decoBottomTotal (n + 1)) (i + 1)) +
          x 1 * MvPolynomial.eval (fun j => x (j + 1))
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalCompanionCore n)
              (decoBottomTotal (n + 1)) (i + 1))) := by
  rw [decoBottomTotalCompanionWronskianCorrection_succ_add_two_eq_split,
    MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, MvPolynomial.eval_rename]
  rfl

/-- The correction vanishes outside the ordinary support interval of the
latest total and companion. -/
theorem decoBottomTotalCompanionWronskianCorrection_eq_zero_of_notMem_Icc
    (n i : Nat) (hi : i ∉ Finset.Icc 1 (n + 1)) :
    decoBottomTotalCompanionWronskianCorrection n i = 0 := by
  have hi1 : i ≠ 1 := by
    intro hiEq
    subst i
    exact hi (Finset.mem_Icc.mpr ⟨le_rfl, by lia⟩)
  rw [decoBottomTotalCompanionWronskianCorrection_of_ne_one n i hi1]
  have hiTotal : i ∉ (decoBottomTotal (n + 1)).vars := by
    intro hiVars
    exact hi (vars_decoBottomTotal_subset_Icc (n + 1) hiVars)
  have hiRename : i ∉ (MvPolynomial.rename (fun j : Nat => j + 1)
      (decoBottomTotal n)).vars := by
    intro hiVars
    obtain ⟨j, hj, hji⟩ := MvPolynomial.mem_vars_rename
      (fun j : Nat => j + 1) (decoBottomTotal n) hiVars
    have hjBounds := vars_decoBottomTotal_subset_Icc n hj
    rw [Finset.mem_Icc] at hjBounds
    apply hi
    rw [Finset.mem_Icc, ← hji]
    constructor <;> lia
  rw [MvPolynomial.coordinateWronskian_eq_zero_of_notMem_vars
    hiTotal hiRename, mul_zero]

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

/-- The complete successor Wronskian in coordinate `i + 2` is a quadratic in
`X 1` over three lower unshifted Wronskians. -/
theorem coordinateWronskian_companionSlope_companion_succ_add_two_eq_split
    (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope (n + 1))
        (decoBottomTotalWronskianCompanion (n + 1)) (i + 2) =
      MvPolynomial.rename (fun j : Nat => j + 1)
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalCompanionExtensionCore n)
            (decoBottomTotalCompanionSuccessorExtension n) (i + 1)) +
        MvPolynomial.X 1 *
          (MvPolynomial.rename (fun j : Nat => j + 1)
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalWronskianCompanion n)
                (decoBottomTotal (n + 1)) (i + 1)) +
            MvPolynomial.X 1 *
              MvPolynomial.rename (fun j : Nat => j + 1)
                (MvPolynomial.coordinateWronskian
                  (decoBottomTotalCompanionCore n)
                  (decoBottomTotal (n + 1)) (i + 1))) := by
  rw [coordinateWronskian_companionSlope_companion_eq_core_add_correction,
    coordinateWronskian_companionCore_companion_succ_add_two,
    decoBottomTotalCompanionWronskianCorrection_succ_add_two_eq_split]

/-- On every occupied positive coordinate, the constant coefficient in the
successor quadratic is the named lower affine-Euler core row. -/
theorem coordinateWronskian_companionSlope_companion_succ_fin_eq_split
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope (n + 1))
        (decoBottomTotalWronskianCompanion (n + 1)) (i + 2 : Nat) =
      MvPolynomial.rename (fun j : Nat => j + 1)
          (decoBottomTotalCompanionSuccessorCoreRow n i) +
        MvPolynomial.X 1 *
          (MvPolynomial.rename (fun j : Nat => j + 1)
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalWronskianCompanion n)
                (decoBottomTotal (n + 1)) (i + 1 : Nat)) +
            MvPolynomial.X 1 *
              MvPolynomial.rename (fun j : Nat => j + 1)
                (MvPolynomial.coordinateWronskian
                  (decoBottomTotalCompanionCore n)
                  (decoBottomTotal (n + 1)) (i + 1 : Nat))) := by
  rw [coordinateWronskian_companionSlope_companion_succ_add_two_eq_split,
    coordinateWronskian_companionExtensionCore_successorExtension]

/-- Evaluation of the bounded successor split exposes the lower core row and
the two remaining Wronskians under the shifted assignment. -/
theorem eval_coordinateWronskian_companionSlope_companion_succ_fin_eq_split
    (n : Nat) (i : Fin (n + 1)) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSlope (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) (i + 2 : Nat)) =
      MvPolynomial.eval (fun j => x (j + 1))
          (decoBottomTotalCompanionSuccessorCoreRow n i) +
        x 1 *
          (MvPolynomial.eval (fun j => x (j + 1))
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalWronskianCompanion n)
                (decoBottomTotal (n + 1)) (i + 1 : Nat)) +
            x 1 * MvPolynomial.eval (fun j => x (j + 1))
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalCompanionCore n)
                (decoBottomTotal (n + 1)) (i + 1 : Nat))) := by
  rw [coordinateWronskian_companionSlope_companion_succ_fin_eq_split,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, MvPolynomial.eval_rename,
    MvPolynomial.eval_rename]
  rfl

/-- Evaluation gives the lower three-Wronskian quadratic under the shifted
assignment. -/
theorem eval_coordinateWronskian_companionSlope_companion_succ_add_two_eq_split
    (n i : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSlope (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) (i + 2)) =
      MvPolynomial.eval (fun j => x (j + 1))
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalCompanionExtensionCore n)
            (decoBottomTotalCompanionSuccessorExtension n) (i + 1)) +
        x 1 *
          (MvPolynomial.eval (fun j => x (j + 1))
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalWronskianCompanion n)
                (decoBottomTotal (n + 1)) (i + 1)) +
            x 1 * MvPolynomial.eval (fun j => x (j + 1))
              (MvPolynomial.coordinateWronskian
                (decoBottomTotalCompanionCore n)
                (decoBottomTotal (n + 1)) (i + 1))) := by
  rw [coordinateWronskian_companionSlope_companion_succ_add_two_eq_split,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, MvPolynomial.eval_rename,
    MvPolynomial.eval_rename]
  rfl

/-- The coordinate-`1` successor Wronskian is independent of its own
coordinate, as exposed by the multiaffine affine-determinant formula. -/
theorem one_notMem_vars_coordinateWronskian_companionSlope_companion
    (n : Nat) :
    1 ∉ (MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionSlope n)
      (decoBottomTotalWronskianCompanion n) 1).vars :=
  MvPolynomial.IsMultiaffine.notMem_vars_coordinateWronskian
    (decoBottomTotalCompanionSlope_isMultiaffine n)
    (decoBottomTotalWronskianCompanion_isMultiaffine n) 1

/-- In coordinate `1`, the complete successor Wronskian is the determinant of
the explicit zero-sections and slopes of the two companion endpoints. -/
theorem coordinateWronskian_companionSlope_companion_one_eq_sections
    (n : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope n)
        (decoBottomTotalWronskianCompanion n) 1 =
      (MvPolynomial.specializeZero 1 (decoBottomTotal (n + 1)) +
          MvPolynomial.specializeZero 1
            (decoBottomTotalCompanionCore n)) *
        (MvPolynomial.pderiv 1 (decoBottomTotal (n + 1)) +
          MvPolynomial.rename (fun i : Nat => i + 1)
            (decoBottomTotal n)) -
      (MvPolynomial.pderiv 1 (decoBottomTotal (n + 1)) +
          MvPolynomial.pderiv 1 (decoBottomTotalCompanionCore n)) *
        MvPolynomial.specializeZero 1 (decoBottomTotal (n + 1)) := by
  rw [MvPolynomial.IsMultiaffine.coordinateWronskian_eq_specializeZero
      (decoBottomTotalCompanionSlope_isMultiaffine n)
      (decoBottomTotalWronskianCompanion_isMultiaffine n) 1,
    specializeZero_one_decoBottomTotalCompanionSlope,
    pderiv_one_decoBottomTotalWronskianCompanion,
    pderiv_one_decoBottomTotalCompanionSlope,
    specializeZero_one_decoBottomTotalWronskianCompanion]

/-- The core/latest-total Wronskian in coordinate `1` is the distinguished
row sum of Rayleigh differences supplied by the normal-core operator. -/
theorem coordinateWronskian_companionCore_total_one_eq_rayleighRow
    (n : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore n)
        (decoBottomTotal (n + 1)) 1 =
      decoBottomTotal (n + 1) *
          MvPolynomial.pderiv 1 (decoBottomTotal (n + 1)) +
        ∑ j : Fin (n + 1),
          (1 - MvPolynomial.X (decoLayerBottomEmbedding (n + 1) j)) *
            MvPolynomial.rayleighDifference (decoBottomTotal (n + 1)) 1
              (decoLayerBottomEmbedding (n + 1) j) := by
  let i : Fin (n + 1) := ⟨0, by lia⟩
  have h := coordinateWronskian_decoNormalBottomCore
    (n + 1) (decoBottomTotal (n + 1)) i
  simpa [decoBottomTotalCompanionCore, i] using h

/-- Equivalently, the coordinate-`1` successor Wronskian is the core/latest
Wronskian plus the shifted preceding total times the successor zero-section.
Every term is independent of coordinate `1`. -/
theorem coordinateWronskian_companionSlope_companion_one_eq_core_add_section
    (n : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope n)
        (decoBottomTotalWronskianCompanion n) 1 =
      MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore n)
          (decoBottomTotal (n + 1)) 1 +
        MvPolynomial.rename (fun i : Nat => i + 1)
            (decoBottomTotal n) *
          MvPolynomial.specializeZero 1
            (decoBottomTotalCompanionSlope n) := by
  rw [coordinateWronskian_companionSlope_companion_one_eq_sections,
    MvPolynomial.IsMultiaffine.coordinateWronskian_eq_specializeZero
      (decoBottomTotalCompanionCore_isMultiaffine n)
      (decoBottomTotal_isMultiaffine (n + 1)) 1,
    specializeZero_one_decoBottomTotalCompanionSlope]
  ring

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

/-- The compensation obligation only needs the finite ordinary support
interval `1, ..., n + 1`; every other coordinate gives `0 ≤ 0`. -/
theorem eval_companionWronskian_compensation_iff_Icc (n : Nat) :
    (∀ i x,
      -MvPolynomial.eval x
          (MvPolynomial.coordinateWronskian
            (decoBottomTotalCompanionCore n)
            (decoBottomTotalWronskianCompanion n) i) ≤
        MvPolynomial.eval x
          (decoBottomTotalCompanionWronskianCorrection n i)) ↔
      ∀ i ∈ Finset.Icc 1 (n + 1), ∀ x,
        -MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalCompanionCore n)
              (decoBottomTotalWronskianCompanion n) i) ≤
          MvPolynomial.eval x
            (decoBottomTotalCompanionWronskianCorrection n i) := by
  constructor
  · intro h i hi x
    exact h i x
  · intro h i x
    by_cases hi : i ∈ Finset.Icc 1 (n + 1)
    · exact h i hi x
    · have hiCore : i ∉ (decoBottomTotalCompanionCore n).vars := by
        intro hiVars
        exact hi (vars_decoBottomTotalCompanionCore_subset_Icc n hiVars)
      have hiCompanion :
          i ∉ (decoBottomTotalWronskianCompanion n).vars := by
        intro hiVars
        exact hi
          (vars_decoBottomTotalWronskianCompanion_subset_Icc n hiVars)
      rw [MvPolynomial.coordinateWronskian_eq_zero_of_notMem_vars
        hiCore hiCompanion,
        decoBottomTotalCompanionWronskianCorrection_eq_zero_of_notMem_Icc
          n i hi]
      simp

/-- The unbounded successor-slope/companion cross-sign condition is exactly
the finite family of named current companion crosses on occupied positive
coordinates. -/
theorem
    eval_coordinateWronskian_companionSlope_companion_nonneg_iff_companionCross
    (n : Nat) :
    (∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionSlope n)
        (decoBottomTotalWronskianCompanion n) i)) ↔
      ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
          n i) := by
  constructor
  · intro h i x
    exact h (i + 1 : Nat) x
  · intro h i x
    by_cases hi : i ∈ Finset.Icc 1 (n + 1)
    · have hiLower : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hiUpper : i - 1 < n + 1 := by
        have := (Finset.mem_Icc.mp hi).2
        lia
      let j : Fin (n + 1) := ⟨i - 1, hiUpper⟩
      have hj := h j x
      simpa only [
        decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross,
        j, Fin.val_mk, Nat.sub_add_cancel hiLower] using hj
    · have hiSlope : i ∉ (decoBottomTotalCompanionSlope n).vars := by
        intro hiVars
        exact hi (vars_decoBottomTotalCompanionSlope_subset_Icc n hiVars)
      have hiCompanion :
          i ∉ (decoBottomTotalWronskianCompanion n).vars := by
        intro hiVars
        exact hi
          (vars_decoBottomTotalWronskianCompanion_subset_Icc n hiVars)
      rw [MvPolynomial.coordinateWronskian_eq_zero_of_notMem_vars
        hiSlope hiCompanion]
      simp

/-- Nonnegativity of the named current companion crosses is exactly the
finite current-data compensation inequality. -/
theorem eval_companionCross_nonneg_iff_compensation_Icc (n : Nat) :
    (∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
        n i)) ↔
      ∀ i ∈ Finset.Icc 1 (n + 1), ∀ x,
        -MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalCompanionCore n)
              (decoBottomTotalWronskianCompanion n) i) ≤
          MvPolynomial.eval x
            (decoBottomTotalCompanionWronskianCorrection n i) := by
  rw [← eval_coordinateWronskian_companionSlope_companion_nonneg_iff_companionCross,
    eval_coordinateWronskian_companionSlope_companion_nonneg_iff_compensation,
    eval_companionWronskian_compensation_iff_Icc]

/-- Nonpositivity of the named current companion Plücker factors is the same
finite compensation condition, in the orientation used by the discriminant
factorization. -/
theorem eval_companionFactor_nonpos_iff_compensation_Icc (n : Nat) :
    (∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactor
        n i) ≤ 0) ↔
      ∀ i ∈ Finset.Icc 1 (n + 1), ∀ x,
        -MvPolynomial.eval x
            (MvPolynomial.coordinateWronskian
              (decoBottomTotalCompanionCore n)
              (decoBottomTotalWronskianCompanion n) i) ≤
          MvPolynomial.eval x
            (decoBottomTotalCompanionWronskianCorrection n i) := by
  rw [← eval_companionCross_nonneg_iff_compensation_Icc]
  constructor <;> intro h i x
  · exact
      (eval_decoBottomTotalCompanionSuccessorCoreCompanionFactor_nonpos_iff_cross
        n i x).mp (h i x)
  · exact
      (eval_decoBottomTotalCompanionSuccessorCoreCompanionFactor_nonpos_iff_cross
        n i x).mpr (h i x)

/-- Once the inherited core-cross sign and the row discriminant bound are
available, global companion-cross nonnegativity only needs to be checked on
the zero locus of the core cross. -/
theorem
    eval_companionCross_nonneg_iff_on_coreCross_zero_of_companionData
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n)
    (hdisc : ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0) :
    (∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
        n i)) ↔
      ∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              n i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              n i) := by
  constructor
  · intro h i x _
    exact h i x
  · intro h i x
    rcases
        eval_decoBottomTotalCompanionSuccessorCore_coreCross_eq_zero_or_companionCross_nonneg
          n i x
          (eval_decoBottomTotalCompanionSuccessorCoreCoreCross_nonneg_of_companionData
            n hstable hdata i x)
          (hdisc i x) with hzero | hnonneg
    · exact h i x hzero
    · exact hnonneg

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

/-- Under preceding-rank stability, the first remaining successor condition
is exactly nonnegativity of the finite named companion-cross family that also
occurs in the current Plücker factorization. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_companionCross
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hcompanion : MvPolynomial.IsRayleigh
      (decoBottomTotalWronskianCompanion n)) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
          n i)) ∧
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
    eval_coordinateWronskian_companionSlope_companion_nonneg_iff_companionCross]

/-- Equivalently, the first remaining successor condition is nonpositivity of
the finite named companion factors, in the orientation used by the current
Plücker factorization. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_companionFactor
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hcompanion : MvPolynomial.IsRayleigh
      (decoBottomTotalWronskianCompanion n)) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactor
          n i) ≤ 0) ∧
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
  rw [decoBottomTotalCompanionRayleighData_succ_iff_companionCross
    n hstable hcompanion]
  constructor <;> rintro ⟨h, hrest⟩
  · exact ⟨fun i x =>
      (eval_decoBottomTotalCompanionSuccessorCoreCompanionFactor_nonpos_iff_cross
        n i x).mpr (h i x), hrest⟩
  · exact ⟨fun i x =>
      (eval_decoBottomTotalCompanionSuccessorCoreCompanionFactor_nonpos_iff_cross
        n i x).mp (h i x), hrest⟩

/-- Under preceding-rank stability, the next companion-data criterion can use
the distinguished coordinate-`1` Wronskian and the finite successor core rows
in place of an unbounded family of next core/companion Wronskians. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_successorCoreRows
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
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        ∀ i : Fin (n + 1), ∀ x,
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRow n i)) ∧
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_of_stable_companion
    n hstable hcompanion,
    eval_coordinateWronskian_companionCore_companion_succ_nonneg_iff]

/-- The exact successor-data criterion can equivalently replace its finite
successor core rows by their leading, constant, and discriminant conditions. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_successorCoreQuadraticData
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
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        DecoBottomTotalCompanionSuccessorCoreQuadraticData n) ∧
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_successorCoreRows
    n hstable hcompanion,
    eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff]

/-- The exact successor-data criterion with the finite core rows expanded into
their current-data compensation and endpoint conditions. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_successorCoreEndpointData
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
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        DecoBottomTotalCompanionSuccessorCoreEndpointData n) ∧
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_successorCoreQuadraticData
    n hstable hcompanion,
    decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_endpointData]

/-- Given the current companion data, the companion-cross condition in the
exact successor criterion is needed only on the zero locus of the inherited
core cross.  Away from that locus, the successor-row discriminant bound
already forces its sign. -/
theorem
    decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              n i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              n i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        DecoBottomTotalCompanionSuccessorCoreEndpointData n) ∧
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_successorCoreEndpointData
    n hstable hdata.companion_isRayleigh]
  constructor
  · rintro ⟨hcross, hdisc, hrows, hnextDisc⟩
    have hcrossNamed :=
      (eval_coordinateWronskian_companionSlope_companion_nonneg_iff_companionCross
        n).mp hcross
    exact ⟨fun i x _ => hcrossNamed i x, hdisc, hrows, hnextDisc⟩
  · rintro ⟨hzero, hdisc, hrows, hnextDisc⟩
    have hcrossNamed :=
      (eval_companionCross_nonneg_iff_on_coreCross_zero_of_companionData
        n hstable hdata hrows.2.discriminant_nonpos).mpr hzero
    have hcross :=
      (eval_coordinateWronskian_companionSlope_companion_nonneg_iff_companionCross
        n).mpr hcrossNamed
    exact ⟨hcross, hdisc, hrows, hnextDisc⟩

/-- As an intermediate endpoint API, after removing the automatic constant
coefficients the zero-locus successor criterion retains the leading and
discriminant conditions for the finite successor rows. -/
theorem
    decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus_reduced
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              n i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              n i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        (∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)) ∧
        ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0) ∧
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus
      n hstable hdata,
    decoBottomTotalCompanionSuccessorCoreEndpointData_iff_quadratic_discriminant
      n hstable hdata]

/-- Stability supplies both endpoint coefficients in each finite successor
row, so the zero-locus successor criterion retains only the row discriminants
from that endpoint package. -/
theorem
    decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus_discriminant
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              n i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              n i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0) ∧
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion (n + 1))
          (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus
      n hstable hdata,
    decoBottomTotalCompanionSuccessorCoreEndpointData_iff_discriminant
      n hstable hdata]

/-- Under current stability and companion data, the exact successor
criterion has only finite distinct-coordinate affine-discriminant families.
Coordinates outside the displayed intervals and diagonal pairs contribute
zero automatically. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_finite
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              n i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              n i)) ∧
      (∀ i ∈ Finset.Icc 1 (n + 1),
        ∀ j ∈ Finset.Icc 1 (n + 1), i < j → ∀ x,
          MvPolynomial.eval x
            (MvPolynomial.affineRayleighDiscriminant
              (decoBottomTotalWronskianCompanion n)
              (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        DecoBottomTotalCompanionSuccessorCoreEndpointData n) ∧
      ∀ i ∈ Finset.Icc 1 (n + 2),
        ∀ j ∈ Finset.Icc 1 (n + 2), i < j → ∀ x,
          MvPolynomial.eval x
            (MvPolynomial.affineRayleighDiscriminant
              (decoBottomTotalWronskianCompanion (n + 1))
              (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus
    n hstable hdata]
  constructor
  · rintro ⟨hzero, hdisc, hrows, hnextDisc⟩
    exact ⟨hzero, fun i _ j _ _ x => hdisc i j x, hrows,
      fun i _ j _ _ x => hnextDisc i j x⟩
  · rintro ⟨hzero, hdisc, hrows, hnextDisc⟩
    refine ⟨hzero,
      eval_affineRayleighDiscriminant_companion_slope_nonpos_of_Icc
        n hdisc,
      hrows, ?_⟩
    apply eval_affineRayleighDiscriminant_companion_core_nonpos_of_Icc
      (n + 1)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hnextDisc

/-- The strongest finite successor criterion currently available: stability
discharges both endpoint coefficients, leaving only finite affine-discriminant
families and the companion cross condition on the inherited zero locus. -/
theorem decoBottomTotalCompanionRayleighData_succ_iff_finite_discriminant
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 1)))
    (hdata : DecoBottomTotalCompanionRayleighData n) :
    DecoBottomTotalCompanionRayleighData (n + 1) ↔
      (∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              n i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              n i)) ∧
      (∀ i ∈ Finset.Icc 1 (n + 1),
        ∀ j ∈ Finset.Icc 1 (n + 1), i < j → ∀ x,
          MvPolynomial.eval x
            (MvPolynomial.affineRayleighDiscriminant
              (decoBottomTotalWronskianCompanion n)
              (decoBottomTotalCompanionSlope n) i j) ≤ 0) ∧
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
        ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0) ∧
      ∀ i ∈ Finset.Icc 1 (n + 2),
        ∀ j ∈ Finset.Icc 1 (n + 2), i < j → ∀ x,
          MvPolynomial.eval x
            (MvPolynomial.affineRayleighDiscriminant
              (decoBottomTotalWronskianCompanion (n + 1))
              (decoBottomTotalCompanionCore (n + 1)) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus_discriminant
    n hstable hdata]
  constructor
  · rintro ⟨hzero, hdisc, hrows, hnextDisc⟩
    exact ⟨hzero, fun i _ j _ _ x => hdisc i j x, hrows,
      fun i _ j _ _ x => hnextDisc i j x⟩
  · rintro ⟨hzero, hdisc, hrows, hnextDisc⟩
    refine ⟨hzero,
      eval_affineRayleighDiscriminant_companion_slope_nonpos_of_Icc
        n hdisc,
      hrows, ?_⟩
    apply eval_affineRayleighDiscriminant_companion_core_nonpos_of_Icc
      (n + 1)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hnextDisc

/-- The exact lower two-rank companion data at rank one.  This gives the
first nontrivial checked instance of the successor criterion. -/
theorem decoBottomTotalCompanionRayleighData_one :
    DecoBottomTotalCompanionRayleighData 1 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_companionCrossZeroLocus
    0 decoLayerTotal_one_mvRealStable
      decoBottomTotalCompanionRayleighData_zero]
  refine ⟨?_, ?_,
    ⟨?_, decoBottomTotalCompanionSuccessorCoreEndpointData_zero⟩, ?_⟩
  · intro i x hzero
    simp
  · intro i j x
    rw [affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_zero]
    simp
  · intro x
    exact
      eval_coordinateWronskian_decoBottomTotalCompanionCore_companion_one_nonneg x
  · intro i j x
    exact
      eval_affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_core_one_nonpos
        i j x

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
