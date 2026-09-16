import RealRooted.Applications.OEIS.A144438.LayerTotalCompanionExtension

/-!
# Successor recurrence for the Deco companion core

This file transports the successor normal core into the same unshifted
coordinate system as the companion extensions.  It thereby reduces their
coordinate Wronskians together under one injective rename.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The unshifted affine Euler core whose positive-coordinate rename is the
normal core attached to the next bottom total. -/
def decoBottomTotalCompanionExtensionCore (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.affineEulerCore (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
    (n + 3 : Real) (decoBottomTotalCompanionTotalExtension n)

/-- The unshifted recurrence form of the next companion slope. -/
def decoBottomTotalCompanionSuccessorSlopeRecurrence (n : Nat) :
    MvPolynomial Nat Real :=
  decoBottomTotalCompanionTotalExtension n +
    decoBottomTotalCompanionExtensionCore n

/-- The affine Euler Rayleigh row of the companion total extension at the
positive coordinate indexed by `i`. -/
def decoBottomTotalCompanionExtensionRayleighRow
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.affineEulerRayleighRow
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
      (decoBottomTotalCompanionTotalExtension n) i.succ

/-- The full lower coefficient obtained after adjoining the successor's fresh
copy of the latest total to the affine Euler Rayleigh row. -/
def decoBottomTotalCompanionSuccessorCoreRow
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  decoBottomTotalCompanionExtensionRayleighRow n i +
    MvPolynomial.X 0 *
      MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionExtensionCore n)
        (decoBottomTotal (n + 1)) (i + 1 : Nat)

/-- The unshifted successor core is multiaffine. -/
theorem decoBottomTotalCompanionExtensionCore_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine
      (decoBottomTotalCompanionExtensionCore n) := by
  unfold decoBottomTotalCompanionExtensionCore
  exact (decoBottomTotalCompanionTotalExtension_isMultiaffine n).affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)

/-- The successor companion extension adds the fresh-coordinate copy of the
latest total to the extension producing that total. -/
theorem decoBottomTotalCompanionSuccessorExtension_eq_totalExtension_add
    (n : Nat) :
    decoBottomTotalCompanionSuccessorExtension n =
      decoBottomTotalCompanionTotalExtension n +
        MvPolynomial.X 0 * decoBottomTotal (n + 1) := by
  unfold decoBottomTotalCompanionSuccessorExtension
    decoBottomTotalCompanionTotalExtension
    decoBottomTotalCompanionSlope
  ring

/-- Away from the fresh coordinate, the core/successor Wronskian splits into
the core/total-extension Wronskian and a fresh-coordinate multiple of the
core/latest-total Wronskian. -/
theorem coordinateWronskian_companionExtensionCore_successorExtension_add_one
    (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionExtensionCore n)
        (decoBottomTotalCompanionSuccessorExtension n) (i + 1) =
      MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCore n)
          (decoBottomTotalCompanionTotalExtension n) (i + 1) +
        MvPolynomial.X 0 *
          MvPolynomial.coordinateWronskian
            (decoBottomTotalCompanionExtensionCore n)
            (decoBottomTotal (n + 1)) (i + 1) := by
  have hi : i + 1 ≠ 0 := by lia
  rw [decoBottomTotalCompanionSuccessorExtension_eq_totalExtension_add,
    MvPolynomial.coordinateWronskian_add_right,
    MvPolynomial.coordinateWronskian_X_mul_right, if_neg hi, add_zero]

/-- The core/total-extension Wronskian in each occupied positive coordinate
is the corresponding affine Euler Rayleigh row. -/
theorem coordinateWronskian_companionExtensionCore_totalExtension
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionExtensionCore n)
        (decoBottomTotalCompanionTotalExtension n) (i + 1 : Nat) =
      decoBottomTotalCompanionExtensionRayleighRow n i := by
  unfold decoBottomTotalCompanionExtensionCore
    decoBottomTotalCompanionExtensionRayleighRow
  simpa using MvPolynomial.coordinateWronskian_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 3 : Real) (decoBottomTotalCompanionTotalExtension n) i.succ

/-- A companion-extension affine-Euler row is independent of its own positive
coordinate. -/
theorem add_one_notMem_vars_decoBottomTotalCompanionExtensionRayleighRow
    (n : Nat) (i : Fin (n + 1)) :
    (i + 1 : Nat) ∉
      (decoBottomTotalCompanionExtensionRayleighRow n i).vars := by
  unfold decoBottomTotalCompanionExtensionRayleighRow
  simpa using MvPolynomial.IsMultiaffine.notMem_vars_affineEulerRayleighRow
    (decoBottomTotalCompanionTotalExtension_isMultiaffine n)
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
    Fin.valEmbedding.injective i.succ

/-- The bounded core/successor Wronskian is an affine Euler Rayleigh row plus
one fresh-coordinate multiple of a lower core/total Wronskian. -/
theorem coordinateWronskian_companionExtensionCore_successorExtension
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionExtensionCore n)
        (decoBottomTotalCompanionSuccessorExtension n) (i + 1 : Nat) =
      decoBottomTotalCompanionSuccessorCoreRow n i := by
  unfold decoBottomTotalCompanionSuccessorCoreRow
  rw [coordinateWronskian_companionExtensionCore_successorExtension_add_one,
    coordinateWronskian_companionExtensionCore_totalExtension]

/-- Each successor core row is independent of the positive coordinate in
which its defining Wronskian is taken. -/
theorem add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRow
    (n : Nat) (i : Fin (n + 1)) :
    (i + 1 : Nat) ∉ (decoBottomTotalCompanionSuccessorCoreRow n i).vars := by
  rw [← coordinateWronskian_companionExtensionCore_successorExtension]
  exact MvPolynomial.IsMultiaffine.notMem_vars_coordinateWronskian
    (decoBottomTotalCompanionExtensionCore_isMultiaffine n)
    (decoBottomTotalCompanionSuccessorExtension_isMultiaffine n)
    (i + 1 : Nat)

/-- The next companion core is the positive-coordinate rename of its
unshifted affine Euler core. -/
theorem decoBottomTotalCompanionCore_succ_eq_rename_extensionCore (n : Nat) :
    decoBottomTotalCompanionCore (n + 1) =
      MvPolynomial.rename (fun i : Nat => i + 1)
        (decoBottomTotalCompanionExtensionCore n) := by
  change decoNormalBottomCore (n + 2) (decoBottomTotal (n + 2)) = _
  rw [decoBottomTotal_add_two_eq_rename_companionTotalExtension,
    decoNormalBottomCore_eq_affineEulerCore]
  unfold decoBottomTotalCompanionExtensionCore
  rw [MvPolynomial.rename_affineEulerCore
    (g := fun i : Nat => i + 1) (hg := by intro i j hij; lia)]
  have hemb :
      (decoLayerBottomEmbedding (n + 2) : Fin (n + 2) → Nat) =
        (fun i : Nat => i + 1) ∘
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) := by
    funext i
    rfl
  rw [hemb]
  congr 1
  push_cast
  ring

/-- The next companion slope is the positive-coordinate rename of its
unshifted recurrence form. -/
theorem decoBottomTotalCompanionSlope_succ_eq_rename (n : Nat) :
    decoBottomTotalCompanionSlope (n + 1) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorSlopeRecurrence n) := by
  unfold decoBottomTotalCompanionSlope
    decoBottomTotalCompanionSuccessorSlopeRecurrence
  rw [decoBottomTotal_add_two_eq_rename_companionTotalExtension,
    decoBottomTotalCompanionCore_succ_eq_rename_extensionCore, map_add]

/-- Stability of the next homogeneous layer orients its unshifted affine
Euler core against the companion total extension in every coordinate. -/
theorem
    eval_coordinateWronskian_companionExtensionCore_totalExtension_nonneg_of_stable
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 2))) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionExtensionCore n)
        (decoBottomTotalCompanionTotalExtension n) i) := by
  have hrenamed :=
    eval_coordinateWronskian_decoNormalBottomCore_total_nonneg
      (n + 2) hstable
  intro i
  have hshifted : ∀ x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCore n)
          (decoBottomTotalCompanionTotalExtension n) i)) := by
    intro x
    have h := hrenamed (i + 1) x
    change 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore (n + 1))
        (decoBottomTotal (n + 2)) (i + 1)) at h
    rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
      decoBottomTotal_add_two_eq_rename_companionTotalExtension,
      MvPolynomial.coordinateWronskian_rename (fun j : Nat => j + 1)
        (by intro j k hjk; lia)] at h
    exact h
  exact (MvPolynomial.forall_eval_rename_iff
    (fun j : Nat => j + 1) (by intro j k hjk; lia)
    (MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionExtensionCore n)
      (decoBottomTotalCompanionTotalExtension n) i)
    (fun r => 0 ≤ r)).mp hshifted

/-- Stability of the next homogeneous layer makes every affine-Euler row of
its unshifted extension core nonnegative. -/
theorem
    eval_affineEulerRayleighRow_companionExtensionCore_nonneg_of_stable
    (n : Nat) (hstable : MvRealStable (decoLayerTotal (n + 2))) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.affineEulerRayleighRow
        (Fin.valEmbedding : Fin (n + 2) → Nat)
        (decoBottomTotalCompanionExtensionCore n) i) := by
  have hnormal :=
    eval_coordinateWronskian_decoNormalBottomCore_iterate_nonneg
      (n + 2) (by lia) hstable
  intro i
  have houter :
      MvPolynomial.affineEulerCore (decoLayerBottomEmbedding (n + 2))
          ((n + 2 : Nat) : Real)
          (decoBottomTotalCompanionCore (n + 1)) =
        MvPolynomial.rename (fun j : Nat => j + 1)
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) → Nat) ((n + 2 : Nat) : Real)
            (decoBottomTotalCompanionExtensionCore n)) := by
    rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
      MvPolynomial.rename_affineEulerCore
        (fun j : Nat => j + 1) (by intro j k hjk; lia)]
    rfl
  have hshifted : ∀ x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) → Nat) ((n + 2 : Nat) : Real)
            (decoBottomTotalCompanionExtensionCore n))
          (decoBottomTotalCompanionExtensionCore n) (i : Nat))) := by
    intro x
    have h := hnormal (i + 1 : Nat) x
    change 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore (decoLayerBottomEmbedding (n + 2))
          ((n + 2 : Nat) : Real)
          (decoBottomTotalCompanionCore (n + 1)))
        (decoBottomTotalCompanionCore (n + 1)) (i + 1 : Nat)) at h
    rw [houter, decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
      MvPolynomial.coordinateWronskian_rename
        (fun j : Nat => j + 1) (by intro j k hjk; lia)] at h
    exact h
  have hunshifted := (MvPolynomial.forall_eval_rename_iff
    (fun j : Nat => j + 1) (by intro j k hjk; lia)
    (MvPolynomial.coordinateWronskian
      (MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) → Nat) ((n + 2 : Nat) : Real)
        (decoBottomTotalCompanionExtensionCore n))
      (decoBottomTotalCompanionExtensionCore n) (i : Nat))
    (fun r => 0 ≤ r)).mp hshifted
  rw [← MvPolynomial.coordinateWronskian_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) → Nat) Fin.valEmbedding.injective
    ((n + 2 : Nat) : Real) (decoBottomTotalCompanionExtensionCore n) i]
  exact hunshifted

/-- Value-one specialization commutes with the affine Euler core defining the
unshifted next companion core. -/
theorem specializeAt_one_decoBottomTotalCompanionExtensionCore
    (n : Nat) (i : Fin (n + 2)) :
    MvPolynomial.specializeAt (i : Nat) 1
        (decoBottomTotalCompanionExtensionCore n) =
      MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
        (MvPolynomial.specializeAt (i : Nat) 1
          (decoBottomTotalCompanionTotalExtension n)) := by
  unfold decoBottomTotalCompanionExtensionCore
  exact MvPolynomial.specializeAt_one_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 3 : Real) (decoBottomTotalCompanionTotalExtension n) i

/-- Differentiating the unshifted next companion core lowers its affine Euler
coefficient by one. -/
theorem pderiv_decoBottomTotalCompanionExtensionCore
    (n : Nat) (i : Fin (n + 2)) :
    MvPolynomial.pderiv (i : Nat)
        (decoBottomTotalCompanionExtensionCore n) =
      MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
        (MvPolynomial.pderiv (i : Nat)
          (decoBottomTotalCompanionTotalExtension n)) := by
  unfold decoBottomTotalCompanionExtensionCore
  have h := MvPolynomial.pderiv_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 3 : Real) (decoBottomTotalCompanionTotalExtension n) i
  have hc : (n + 3 : Real) - 1 = (n + 2 : Real) := by
    ring
  rw [hc] at h
  simpa only [Fin.valEmbedding_apply] using h

/-- Every noninitial value-one section of the next companion core is the
positive-coordinate shift of the corresponding unshifted core section. -/
theorem specializeAt_one_decoBottomTotalCompanionCore_succ_add_two
    (n i : Nat) :
    MvPolynomial.specializeAt (i + 2) 1
        (decoBottomTotalCompanionCore (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.specializeAt (i + 1) 1
          (decoBottomTotalCompanionExtensionCore n)) := by
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore]
  simpa only [Nat.add_assoc] using
    MvPolynomial.specializeAt_rename (fun j : Nat => j + 1)
      (by intro j k h; lia) (i + 1) 1
        (decoBottomTotalCompanionExtensionCore n)

/-- Every noninitial derivative of the next companion core is the
positive-coordinate shift of the corresponding unshifted core derivative. -/
theorem pderiv_decoBottomTotalCompanionCore_succ_add_two
    (n i : Nat) :
    MvPolynomial.pderiv (i + 2)
        (decoBottomTotalCompanionCore (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.pderiv (i + 1)
          (decoBottomTotalCompanionExtensionCore n)) := by
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore]
  simpa only [Nat.add_assoc] using
    MvPolynomial.pderiv_rename (R := Real)
      (f := fun j : Nat => j + 1) (by intro j k h; lia) (i + 1)
        (decoBottomTotalCompanionExtensionCore n)

/-- At each occupied noninitial coordinate, a value-one section of the next
companion core is the shift of an affine Euler core of the corresponding
total-extension section. -/
theorem specializeAt_one_decoBottomTotalCompanionCore_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.specializeAt (i + 2 : Nat) 1
        (decoBottomTotalCompanionCore (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
          (MvPolynomial.specializeAt (i + 1 : Nat) 1
            (decoBottomTotalCompanionTotalExtension n))) := by
  rw [specializeAt_one_decoBottomTotalCompanionCore_succ_add_two]
  congr 1
  simpa only [Fin.val_succ] using
    specializeAt_one_decoBottomTotalCompanionExtensionCore n i.succ

/-- At each occupied noninitial coordinate, a derivative of the next
companion core is the shift of a lowered-coefficient affine Euler core of the
corresponding total-extension derivative. -/
theorem pderiv_decoBottomTotalCompanionCore_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.pderiv (i + 2 : Nat)
        (decoBottomTotalCompanionCore (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
          (MvPolynomial.pderiv (i + 1 : Nat)
            (decoBottomTotalCompanionTotalExtension n))) := by
  rw [pderiv_decoBottomTotalCompanionCore_succ_add_two]
  congr 1
  simpa only [Fin.val_succ] using
    pderiv_decoBottomTotalCompanionExtensionCore n i.succ

/-- At each occupied noninitial coordinate, the endpoint factor of the next
companion core is the shift of the product of the corresponding affine Euler
section and derivative cores. -/
theorem specializeAt_one_mul_pderiv_decoBottomTotalCompanionCore_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.specializeAt (i + 2 : Nat) 1
          (decoBottomTotalCompanionCore (n + 1)) *
        MvPolynomial.pderiv (i + 2 : Nat)
          (decoBottomTotalCompanionCore (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
            (MvPolynomial.specializeAt (i + 1 : Nat) 1
              (decoBottomTotalCompanionTotalExtension n)) *
          MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
            (MvPolynomial.pderiv (i + 1 : Nat)
              (decoBottomTotalCompanionTotalExtension n))) := by
  rw [specializeAt_one_decoBottomTotalCompanionCore_succ_fin,
    pderiv_decoBottomTotalCompanionCore_succ_fin, map_mul]

/-- Every noninitial affine-Euler remainder of the next companion is the
shift of the corresponding remainder of its unshifted successor extension. -/
theorem affineEulerRayleighRemainder_companion_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.affineEulerRayleighRemainder
        (Fin.valEmbedding : Fin (n + 3) → Nat)
        (decoBottomTotalWronskianCompanion (n + 1)) i.succ.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerRayleighRemainder
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalCompanionSuccessorExtension n) i.succ) := by
  rw [decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  exact MvPolynomial.affineEulerRayleighRemainder_rename_succ
    (decoBottomTotalCompanionSuccessorExtension n) (n + 2) i.succ

/-- Every noninitial affine-Euler row of the next companion is the shift of
the corresponding row of its unshifted successor extension. -/
theorem affineEulerRayleighRow_companion_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.affineEulerRayleighRow
        (Fin.valEmbedding : Fin (n + 3) → Nat)
        (decoBottomTotalWronskianCompanion (n + 1)) i.succ.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalCompanionSuccessorExtension n) i.succ) := by
  rw [decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  exact MvPolynomial.affineEulerRayleighRow_rename_succ
    (decoBottomTotalCompanionSuccessorExtension n) (n + 2) i.succ

/-- Every noninitial affine-Euler remainder of the next companion core is the
shift of the corresponding remainder of its unshifted affine Euler core. -/
theorem affineEulerRayleighRemainder_companionCore_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.affineEulerRayleighRemainder
        (Fin.valEmbedding : Fin (n + 3) → Nat)
        (decoBottomTotalCompanionCore (n + 1)) i.succ.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerRayleighRemainder
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalCompanionExtensionCore n) i.succ) := by
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore]
  exact MvPolynomial.affineEulerRayleighRemainder_rename_succ
    (decoBottomTotalCompanionExtensionCore n) (n + 2) i.succ

/-- Every noninitial affine-Euler row of the next companion core is the shift
of the corresponding row of its unshifted affine Euler core. -/
theorem affineEulerRayleighRow_companionCore_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.affineEulerRayleighRow
        (Fin.valEmbedding : Fin (n + 3) → Nat)
        (decoBottomTotalCompanionCore (n + 1)) i.succ.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalCompanionExtensionCore n) i.succ) := by
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore]
  exact MvPolynomial.affineEulerRayleighRow_rename_succ
    (decoBottomTotalCompanionExtensionCore n) (n + 2) i.succ

/-- The mixed affine-Euler-core/latest-total Wronskian at a noninitial next
coordinate is the shift of its unshifted total-extension counterpart. -/
theorem coordinateWronskian_affineEulerCore_companionCore_succ_total_add_two
    (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 3) → Nat) (n + 3 : Real)
          (decoBottomTotalCompanionCore (n + 1)))
        (decoBottomTotal (n + 2)) (i + 2) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 3 : Real)
            (decoBottomTotalCompanionExtensionCore n))
          (decoBottomTotalCompanionTotalExtension n) (i + 1)) := by
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
    MvPolynomial.affineEulerCore_rename_succ,
    decoBottomTotal_add_two_eq_rename_companionTotalExtension]
  simpa only [Nat.add_assoc] using
    MvPolynomial.coordinateWronskian_rename (fun j : Nat => j + 1)
      (by intro j k h; lia)
      (MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 3 : Real)
        (decoBottomTotalCompanionExtensionCore n))
      (decoBottomTotalCompanionTotalExtension n) (i + 1)

/-- Every coordinate-`i + 2` Wronskian of the next core and companion is the
shift of the corresponding unshifted successor-extension Wronskian. -/
theorem coordinateWronskian_companionCore_companion_succ_add_two
    (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore (n + 1))
        (decoBottomTotalWronskianCompanion (n + 1)) (i + 2) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCore n)
          (decoBottomTotalCompanionSuccessorExtension n) (i + 1)) := by
  rw [decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
    decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  simpa only [Nat.add_assoc] using
    MvPolynomial.coordinateWronskian_rename (fun j : Nat => j + 1)
      (by intro j k hjk; lia)
      (decoBottomTotalCompanionExtensionCore n)
      (decoBottomTotalCompanionSuccessorExtension n) (i + 1)

/-- In every occupied coordinate above `1`, the next companion-data
Wronskian is the positive-coordinate rename of the named successor core row. -/
theorem coordinateWronskian_companionCore_companion_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore (n + 1))
        (decoBottomTotalWronskianCompanion (n + 1)) (i + 2 : Nat) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreRow n i) := by
  rw [coordinateWronskian_companionCore_companion_succ_add_two,
    coordinateWronskian_companionExtensionCore_successorExtension]

/-- Evaluation of the next positive-coordinate companion-data Wronskian is
evaluation of the corresponding successor core row under the shifted
assignment. -/
theorem eval_coordinateWronskian_companionCore_companion_succ_fin
    (n : Nat) (i : Fin (n + 1)) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) (i + 2 : Nat)) =
      MvPolynomial.eval (fun j => x (j + 1))
        (decoBottomTotalCompanionSuccessorCoreRow n i) := by
  rw [coordinateWronskian_companionCore_companion_succ_fin,
    MvPolynomial.eval_rename]
  rfl

/-- Nonnegativity of every next companion-data Wronskian is equivalent to
the distinguished coordinate-`1` condition and nonnegativity of the finite
family of successor core rows. -/
theorem eval_coordinateWronskian_companionCore_companion_succ_nonneg_iff
    (n : Nat) :
    (∀ k x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore (n + 1))
        (decoBottomTotalWronskianCompanion (n + 1)) k)) ↔
      (∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) 1)) ∧
      ∀ i : Fin (n + 1), ∀ x,
        0 ≤ MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRow n i) := by
  have hCore : (decoBottomTotalCompanionCore (n + 1)).vars ⊆
      Finset.Icc 1 (n + 2) := by
    intro k hk
    have hbounds :=
      vars_decoBottomTotalCompanionCore_subset_Icc (n + 1) hk
    rw [Finset.mem_Icc] at hbounds ⊢
    constructor <;> lia
  have hCompanion : (decoBottomTotalWronskianCompanion (n + 1)).vars ⊆
      Finset.Icc 1 (n + 2) := by
    intro k hk
    have hbounds :=
      vars_decoBottomTotalWronskianCompanion_subset_Icc (n + 1) hk
    rw [Finset.mem_Icc] at hbounds ⊢
    constructor <;> lia
  rw [MvPolynomial.eval_coordinateWronskian_nonneg_iff_finset
    _ _ (Finset.Icc 1 (n + 2)) hCore hCompanion]
  constructor
  · intro h
    refine ⟨h 1 (Finset.mem_Icc.mpr ⟨le_rfl, by lia⟩), ?_⟩
    intro i x
    let y : Nat → Real
      | 0 => 0
      | k + 1 => x k
    have hi : (i + 2 : Nat) ∈ Finset.Icc 1 (n + 2) := by
      rw [Finset.mem_Icc]
      constructor
      · lia
      · exact Nat.add_le_add_right i.isLt 1
    have hrow := h (i + 2 : Nat) hi y
    rw [eval_coordinateWronskian_companionCore_companion_succ_fin] at hrow
    simpa [y] using hrow
  · rintro ⟨hone, hrows⟩ k hk x
    rw [Finset.mem_Icc] at hk
    by_cases hk1 : k = 1
    · subst k
      exact hone x
    · have hk2 : 2 ≤ k := by lia
      let i : Fin (n + 1) := ⟨k - 2, by lia⟩
      have hik : (i + 2 : Nat) = k := by
        simp only [i]
        lia
      rw [← hik,
        eval_coordinateWronskian_companionCore_companion_succ_fin]
      exact hrows i (fun j => x (j + 1))

/-- Evaluation of the shifted successor core/companion Wronskian uses the
shifted assignment and the unshifted extensions. -/
theorem eval_coordinateWronskian_companionCore_companion_succ_add_two
    (n i : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore (n + 1))
          (decoBottomTotalWronskianCompanion (n + 1)) (i + 2)) =
      MvPolynomial.eval (fun j => x (j + 1))
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCore n)
          (decoBottomTotalCompanionSuccessorExtension n) (i + 1)) := by
  rw [coordinateWronskian_companionCore_companion_succ_add_two,
    MvPolynomial.eval_rename]
  rfl

end

end RealRooted.Applications.OEIS
