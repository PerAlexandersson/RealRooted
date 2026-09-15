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

/-- The unshifted successor core is multiaffine. -/
theorem decoBottomTotalCompanionExtensionCore_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine
      (decoBottomTotalCompanionExtensionCore n) := by
  unfold decoBottomTotalCompanionExtensionCore
  exact (decoBottomTotalCompanionTotalExtension_isMultiaffine n).affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)

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
