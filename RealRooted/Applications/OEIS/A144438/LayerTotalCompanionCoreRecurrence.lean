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

/-- The affine Euler Rayleigh row of the companion total extension at the
positive coordinate indexed by `i`. -/
def decoBottomTotalCompanionExtensionRayleighRow
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  decoBottomTotalCompanionTotalExtension n *
      MvPolynomial.pderiv (i + 1 : Nat)
        (decoBottomTotalCompanionTotalExtension n) +
    ∑ j : Fin (n + 2),
      (1 - MvPolynomial.X (j : Nat)) *
        MvPolynomial.rayleighDifference
          (decoBottomTotalCompanionTotalExtension n)
          (i + 1 : Nat) (j : Nat)

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
  constructor
  · intro h
    refine ⟨h 1, ?_⟩
    intro i x
    let y : Nat → Real
      | 0 => 0
      | k + 1 => x k
    have hrow := h (i + 2 : Nat) y
    rw [eval_coordinateWronskian_companionCore_companion_succ_fin] at hrow
    simpa [y] using hrow
  · rintro ⟨hone, hrows⟩ k x
    by_cases hk : k ∈ Finset.Icc 1 (n + 2)
    · rw [Finset.mem_Icc] at hk
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
    · have hkCore :
          k ∉ (decoBottomTotalCompanionCore (n + 1)).vars := by
        intro hkVars
        apply hk
        have hbounds :=
          vars_decoBottomTotalCompanionCore_subset_Icc (n + 1) hkVars
        rw [Finset.mem_Icc] at hbounds ⊢
        constructor <;> lia
      have hkCompanion :
          k ∉ (decoBottomTotalWronskianCompanion (n + 1)).vars := by
        intro hkVars
        apply hk
        have hbounds :=
          vars_decoBottomTotalWronskianCompanion_subset_Icc (n + 1) hkVars
        rw [Finset.mem_Icc] at hbounds ⊢
        constructor <;> lia
      rw [MvPolynomial.coordinateWronskian_eq_zero_of_notMem_vars
        hkCore hkCompanion, map_zero]

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
