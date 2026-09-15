import RealRooted.Applications.OEIS.A144438.LayerTotalCompanionCoreRecurrence
import RealRooted.Mathlib.Algebra.QuadraticDiscriminant
import RealRooted.Multiaffine.AffineLineRestriction

/-!
# Fresh-coordinate quadratic for the Deco companion core rows

This file decomposes the finite successor core rows along their remaining
fresh coordinate.  The three resulting endpoint Wronskian coefficients and
their discriminant are exact algebraic data; no sign claim is made here.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The zero-section of the companion extension core in its fresh coordinate. -/
def decoBottomTotalCompanionExtensionCoreZero (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.specializeZero 0
    (decoBottomTotalCompanionExtensionCore n)

/-- The slope of the companion extension core in its fresh coordinate. -/
def decoBottomTotalCompanionExtensionCoreSlope (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.pderiv 0 (decoBottomTotalCompanionExtensionCore n)

/-- The unshifted recurrence form of the next companion-extension core's
fresh-coordinate zero-section. -/
def decoBottomTotalCompanionSuccessorCoreZeroRecurrence (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.affineEulerCore
      (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 4 : Real)
      (decoBottomTotalCompanionSuccessorExtension n) +
    decoBottomTotalCompanionExtensionCore n

/-- The unshifted recurrence form of the next companion-extension core's
fresh-coordinate slope. -/
def decoBottomTotalCompanionSuccessorCoreSlopeRecurrence (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 3 : Real)
    (decoBottomTotalCompanionExtensionCore n)

/-- The fresh-coordinate derivative of the total extension is its companion
core. -/
theorem pderiv_zero_decoBottomTotalCompanionTotalExtension (n : Nat) :
    MvPolynomial.pderiv 0
        (decoBottomTotalCompanionTotalExtension n) =
      decoBottomTotalCompanionCore n := by
  unfold decoBottomTotalCompanionTotalExtension
  rw [map_add, MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n),
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (zero_notMem_vars_decoBottomTotalCompanionCore n)]
  ring

/-- The fresh-coordinate slope of the extension core is the affine Euler core
of the preceding companion core, with coefficient lowered by one. -/
theorem decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore
    (n : Nat) :
    decoBottomTotalCompanionExtensionCoreSlope n =
      MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
          (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionExtensionCoreSlope
    decoBottomTotalCompanionExtensionCore
  let i : Fin (n + 2) := ⟨0, by lia⟩
  have hderiv : MvPolynomial.pderiv 0
        (MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
            (decoBottomTotalCompanionTotalExtension n)) =
      MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) ((n + 3 : Real) - 1)
          (MvPolynomial.pderiv 0
            (decoBottomTotalCompanionTotalExtension n)) := by
    simpa [i] using MvPolynomial.pderiv_affineEulerCore
      (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
        (n + 3 : Real) (decoBottomTotalCompanionTotalExtension n) i
  rw [hderiv, pderiv_zero_decoBottomTotalCompanionTotalExtension]
  congr 2
  ring

/-- The extension core splits into the affine Euler core of the companion,
the preceding companion core, and the fresh-coordinate slope. -/
theorem decoBottomTotalCompanionExtensionCore_eq_base_add_X_mul_slope
    (n : Nat) :
    decoBottomTotalCompanionExtensionCore n =
      MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
          (decoBottomTotalWronskianCompanion n) +
        decoBottomTotalCompanionCore n +
        MvPolynomial.X 0 *
          decoBottomTotalCompanionExtensionCoreSlope n := by
  rw [decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore]
  unfold decoBottomTotalCompanionExtensionCore
    decoBottomTotalCompanionTotalExtension
  let i : Fin (n + 2) := ⟨0, by lia⟩
  have h := MvPolynomial.affineEulerCore_add_X_mul
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 3 : Real) (decoBottomTotalWronskianCompanion n)
        (decoBottomTotalCompanionCore n) i
  have hc : (n + 3 : Real) - 1 = (n + 2 : Real) := by ring
  rw [hc] at h
  simpa [i] using h

/-- The constant coefficient of a successor core row in the fresh
coordinate. -/
def decoBottomTotalCompanionSuccessorCoreRowConstant
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionExtensionCoreZero n)
    (decoBottomTotalWronskianCompanion n) (i + 1 : Nat)

/-- The linear coefficient of a successor core row in the fresh coordinate. -/
def decoBottomTotalCompanionSuccessorCoreRowLinear
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionExtensionCoreZero n)
      (decoBottomTotalCompanionSlope n) (i + 1 : Nat) +
    MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionExtensionCoreSlope n)
      (decoBottomTotalWronskianCompanion n) (i + 1 : Nat)

/-- The quadratic coefficient of a successor core row in the fresh
coordinate. -/
def decoBottomTotalCompanionSuccessorCoreRowQuadratic
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionExtensionCoreSlope n)
    (decoBottomTotalCompanionSlope n) (i + 1 : Nat)

/-- The polynomial discriminant of the fresh-coordinate successor core row. -/
def decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  decoBottomTotalCompanionSuccessorCoreRowLinear n i ^ 2 -
    MvPolynomial.C 4 *
      decoBottomTotalCompanionSuccessorCoreRowQuadratic n i *
        decoBottomTotalCompanionSuccessorCoreRowConstant n i

/-- The unshifted recurrence form of a next constant row coefficient. -/
def decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
    (decoBottomTotalCompanionSuccessorExtension n) (i + 1 : Nat)

/-- The unshifted recurrence form of a next linear row coefficient. -/
def decoBottomTotalCompanionSuccessorCoreRowLinearRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
      (decoBottomTotalCompanionSuccessorSlopeRecurrence n) (i + 1 : Nat) +
    MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
      (decoBottomTotalCompanionSuccessorExtension n) (i + 1 : Nat)

/-- The unshifted recurrence form of a next quadratic row coefficient. -/
def decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
    (decoBottomTotalCompanionSuccessorSlopeRecurrence n) (i + 1 : Nat)

/-- The unshifted recurrence form of a next row discriminant. -/
def decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  decoBottomTotalCompanionSuccessorCoreRowLinearRecurrence n i ^ 2 -
    MvPolynomial.C 4 *
      decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i *
        decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i

/-- The skew term in the Plücker factorization of the unshifted next-row
discriminant. -/
def decoBottomTotalCompanionSuccessorCoreRowDiscriminantSkewRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
      (decoBottomTotalCompanionSuccessorSlopeRecurrence n) (i + 1 : Nat) -
    MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
      (decoBottomTotalCompanionSuccessorExtension n) (i + 1 : Nat)

/-- The core-pair factor in the Plücker factorization of the unshifted
next-row discriminant. -/
def decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreFactorRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
    (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n) (i + 1 : Nat)

/-- The companion-pair factor in the Plücker factorization of the unshifted
next-row discriminant. -/
def
    decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactorRecurrence
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionSuccessorExtension n)
    (decoBottomTotalCompanionSuccessorSlopeRecurrence n) (i + 1 : Nat)

/-- The successor-core row discriminant has the generic Plücker
factorization for the two affine endpoint pairs. -/
theorem decoBottomTotalCompanionSuccessorCoreRowDiscriminant_eq_plucker
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i =
      (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCoreZero n)
          (decoBottomTotalCompanionSlope n) (i + 1 : Nat) -
        MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCoreSlope n)
          (decoBottomTotalWronskianCompanion n) (i + 1 : Nat)) ^ 2 -
      4 * MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionExtensionCoreZero n)
          (decoBottomTotalCompanionExtensionCoreSlope n) (i + 1 : Nat) *
        MvPolynomial.coordinateWronskian
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) (i + 1 : Nat) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowDiscriminant,
    decoBottomTotalCompanionSuccessorCoreRowLinear,
    decoBottomTotalCompanionSuccessorCoreRowQuadratic,
    decoBottomTotalCompanionSuccessorCoreRowConstant,
    show (MvPolynomial.C (4 : Real) : MvPolynomial Nat Real) = 4 by
      exact map_ofNat MvPolynomial.C 4]
  exact MvPolynomial.coordinateWronskian_quadratic_discriminant
    (decoBottomTotalCompanionExtensionCoreZero n)
    (decoBottomTotalCompanionExtensionCoreSlope n)
    (decoBottomTotalWronskianCompanion n)
    (decoBottomTotalCompanionSlope n) (i + 1 : Nat)

/-- The unshifted next-row discriminant has the same generic Plücker
factorization. -/
theorem
    decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_eq_plucker
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i =
      (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
          (decoBottomTotalCompanionSuccessorSlopeRecurrence n)
          (i + 1 : Nat) -
        MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
          (decoBottomTotalCompanionSuccessorExtension n)
          (i + 1 : Nat)) ^ 2 -
      4 * MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
          (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
          (i + 1 : Nat) *
        MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSuccessorExtension n)
          (decoBottomTotalCompanionSuccessorSlopeRecurrence n)
          (i + 1 : Nat) := by
  unfold decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence
    decoBottomTotalCompanionSuccessorCoreRowLinearRecurrence
    decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence
    decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence
  rw [show (MvPolynomial.C (4 : Real) : MvPolynomial Nat Real) = 4 by
    exact map_ofNat MvPolynomial.C 4]
  exact MvPolynomial.coordinateWronskian_quadratic_discriminant
    (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
    (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
    (decoBottomTotalCompanionSuccessorExtension n)
    (decoBottomTotalCompanionSuccessorSlopeRecurrence n) (i + 1 : Nat)

/-- In named form, the unshifted next-row discriminant is its skew square
minus four times its core and companion factors. -/
theorem
    decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_eq_factors
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i =
      decoBottomTotalCompanionSuccessorCoreRowDiscriminantSkewRecurrence
          n i ^ 2 -
        4 *
          decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreFactorRecurrence
            n i *
          decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactorRecurrence
            n i := by
  rw [decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_eq_plucker]
  rfl

/-- Nonpositivity of an unshifted next-row discriminant is exactly the named
Plücker square-versus-product inequality at the same evaluation. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_nonpos_iff
    (n : Nat) (i : Fin (n + 1)) (x : Nat → Real) :
    MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i) ≤
        0 ↔
      MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowDiscriminantSkewRecurrence
            n i) ^ 2 ≤
        4 * MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreFactorRecurrence
              n i) *
          MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactorRecurrence
              n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_eq_factors]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_mul, map_ofNat]
  constructor <;> intro h <;> linarith

/-- Uniform nonpositivity of all unshifted next-row discriminants is exactly
the uniform family of named Plücker square-versus-product inequalities. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_nonpos_iff_all
    (n : Nat) :
    (∀ i : Fin (n + 1), ∀ x,
      MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i) ≤
          0) ↔
      ∀ i : Fin (n + 1), ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantSkewRecurrence
              n i) ^ 2 ≤
          4 * MvPolynomial.eval x
              (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreFactorRecurrence
                n i) *
            MvPolynomial.eval x
              (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactorRecurrence
                n i) := by
  constructor
  · intro h i x
    exact
      (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_nonpos_iff
        n i x).mp (h i x)
  · intro h i x
    exact
      (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_nonpos_iff
        n i x).mpr (h i x)

/-- The companion extension core is affine in coordinate `0`, with the named
zero-section and slope. -/
theorem decoBottomTotalCompanionExtensionCore_eq_zero_add_X_mul_slope
    (n : Nat) :
    decoBottomTotalCompanionExtensionCore n =
      decoBottomTotalCompanionExtensionCoreZero n +
        MvPolynomial.X 0 *
          decoBottomTotalCompanionExtensionCoreSlope n := by
  exact MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv
    (decoBottomTotalCompanionExtensionCore_isMultiaffine n) 0

/-- The zero-section of the extension core is the companion affine Euler
core plus the preceding companion core. -/
theorem decoBottomTotalCompanionExtensionCoreZero_eq_affineEulerCore_add
    (n : Nat) :
    decoBottomTotalCompanionExtensionCoreZero n =
      MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
          (decoBottomTotalWronskianCompanion n) +
        decoBottomTotalCompanionCore n := by
  have h :=
    decoBottomTotalCompanionExtensionCore_eq_zero_add_X_mul_slope n
  rw [decoBottomTotalCompanionExtensionCore_eq_base_add_X_mul_slope] at h
  exact (add_right_cancel h).symm

/-- The next core zero-section is the positive-coordinate rename of its
unshifted recurrence form. -/
theorem decoBottomTotalCompanionExtensionCoreZero_succ_eq_rename
    (n : Nat) :
    decoBottomTotalCompanionExtensionCoreZero (n + 1) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n) := by
  rw [decoBottomTotalCompanionExtensionCoreZero_eq_affineEulerCore_add]
  have hc : ((n + 1 : Nat) : Real) + 3 = (n : Real) + 4 := by
    push_cast
    ring
  unfold decoBottomTotalCompanionSuccessorCoreZeroRecurrence
  rw [hc, decoBottomTotalWronskianCompanion_succ_eq_rename_extension,
    MvPolynomial.affineEulerCore_rename_succ,
    decoBottomTotalCompanionCore_succ_eq_rename_extensionCore, map_add]

/-- The next core slope is the positive-coordinate rename of its unshifted
recurrence form. -/
theorem decoBottomTotalCompanionExtensionCoreSlope_succ_eq_rename
    (n : Nat) :
    decoBottomTotalCompanionExtensionCoreSlope (n + 1) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n) := by
  rw [decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore]
  have hc : ((n + 1 : Nat) : Real) + 2 = (n : Real) + 3 := by
    push_cast
    ring
  unfold decoBottomTotalCompanionSuccessorCoreSlopeRecurrence
  rw [hc, decoBottomTotalCompanionCore_succ_eq_rename_extensionCore,
    MvPolynomial.affineEulerCore_rename_succ]

/-- The constant row coefficient splits into an affine Euler row of the
companion and the current companion-data Wronskian. -/
theorem decoBottomTotalCompanionSuccessorCoreRowConstant_eq_add
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstant n i =
      MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
          (decoBottomTotalWronskianCompanion n) i.succ +
        MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore n)
          (decoBottomTotalWronskianCompanion n) (i + 1 : Nat) := by
  have hrow := MvPolynomial.coordinateWronskian_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 3 : Real) (decoBottomTotalWronskianCompanion n) i.succ
  change MvPolynomial.coordinateWronskian
      (MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
        (decoBottomTotalWronskianCompanion n))
      (decoBottomTotalWronskianCompanion n) (i + 1 : Nat) = _ at hrow
  unfold decoBottomTotalCompanionSuccessorCoreRowConstant
  rw [decoBottomTotalCompanionExtensionCoreZero_eq_affineEulerCore_add,
    MvPolynomial.coordinateWronskian_add_left, hrow]

/-- The unshifted constant recurrence is the successor-extension affine-Euler
row plus the current successor core row. -/
theorem decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence_eq_add
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i =
      MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalCompanionSuccessorExtension n) i.succ +
        decoBottomTotalCompanionSuccessorCoreRow n i := by
  unfold decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence
    decoBottomTotalCompanionSuccessorCoreZeroRecurrence
  rw [MvPolynomial.coordinateWronskian_add_left]
  have hrow := MvPolynomial.coordinateWronskian_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) → Nat) Fin.valEmbedding.injective
    (n + 4 : Real) (decoBottomTotalCompanionSuccessorExtension n) i.succ
  have hcore :=
    coordinateWronskian_companionExtensionCore_successorExtension n i
  simpa only [Fin.valEmbedding_apply, Fin.val_succ] using
    congrArg₂ (· + ·) hrow hcore

/-- The quadratic row coefficient splits into a mixed core/total row and an
affine Euler row of the preceding companion core. -/
theorem decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_add
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadratic n i =
      MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
            (decoBottomTotalCompanionCore n))
          (decoBottomTotal (n + 1)) (i + 1 : Nat) +
        MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
          (decoBottomTotalCompanionCore n) i.succ := by
  have hrow := MvPolynomial.coordinateWronskian_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 2 : Real) (decoBottomTotalCompanionCore n) i.succ
  change MvPolynomial.coordinateWronskian
      (MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
        (decoBottomTotalCompanionCore n))
      (decoBottomTotalCompanionCore n) (i + 1 : Nat) = _ at hrow
  unfold decoBottomTotalCompanionSuccessorCoreRowQuadratic
    decoBottomTotalCompanionSlope
  rw [decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore,
    MvPolynomial.coordinateWronskian_add_right, hrow]

/-- The unshifted quadratic recurrence is the mixed
core/total-extension Wronskian plus the current extension-core affine-Euler
row. -/
theorem decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_eq_add
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i =
      MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 3 : Real)
            (decoBottomTotalCompanionExtensionCore n))
          (decoBottomTotalCompanionTotalExtension n) (i + 1 : Nat) +
        MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalCompanionExtensionCore n) i.succ := by
  unfold decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence
    decoBottomTotalCompanionSuccessorCoreSlopeRecurrence
    decoBottomTotalCompanionSuccessorSlopeRecurrence
  rw [MvPolynomial.coordinateWronskian_add_right]
  have hrow := MvPolynomial.coordinateWronskian_affineEulerCore
    (Fin.valEmbedding : Fin (n + 2) → Nat) Fin.valEmbedding.injective
    (n + 3 : Real) (decoBottomTotalCompanionExtensionCore n) i.succ
  simpa only [Fin.valEmbedding_apply, Fin.val_succ] using
    congrArg₂ (· + ·) rfl hrow

/-- The constant row coefficient is its companion value-one endpoint product,
off-row affine-Euler remainder, and current companion-data Wronskian. -/
theorem decoBottomTotalCompanionSuccessorCoreRowConstant_eq_endpoint_remainder
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstant n i =
      ((MvPolynomial.specializeZero (i + 1 : Nat)
            (decoBottomTotalWronskianCompanion n) +
          MvPolynomial.pderiv (i + 1 : Nat)
            (decoBottomTotalWronskianCompanion n)) *
        MvPolynomial.pderiv (i + 1 : Nat)
          (decoBottomTotalWronskianCompanion n) +
        MvPolynomial.affineEulerRayleighRemainder
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalWronskianCompanion n) i.succ) +
      MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore n)
        (decoBottomTotalWronskianCompanion n) (i + 1 : Nat) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowConstant_eq_add,
    MvPolynomial.IsMultiaffine.affineEulerRayleighRow_eq_erase
      (decoBottomTotalWronskianCompanion_isMultiaffine n)
      (Fin.valEmbedding : Fin (n + 2) → Nat) i.succ]
  simp only [Fin.valEmbedding_apply, Fin.val_succ]

/-- The constant row coefficient uses the canonical value-one section of the
companion, its derivative, the off-row remainder, and the current data
Wronskian. -/
theorem decoBottomTotalCompanionSuccessorCoreRowConstant_eq_specializeAt_one_remainder
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstant n i =
      (MvPolynomial.specializeAt (i + 1 : Nat) 1
          (decoBottomTotalWronskianCompanion n) *
        MvPolynomial.pderiv (i + 1 : Nat)
          (decoBottomTotalWronskianCompanion n) +
        MvPolynomial.affineEulerRayleighRemainder
          (Fin.valEmbedding : Fin (n + 2) → Nat)
          (decoBottomTotalWronskianCompanion n) i.succ) +
      MvPolynomial.coordinateWronskian
        (decoBottomTotalCompanionCore n)
        (decoBottomTotalWronskianCompanion n) (i + 1 : Nat) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowConstant_eq_endpoint_remainder,
    MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
      (decoBottomTotalWronskianCompanion_isMultiaffine n) (i + 1 : Nat)]

/-- The quadratic row coefficient is its mixed endpoint Wronskian plus the
core value-one endpoint product and off-row affine-Euler remainder. -/
theorem decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_endpoint_remainder
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadratic n i =
      MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 2 : Real)
            (decoBottomTotalCompanionCore n))
          (decoBottomTotal (n + 1)) (i + 1 : Nat) +
        ((MvPolynomial.specializeZero (i + 1 : Nat)
              (decoBottomTotalCompanionCore n) +
            MvPolynomial.pderiv (i + 1 : Nat)
              (decoBottomTotalCompanionCore n)) *
          MvPolynomial.pderiv (i + 1 : Nat)
            (decoBottomTotalCompanionCore n) +
          MvPolynomial.affineEulerRayleighRemainder
            (Fin.valEmbedding : Fin (n + 2) → Nat)
            (decoBottomTotalCompanionCore n) i.succ) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_add,
    MvPolynomial.IsMultiaffine.affineEulerRayleighRow_eq_erase
      (decoBottomTotalCompanionCore_isMultiaffine n)
      (Fin.valEmbedding : Fin (n + 2) → Nat) i.succ]
  simp only [Fin.valEmbedding_apply, Fin.val_succ]

/-- The quadratic row coefficient uses the canonical value-one section of the
companion core, its derivative, the off-row remainder, and the mixed
core/latest-total Wronskian. -/
theorem decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_specializeAt_one_remainder
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadratic n i =
      MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 2 : Real)
            (decoBottomTotalCompanionCore n))
          (decoBottomTotal (n + 1)) (i + 1 : Nat) +
        (MvPolynomial.specializeAt (i + 1 : Nat) 1
            (decoBottomTotalCompanionCore n) *
          MvPolynomial.pderiv (i + 1 : Nat)
            (decoBottomTotalCompanionCore n) +
          MvPolynomial.affineEulerRayleighRemainder
            (Fin.valEmbedding : Fin (n + 2) → Nat)
            (decoBottomTotalCompanionCore n) i.succ) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_endpoint_remainder,
    MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
      (decoBottomTotalCompanionCore_isMultiaffine n) (i + 1 : Nat)]

/-- Away from the distinguished first row, the next constant endpoint is the
shift of the successor-extension affine-Euler row plus the current successor
core row. -/
theorem decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstant (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.affineEulerRayleighRow
            (Fin.valEmbedding : Fin (n + 2) → Nat)
            (decoBottomTotalCompanionSuccessorExtension n) i.succ +
          decoBottomTotalCompanionSuccessorCoreRow n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowConstant_eq_add,
    affineEulerRayleighRow_companion_succ_fin]
  have hcoord :=
    coordinateWronskian_companionCore_companion_succ_fin n i
  rw [show MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionCore (n + 1))
      (decoBottomTotalWronskianCompanion (n + 1))
      ((i.succ : Fin (n + 2)) + 1 : Nat) =
        MvPolynomial.rename (fun j : Nat => j + 1)
          (decoBottomTotalCompanionSuccessorCoreRow n i) by
    simpa only [Fin.val_succ, Nat.add_assoc] using hcoord,
    map_add]

/-- Away from the distinguished first row, the next quadratic endpoint is
the shift of the mixed total-extension Wronskian plus the affine-Euler row of
the current extension core. -/
theorem decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadratic (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
            (MvPolynomial.affineEulerCore
              (Fin.valEmbedding : Fin (n + 2) → Nat) (n + 3 : Real)
              (decoBottomTotalCompanionExtensionCore n))
            (decoBottomTotalCompanionTotalExtension n) (i + 1 : Nat) +
          MvPolynomial.affineEulerRayleighRow
            (Fin.valEmbedding : Fin (n + 2) → Nat)
            (decoBottomTotalCompanionExtensionCore n) i.succ) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_add]
  have hc : ((n + 1 : Nat) : Real) + 2 = (n : Real) + 3 := by
    push_cast
    ring
  have hmixed :=
    coordinateWronskian_affineEulerCore_companionCore_succ_total_add_two
      n (i : Nat)
  have hrow := affineEulerRayleighRow_companionCore_succ_fin n i
  have hsum := congrArg₂ (· + ·) hmixed hrow
  simpa only [hc, Nat.add_assoc, Fin.val_succ, map_add] using hsum

/-- The complete next constant coefficient is the positive-coordinate rename
of its named unshifted recurrence. -/
theorem
    decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_eq_recurrence
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstant (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin,
    decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence_eq_add]

/-- The complete next quadratic coefficient is the positive-coordinate
rename of its named unshifted recurrence. -/
theorem
    decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_eq_recurrence
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadratic (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin,
    decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence_eq_add]

/-- The complete next linear coefficient is the positive-coordinate rename
of its named unshifted recurrence. -/
theorem decoBottomTotalCompanionSuccessorCoreRowLinear_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowLinear (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreRowLinearRecurrence n i) := by
  unfold decoBottomTotalCompanionSuccessorCoreRowLinear
    decoBottomTotalCompanionSuccessorCoreRowLinearRecurrence
  rw [decoBottomTotalCompanionExtensionCoreZero_succ_eq_rename,
    decoBottomTotalCompanionSlope_succ_eq_rename,
    decoBottomTotalCompanionExtensionCoreSlope_succ_eq_rename,
    decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  have hleft := MvPolynomial.coordinateWronskian_rename
    (fun j : Nat => j + 1) (by intro j k h; lia)
    (decoBottomTotalCompanionSuccessorCoreZeroRecurrence n)
    (decoBottomTotalCompanionSuccessorSlopeRecurrence n) (i + 1 : Nat)
  have hright := MvPolynomial.coordinateWronskian_rename
    (fun j : Nat => j + 1) (by intro j k h; lia)
    (decoBottomTotalCompanionSuccessorCoreSlopeRecurrence n)
    (decoBottomTotalCompanionSuccessorExtension n) (i + 1 : Nat)
  have hsum := congrArg₂ (· + ·) hleft hright
  simpa only [Fin.val_succ, Nat.add_assoc, map_add] using hsum

/-- Every non-distinguished next row discriminant is the
positive-coordinate rename of its named unshifted recurrence. -/
theorem decoBottomTotalCompanionSuccessorCoreRowDiscriminant_succ_fin
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowDiscriminant (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i) := by
  unfold decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence
  rw [decoBottomTotalCompanionSuccessorCoreRowLinear_succ_fin,
    decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_eq_recurrence,
    decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_eq_recurrence,
    map_sub, map_pow, map_mul, map_mul, MvPolynomial.rename_C]

/-- Universal nonnegativity of a non-distinguished next constant coefficient
is exactly universal nonnegativity of its unshifted recurrence. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_nonneg_iff
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowConstant (n + 1) i.succ)) ↔
      ∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_eq_recurrence]
  exact MvPolynomial.forall_eval_rename_iff
    (fun j : Nat => j + 1) (by intro j k h; lia)
    (decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i)
    (fun y : Real => 0 ≤ y)

/-- Universal nonnegativity of a non-distinguished next quadratic coefficient
is exactly universal nonnegativity of its unshifted recurrence. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_nonneg_iff
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic (n + 1) i.succ)) ↔
      ∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_eq_recurrence]
  exact MvPolynomial.forall_eval_rename_iff
    (fun j : Nat => j + 1) (by intro j k h; lia)
    (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i)
    (fun y : Real => 0 ≤ y)

/-- Universal nonpositivity of a non-distinguished next discriminant is
exactly universal nonpositivity of its unshifted recurrence. -/
theorem
    eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminant_succ_fin_nonpos_iff
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant (n + 1) i.succ) ≤
        0) ↔
      ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i) ≤
          0 := by
  rw [decoBottomTotalCompanionSuccessorCoreRowDiscriminant_succ_fin]
  exact MvPolynomial.forall_eval_rename_iff
    (fun j : Nat => j + 1) (by intro j k h; lia)
    (decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i)
    (fun y : Real => y ≤ 0)

/-- Each successor core row is exactly quadratic in the remaining fresh
coordinate, with the three named endpoint-Wronskian coefficients. -/
theorem decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRow n i =
      decoBottomTotalCompanionSuccessorCoreRowConstant n i +
        MvPolynomial.X 0 *
          decoBottomTotalCompanionSuccessorCoreRowLinear n i +
        MvPolynomial.X 0 ^ 2 *
          decoBottomTotalCompanionSuccessorCoreRowQuadratic n i := by
  rw [← coordinateWronskian_companionExtensionCore_successorExtension,
    decoBottomTotalCompanionExtensionCore_eq_zero_add_X_mul_slope]
  unfold decoBottomTotalCompanionSuccessorExtension
    decoBottomTotalCompanionSuccessorCoreRowConstant
    decoBottomTotalCompanionSuccessorCoreRowLinear
    decoBottomTotalCompanionSuccessorCoreRowQuadratic
  exact MvPolynomial.coordinateWronskian_add_X_mul_add_X_mul_of_ne
    _ _ _ _ (i + 1 : Nat) 0 (by lia)

/-- Every non-distinguished next successor-core row is the fresh-coordinate
quadratic assembled from the three named unshifted coefficient recurrences. -/
theorem decoBottomTotalCompanionSuccessorCoreRow_succ_fin_eq_recurrence
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRow (n + 1) i.succ =
      MvPolynomial.rename (fun j : Nat => j + 1)
          (decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i) +
        MvPolynomial.X 0 *
          MvPolynomial.rename (fun j : Nat => j + 1)
            (decoBottomTotalCompanionSuccessorCoreRowLinearRecurrence n i) +
        MvPolynomial.X 0 ^ 2 *
          MvPolynomial.rename (fun j : Nat => j + 1)
            (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence
              n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic,
    decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_eq_recurrence,
    decoBottomTotalCompanionSuccessorCoreRowLinear_succ_fin,
    decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_eq_recurrence]

/-- Evaluation of a successor core row is the corresponding scalar quadratic
in the fresh coordinate. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic
    (n : Nat) (i : Fin (n + 1)) (x : Nat → Real) :
    MvPolynomial.eval x (decoBottomTotalCompanionSuccessorCoreRow n i) =
      MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowConstant n i) +
        x 0 * MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowLinear n i) +
        x 0 ^ 2 * MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, map_pow]

/-- The core zero-section is independent of its specialized coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionExtensionCoreZero
    (n : Nat) :
    0 ∉ (decoBottomTotalCompanionExtensionCoreZero n).vars := by
  intro h
  have herase := MvPolynomial.vars_specializeZero_subset_erase
    (decoBottomTotalCompanionExtensionCore n) 0 h
  exact (Finset.mem_erase.mp herase).1 rfl

/-- The core slope is independent of its differentiated coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionExtensionCoreSlope
    (n : Nat) :
    0 ∉ (decoBottomTotalCompanionExtensionCoreSlope n).vars := by
  exact MvPolynomial.IsMultiaffine.notMem_vars_pderiv_self
    (decoBottomTotalCompanionExtensionCore_isMultiaffine n) 0

/-- The constant row coefficient is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowConstant n i).vars := by
  unfold decoBottomTotalCompanionSuccessorCoreRowConstant
  exact MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreZero n)
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n) (i + 1 : Nat)

/-- The linear row coefficient is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowLinear n i).vars := by
  have hleft := MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreZero n)
    (zero_notMem_vars_decoBottomTotalCompanionSlope n) (i + 1 : Nat)
  have hright := MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreSlope n)
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n) (i + 1 : Nat)
  intro h
  exact (Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ h)).elim
    hleft hright

/-- The quadratic row coefficient is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i).vars := by
  unfold decoBottomTotalCompanionSuccessorCoreRowQuadratic
  exact MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreSlope n)
    (zero_notMem_vars_decoBottomTotalCompanionSlope n) (i + 1 : Nat)

private theorem notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    {n : Nat} {i : Fin (n + 1)} {k : Nat}
    (hlinear : k ∉
      (decoBottomTotalCompanionSuccessorCoreRowLinear n i).vars)
    (hquadratic : k ∉
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i).vars)
    (hconstant : k ∉
      (decoBottomTotalCompanionSuccessorCoreRowConstant n i).vars) :
    k ∉ (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i).vars := by
  intro h
  unfold decoBottomTotalCompanionSuccessorCoreRowDiscriminant at h
  rcases Finset.mem_union.mp
      (MvPolynomial.vars_sub_subset
        (p := decoBottomTotalCompanionSuccessorCoreRowLinear n i ^ 2)
        (q := MvPolynomial.C 4 *
          decoBottomTotalCompanionSuccessorCoreRowQuadratic n i *
            decoBottomTotalCompanionSuccessorCoreRowConstant n i) h) with
    hleft | hright
  · exact hlinear (MvPolynomial.vars_pow _ 2 hleft)
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hright) with
      hproduct | hconstantMem
    · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hproduct) with
        hfour | hquadraticMem
      · simp at hfour
      · exact hquadratic hquadraticMem
    · exact hconstant hconstantMem

/-- The row discriminant is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i).vars :=
  notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear n i)
    (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
    (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i)

/-- The constant row coefficient is independent of the row coordinate. -/
theorem add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant
    (n : Nat) (i : Fin (n + 1)) :
    (i + 1 : Nat) ∉
      (decoBottomTotalCompanionSuccessorCoreRowConstant n i).vars := by
  unfold decoBottomTotalCompanionSuccessorCoreRowConstant
  exact MvPolynomial.IsMultiaffine.notMem_vars_coordinateWronskian
    (MvPolynomial.IsMultiaffine.specializeZero_preserves
      (decoBottomTotalCompanionExtensionCore_isMultiaffine n) 0)
    (decoBottomTotalWronskianCompanion_isMultiaffine n) (i + 1 : Nat)

/-- The linear row coefficient is independent of the row coordinate. -/
theorem add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear
    (n : Nat) (i : Fin (n + 1)) :
    (i + 1 : Nat) ∉
      (decoBottomTotalCompanionSuccessorCoreRowLinear n i).vars := by
  have hleft :=
    MvPolynomial.IsMultiaffine.notMem_vars_coordinateWronskian
      (MvPolynomial.IsMultiaffine.specializeZero_preserves
        (decoBottomTotalCompanionExtensionCore_isMultiaffine n) 0)
      (decoBottomTotalCompanionSlope_isMultiaffine n) (i + 1 : Nat)
  have hright :=
    MvPolynomial.IsMultiaffine.notMem_vars_coordinateWronskian
      ((decoBottomTotalCompanionExtensionCore_isMultiaffine n).pderiv 0)
      (decoBottomTotalWronskianCompanion_isMultiaffine n) (i + 1 : Nat)
  unfold decoBottomTotalCompanionSuccessorCoreRowLinear
  intro h
  exact (Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ h)).elim
    hleft hright

/-- The quadratic row coefficient is independent of the row coordinate. -/
theorem add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic
    (n : Nat) (i : Fin (n + 1)) :
    (i + 1 : Nat) ∉
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i).vars := by
  unfold decoBottomTotalCompanionSuccessorCoreRowQuadratic
  exact MvPolynomial.IsMultiaffine.notMem_vars_coordinateWronskian
    ((decoBottomTotalCompanionExtensionCore_isMultiaffine n).pderiv 0)
    (decoBottomTotalCompanionSlope_isMultiaffine n) (i + 1 : Nat)

/-- The row discriminant is independent of the row coordinate. -/
theorem add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    (n : Nat) (i : Fin (n + 1)) :
    (i + 1 : Nat) ∉
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i).vars :=
  notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear n i)
    (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
    (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i)

/-- Global nonnegativity of a successor core row is exactly nonnegativity of
its leading and constant coefficients together with nonpositivity of its
fresh-coordinate discriminant. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      (∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)) ∧
      (∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowConstant n i)) ∧
      ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0 := by
  have hconstant :=
    zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i
  have hlinear :=
    zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear n i
  have hquadratic :=
    zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i
  constructor
  · intro h
    have hscalar (x : Nat → Real) : ∀ t : Real,
        0 ≤ MvPolynomial.eval x
              (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i) *
            (t * t) +
          MvPolynomial.eval x
              (decoBottomTotalCompanionSuccessorCoreRowLinear n i) * t +
          MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowConstant n i) := by
      intro t
      have ht := h (Function.update x 0 t)
      rw [eval_decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic,
        MvPolynomial.eval_update_eq_of_notMem_vars hconstant,
        MvPolynomial.eval_update_eq_of_notMem_vars hlinear,
        MvPolynomial.eval_update_eq_of_notMem_vars hquadratic] at ht
      simp only [Function.update, dite_true] at ht
      simpa only [pow_two, mul_comm,
        add_comm, add_left_comm, add_assoc] using ht
    refine ⟨fun x => quadratic_leadingCoeff_nonneg (hscalar x), ?_, ?_⟩
    · intro x
      simpa using hscalar x 0
    · intro x
      have hdisc := discrim_le_zero (hscalar x)
      simpa [decoBottomTotalCompanionSuccessorCoreRowDiscriminant,
        discrim] using hdisc
  · rintro ⟨hquadraticNonneg, hconstantNonneg, hdisc⟩ x
    have hdiscEval :
        discrim
          (MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i))
          (MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowLinear n i))
          (MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowConstant n i)) ≤ 0 := by
      simpa [decoBottomTotalCompanionSuccessorCoreRowDiscriminant,
        discrim] using hdisc x
    have hnonneg := quadratic_nonneg_of_nonneg_of_discrim_nonpos
      (hquadraticNonneg x) (hconstantNonneg x) hdiscEval (x 0)
    rw [eval_decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic]
    simpa only [pow_two, mul_comm, add_comm, add_left_comm, add_assoc]
      using hnonneg

/-- The exact finite coefficient conditions for nonnegativity of every
successor core row.  This packages proof obligations and does not assert that
they hold. -/
structure DecoBottomTotalCompanionSuccessorCoreQuadraticData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
  constant_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowConstant n i)
  discriminant_nonpos : ∀ i : Fin (n + 1), ∀ x,
    MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0

/-- The coefficient conditions for the distinguished first row at the next
rank.  This packages the boundary obligations not covered by the shifted
recurrence. -/
structure DecoBottomTotalCompanionSuccessorCoreDistinguishedQuadraticData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ x, 0 ≤ MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowQuadratic (n + 1) 0)
  constant_nonneg : ∀ x, 0 ≤ MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowConstant (n + 1) 0)
  discriminant_nonpos : ∀ x, MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowDiscriminant (n + 1) 0) ≤ 0

/-- The unshifted coefficient conditions for all recurrence-controlled rows at
the next rank. -/
structure DecoBottomTotalCompanionSuccessorCoreRecurrenceQuadraticData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i)
  constant_nonneg : ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i)
  discriminant_nonpos : ∀ i : Fin (n + 1), ∀ x, MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence n i) ≤ 0

/-- The recurrence-controlled coefficient conditions with the discriminant
obligation exposed as its exact Plücker square-versus-product inequality. -/
structure DecoBottomTotalCompanionSuccessorCoreRecurrenceFactorData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowQuadraticRecurrence n i)
  constant_nonneg : ∀ i : Fin (n + 1), ∀ x, 0 ≤ MvPolynomial.eval x
    (decoBottomTotalCompanionSuccessorCoreRowConstantRecurrence n i)
  discriminant_bound : ∀ i : Fin (n + 1), ∀ x,
    MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminantSkewRecurrence
          n i) ^ 2 ≤
      4 * MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreFactorRecurrence
            n i) *
        MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionFactorRecurrence
            n i)

/-- Recurrence quadratic data is exactly the same endpoint data with its
discriminant condition written as the named Plücker factor inequality. -/
theorem
    decoBottomTotalCompanionSuccessorCoreRecurrenceQuadraticData_iff_factorData
    (n : Nat) :
    DecoBottomTotalCompanionSuccessorCoreRecurrenceQuadraticData n ↔
      DecoBottomTotalCompanionSuccessorCoreRecurrenceFactorData n := by
  constructor
  · intro h
    exact ⟨h.quadratic_nonneg, h.constant_nonneg,
      (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_nonpos_iff_all
        n).mp h.discriminant_nonpos⟩
  · intro h
    exact ⟨h.quadratic_nonneg, h.constant_nonneg,
      (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminantRecurrence_nonpos_iff_all
        n).mpr h.discriminant_bound⟩

/-- The next-rank coefficient data splits exactly into the distinguished first
row and the unshifted recurrence data for every remaining row. -/
theorem decoBottomTotalCompanionSuccessorCoreQuadraticData_succ_iff
    (n : Nat) :
    DecoBottomTotalCompanionSuccessorCoreQuadraticData (n + 1) ↔
      DecoBottomTotalCompanionSuccessorCoreDistinguishedQuadraticData n ∧
        DecoBottomTotalCompanionSuccessorCoreRecurrenceQuadraticData n := by
  constructor
  · intro h
    have hquadratic := Fin.forall_fin_succ.mp h.quadratic_nonneg
    have hconstant := Fin.forall_fin_succ.mp h.constant_nonneg
    have hdiscriminant := Fin.forall_fin_succ.mp h.discriminant_nonpos
    refine ⟨⟨hquadratic.1, hconstant.1, hdiscriminant.1⟩, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact
        (eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_nonneg_iff
          n i).mp (hquadratic.2 i)
    · intro i
      exact
        (eval_decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_nonneg_iff
          n i).mp (hconstant.2 i)
    · intro i
      exact
        (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminant_succ_fin_nonpos_iff
          n i).mp (hdiscriminant.2 i)
  · rintro ⟨hfirst, hrecurrence⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.forall_fin_succ]
      exact ⟨hfirst.quadratic_nonneg, fun i =>
        (eval_decoBottomTotalCompanionSuccessorCoreRowQuadratic_succ_fin_nonneg_iff
          n i).mpr (hrecurrence.quadratic_nonneg i)⟩
    · rw [Fin.forall_fin_succ]
      exact ⟨hfirst.constant_nonneg, fun i =>
        (eval_decoBottomTotalCompanionSuccessorCoreRowConstant_succ_fin_nonneg_iff
          n i).mpr (hrecurrence.constant_nonneg i)⟩
    · rw [Fin.forall_fin_succ]
      exact ⟨hfirst.discriminant_nonpos, fun i =>
        (eval_decoBottomTotalCompanionSuccessorCoreRowDiscriminant_succ_fin_nonpos_iff
          n i).mpr (hrecurrence.discriminant_nonpos i)⟩

/-- Equivalently, the complete next-rank coefficient data consists of the
distinguished first row and the exact Plücker factor inequalities for the
recurrence-controlled tail. -/
theorem decoBottomTotalCompanionSuccessorCoreQuadraticData_succ_iff_factorData
    (n : Nat) :
    DecoBottomTotalCompanionSuccessorCoreQuadraticData (n + 1) ↔
      DecoBottomTotalCompanionSuccessorCoreDistinguishedQuadraticData n ∧
        DecoBottomTotalCompanionSuccessorCoreRecurrenceFactorData n :=
  (decoBottomTotalCompanionSuccessorCoreQuadraticData_succ_iff n).trans
    (and_congr Iff.rfl
      (decoBottomTotalCompanionSuccessorCoreRecurrenceQuadraticData_iff_factorData
        n))

/-- The exact successor-row coefficient conditions on the canonical slice
where the absent fresh coordinate is `0` and the absent row coordinate is `1`.
This packages proof obligations and does not assert that they hold. -/
structure DecoBottomTotalCompanionSuccessorCoreReducedQuadraticData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval
      (Function.update (Function.update x 0 0) (i + 1 : Nat) 1)
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
  constant_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval
      (Function.update (Function.update x 0 0) (i + 1 : Nat) 1)
      (decoBottomTotalCompanionSuccessorCoreRowConstant n i)
  discriminant_nonpos : ∀ i : Fin (n + 1), ∀ x,
    MvPolynomial.eval
      (Function.update (Function.update x 0 0) (i + 1 : Nat) 1)
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0

/-- The successor-row coefficient conditions are unchanged after fixing the
two coordinates absent from every coefficient polynomial. -/
theorem decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_reduced
    (n : Nat) :
    DecoBottomTotalCompanionSuccessorCoreQuadraticData n ↔
      DecoBottomTotalCompanionSuccessorCoreReducedQuadraticData n := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (MvPolynomial.forall_eval_iff_forall_eval_update_update_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
        (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
        0 1 (fun y : Real ↦ 0 ≤ y)).mp (h.quadratic_nonneg i)
    · intro i
      exact (MvPolynomial.forall_eval_iff_forall_eval_update_update_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i)
        (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i)
        0 1 (fun y : Real ↦ 0 ≤ y)).mp (h.constant_nonneg i)
    · intro i
      exact (MvPolynomial.forall_eval_iff_forall_eval_update_update_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i)
        (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i)
        0 1 (fun y : Real ↦ y ≤ 0)).mp (h.discriminant_nonpos i)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (MvPolynomial.forall_eval_iff_forall_eval_update_update_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
        (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
        0 1 (fun y : Real ↦ 0 ≤ y)).mpr (h.quadratic_nonneg i)
    · intro i
      exact (MvPolynomial.forall_eval_iff_forall_eval_update_update_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i)
        (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i)
        0 1 (fun y : Real ↦ 0 ≤ y)).mpr (h.constant_nonneg i)
    · intro i
      exact (MvPolynomial.forall_eval_iff_forall_eval_update_update_of_notMem_vars
        (zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i)
        (add_one_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i)
        0 1 (fun y : Real ↦ y ≤ 0)).mpr (h.discriminant_nonpos i)

/-- The same finite endpoint conditions with the constant coefficient written
as compensation against the current companion-data Wronskian and the
quadratic coefficient expanded into its genuinely new two summands. -/
structure DecoBottomTotalCompanionSuccessorCoreEndpointData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
            (decoBottomTotalCompanionCore n))
          (decoBottomTotal (n + 1)) (i + 1 : Nat)) +
      MvPolynomial.eval x
        (MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
          (decoBottomTotalCompanionCore n) i.succ)
  constant_compensation : ∀ i : Fin (n + 1), ∀ x,
    -MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore n)
          (decoBottomTotalWronskianCompanion n) (i + 1 : Nat)) ≤
      MvPolynomial.eval x
        (MvPolynomial.affineEulerRayleighRow
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat)
          (decoBottomTotalWronskianCompanion n) i.succ)
  discriminant_nonpos : ∀ i : Fin (n + 1), ∀ x,
    MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0

/-- Quadratic coefficient data is exactly the expanded endpoint package; in
particular, the constant condition is a compensation inequality rather than a
stronger separate sign requirement. -/
theorem decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_endpointData
    (n : Nat) :
    DecoBottomTotalCompanionSuccessorCoreQuadraticData n ↔
      DecoBottomTotalCompanionSuccessorCoreEndpointData n := by
  constructor
  · intro h
    refine ⟨?_, ?_, h.discriminant_nonpos⟩
    · intro i x
      rw [← MvPolynomial.eval_add,
        ← decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_add]
      exact h.quadratic_nonneg i x
    · intro i x
      have hconstant := h.constant_nonneg i x
      rw [decoBottomTotalCompanionSuccessorCoreRowConstant_eq_add,
        MvPolynomial.eval_add] at hconstant
      linarith
  · intro h
    refine ⟨?_, ?_, h.discriminant_nonpos⟩
    · intro i x
      rw [decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_add,
        MvPolynomial.eval_add]
      exact h.quadratic_nonneg i x
    · intro i x
      have hconstant := h.constant_compensation i x
      rw [decoBottomTotalCompanionSuccessorCoreRowConstant_eq_add,
        MvPolynomial.eval_add]
      linarith

/-- The expanded endpoint conditions are exactly the coefficient conditions
after removing their two inessential coordinates. -/
theorem decoBottomTotalCompanionSuccessorCoreEndpointData_iff_reduced
    (n : Nat) :
    DecoBottomTotalCompanionSuccessorCoreEndpointData n ↔
      DecoBottomTotalCompanionSuccessorCoreReducedQuadraticData n :=
  (decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_endpointData n).symm.trans
    (decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_reduced n)

/-- The finite successor core rows are nonnegative exactly when their bundled
quadratic coefficient data holds. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff
    (n : Nat) :
    (∀ i : Fin (n + 1), ∀ x,
      0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      DecoBottomTotalCompanionSuccessorCoreQuadraticData n := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
        n i).mp (h i) |>.1
    · intro i
      exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
        n i).mp (h i) |>.2.1
    · intro i
      exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
        n i).mp (h i) |>.2.2
  · intro h i
    exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
      n i).mpr ⟨h.quadratic_nonneg i, h.constant_nonneg i,
        h.discriminant_nonpos i⟩

/-- Global nonnegativity of all finite successor rows is exactly the reduced
two-coordinate coefficient package. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff_reduced
    (n : Nat) :
    (∀ i : Fin (n + 1), ∀ x,
      0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      DecoBottomTotalCompanionSuccessorCoreReducedQuadraticData n :=
  (eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff n).trans
    (decoBottomTotalCompanionSuccessorCoreQuadraticData_iff_reduced n)

end

end RealRooted.Applications.OEIS
