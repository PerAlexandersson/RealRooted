import RealRooted.Applications.OEIS.A144438.LayerTotal

/-!
# Ordinary-coordinate recurrence for the Deco layer total

This file defines the dehomogenized positive-label total directly through its
normal and exceptional recurrences.  It then proves that this definition is
exactly the finite-coordinate `decoLayerTotal` after dehomogenization and
coordinate embedding.

No stability claim is made for the total.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The ordinary-coordinate Deco total, defined directly by the
normal-plus-exceptional bottom-variable recurrence. -/
def decoBottomTotal : Nat → MvPolynomial Nat Real
  | 0 => 1
  | 1 => decoNormalBottomStep 0 1
  | n + 2 =>
      decoNormalBottomStep (n + 1) (decoBottomTotal (n + 1)) +
        decoExceptionalBottomStep (decoBottomTotal n)

@[simp] theorem decoBottomTotal_zero : decoBottomTotal 0 = 1 := rfl

@[simp] theorem decoBottomTotal_one :
    decoBottomTotal 1 = 1 + MvPolynomial.X 1 := by
  simp [decoBottomTotal, decoNormalBottomStep, decoNormalBottomCore]

/-- The defining ordinary-coordinate two-step recurrence. -/
theorem decoBottomTotal_recurrence (n : Nat) :
    decoBottomTotal (n + 2) =
      decoNormalBottomStep (n + 1) (decoBottomTotal (n + 1)) +
        decoExceptionalBottomStep (decoBottomTotal n) := rfl

/-- Every recurrence-defined bottom total has constant coefficient one. -/
@[simp] theorem constantCoeff_decoBottomTotal : ∀ n : Nat,
    MvPolynomial.constantCoeff (decoBottomTotal n) = 1 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [decoBottomTotal_recurrence, map_add,
        constantCoeff_decoNormalBottomStep,
        constantCoeff_decoExceptionalBottomStep, ih1]
      simp

/-- The recurrence-defined bottom total is never the zero polynomial. -/
theorem decoBottomTotal_ne_zero (n : Nat) : decoBottomTotal n ≠ 0 := by
  intro hzero
  have h := congrArg MvPolynomial.constantCoeff hzero
  simp at h

/-- Dehomogenizing the finite-coordinate layer total and embedding its
ordinary coordinates as positive labels recovers the directly recursive
ordinary-coordinate total. -/
theorem rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal :
    ∀ n : Nat,
      MvPolynomial.rename (decoLayerBottomEmbedding n)
          (MvPolynomial.dehomogenize (decoLayerTotal n)) =
        decoBottomTotal n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [decoLayerTotal]
  | one =>
      rw [decoLayerTotal_one,
        rename_dehomogenize_decoNormalLayerStep_eq_decoNormalBottomStep]
      · simp [decoBottomTotal]
      · exact MvPolynomial.isHomogeneous_X Real
          (none : DecoLayerCoord 0)
  | more n ih0 ih1 =>
      rw [decoLayerTotal_recurrence]
      simp only [map_add]
      rw [rename_dehomogenize_decoNormalLayerStep_eq_decoNormalBottomStep
          (decoLayerTotal_isHomogeneous (n + 1)),
        rename_dehomogenize_decoExceptionalLayerStep_eq_decoExceptionalBottomStep,
        ih0, ih1, decoBottomTotal_recurrence]

end


end RealRooted.Applications.OEIS
