import RealRooted.Applications.OEIS.A144438.LayerTotal
import RealRooted.MultivariateStability.LinearForm

/-!
# Initial stability certificates for the Deco layer total

The first three recurrence-defined totals are multivariate real stable.  The
rank-two proof rewrites the two recurrence branches as one nonnegative
directional-derivative pencil.  No claim is made here for higher-rank totals:
stability is not closed under the outer addition in the defining recurrence.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The rank-zero recurrence-defined layer total is multivariate real
stable. -/
theorem decoLayerTotal_zero_mvRealStable :
    MvRealStable (decoLayerTotal 0) := by
  simpa using (MvRealStable.X (none : DecoLayerCoord 0))

/-- The rank-one recurrence-defined layer total is multivariate real
stable. -/
theorem decoLayerTotal_one_mvRealStable :
    MvRealStable (decoLayerTotal 1) := by
  rw [decoLayerTotal_one]
  exact decoNormalLayerStep_mvRealStable
    (MvRealStable.X (none : DecoLayerCoord 0))

/-- The stable quadratic precursor used by the rank-two total. -/
private def decoLayerTotalTwoPrecursor :
    MvPolynomial (DecoLayerCoord 1) Real :=
  MvPolynomial.X none *
    (MvPolynomial.X none +
      MvPolynomial.C 2 * MvPolynomial.X (some 0))

/-- The nonnegative derivative direction for the rank-two precursor. -/
private def decoLayerTotalTwoWeight : DecoLayerCoord 1 → Real
  | none => 1 / 2
  | some _ => 1

/-- Relabel the precursor variable as `u₂` in the rank-two coordinates. -/
private def decoLayerTotalTwoRename : DecoLayerCoord 1 → DecoLayerCoord 2
  | none => none
  | some _ => some 1

/-- The rank-two directional-derivative pencil before multiplying by `s`. -/
private def decoLayerTotalTwoPencil :
    MvPolynomial (DecoLayerCoord 2) Real :=
  MvPolynomial.rename decoLayerTotalTwoRename decoLayerTotalTwoPrecursor +
    MvPolynomial.X (some 0) *
      MvPolynomial.rename decoLayerTotalTwoRename
        (directionalPDeriv decoLayerTotalTwoWeight
          decoLayerTotalTwoPrecursor)

/-- The quadratic precursor is multivariate real stable. -/
private theorem decoLayerTotalTwoPrecursor_mvRealStable :
    MvRealStable decoLayerTotalTwoPrecursor := by
  apply (MvRealStable.X none).mul
  simpa using
    (MvRealStable.C_mul_X_add_C_mul_X
      (none : DecoLayerCoord 1) (some 0) (a := 1) (b := 2)
        zero_le_one (by norm_num) (Or.inl zero_lt_one))

/-- The rank-two pencil is multivariate real stable. -/
private theorem decoLayerTotalTwoPencil_mvRealStable :
    MvRealStable decoLayerTotalTwoPencil := by
  exact decoLayerTotalTwoPrecursor_mvRealStable.directionalPDeriv_pencil_rename
    decoLayerTotalTwoWeight (by
      intro i
      cases i with
      | none => norm_num [decoLayerTotalTwoWeight]
      | some i => norm_num [decoLayerTotalTwoWeight])
    decoLayerTotalTwoRename (some 0)

/-- The two rank-two recurrence branches combine into the stable pencil. -/
private theorem decoLayerTotal_two_eq_pencil :
    decoLayerTotal 2 =
      MvPolynomial.X none * decoLayerTotalTwoPencil := by
  have hdefault : (default : DecoLayerCoord 0) = none := rfl
  have hhalf :
      (MvPolynomial.C (1 / 2 : Real) :
          MvPolynomial (DecoLayerCoord 2) Real) * 2 = 1 := by
    rw [← map_ofNat (MvPolynomial.C : Real →+*
      MvPolynomial (DecoLayerCoord 2) Real) 2, ← map_mul]
    norm_num
  have hhalf_mul (P : MvPolynomial (DecoLayerCoord 2) Real) :
      P * MvPolynomial.C (1 / 2 : Real) * 2 = P := by
    calc
      P * MvPolynomial.C (1 / 2 : Real) * 2 =
          P * (MvPolynomial.C (1 / 2 : Real) * 2) := by ring
      _ = P := by rw [hhalf, mul_one]
  have htwo_half :
      (MvPolynomial.C (2 : Real) :
          MvPolynomial (DecoLayerCoord 2) Real) *
        MvPolynomial.C (1 / 2 : Real) = 1 := by
    rw [← map_mul]
    norm_num
  have htwo_half_mul (P : MvPolynomial (DecoLayerCoord 2) Real) :
      P * MvPolynomial.C (2 : Real) *
        MvPolynomial.C (1 / 2 : Real) = P := by
    calc
      P * MvPolynomial.C (2 : Real) * MvPolynomial.C (1 / 2 : Real) =
          P * (MvPolynomial.C (2 : Real) *
            MvPolynomial.C (1 / 2 : Real)) := by ring
      _ = P := by rw [htwo_half, mul_one]
  rw [decoLayerTotal_recurrence 0, decoLayerTotal_one,
    decoLayerTotal_zero]
  simp [decoNormalLayerStep, decoExceptionalLayerStep, decoNormalRename,
    decoExceptionalRename,
    decoLayerTotalTwoPencil, decoLayerTotalTwoPrecursor,
      directionalPDeriv, decoLayerTotalTwoWeight,
        decoLayerTotalTwoRename, hdefault]
  ring_nf
  rw [htwo_half_mul, hhalf_mul]
  rw [map_ofNat (MvPolynomial.C : Real →+*
    MvPolynomial (DecoLayerCoord 2) Real) 2]
  ring

/-- The rank-two recurrence-defined layer total is multivariate real stable.
The two recurrence branches combine into a single nonnegative
directional-derivative pencil over `s * (s + 2 * u₂)`. -/
theorem decoLayerTotal_two_mvRealStable :
    MvRealStable
      (decoLayerTotal 2 : MvPolynomial (DecoLayerCoord 2) Real) := by
  rw [decoLayerTotal_two_eq_pencil]
  exact (MvRealStable.X none).mul
    decoLayerTotalTwoPencil_mvRealStable

end

end RealRooted.Applications.OEIS
