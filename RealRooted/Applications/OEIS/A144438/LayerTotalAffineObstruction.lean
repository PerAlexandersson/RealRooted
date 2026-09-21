import RealRooted.Applications.OEIS.A144438.LayerTotalAffineStability
import RealRooted.Applications.OEIS.A144438.LayerTotalRankThree

/-!
# Obstruction to separate exceptional-Wronskian positivity

The exceptional cross term in the affine recurrence is not nonnegative by
itself, even in the step producing the stable rank-four total. Consequently a
valid all-rank invariant must retain quantitative compensation from the normal
Wronskian rather than prove the two summands independently nonnegative.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- At the first rank-four step, the exceptional cross Wronskian is negative
at coordinate `2` when `x₄ = -1` and all other coordinates vanish. -/
theorem eval_coordinateWronskian_affineSlope_exceptionalBase_two_rank_two :
    MvPolynomial.eval (fun i : Nat => if i = 4 then -1 else 0)
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope 2)
        (decoBottomTotalAffineExceptionalBase 2) 2) = -5 := by
  rw [coordinateWronskian_affineSlope_exceptionalBase_two]
  unfold decoBottomTotalAffineExceptionalCore decoBottomTotalAffineSlope
  rw [decoBottomTotal_three]
  norm_num [decoNormalBottomCore, decoBottomTotal,
    decoNormalBottomStep, decoExceptionalBottomStep,
    Fin.sum_univ_succ, MvPolynomial.pderiv_mul, Pi.single_apply]
  simp [MvPolynomial.eval_rename]
  norm_num

/-- Separate nonnegativity of the exceptional cross term is false already for
the recurrence step producing rank four. -/
theorem not_exceptionalCrossWronskian_nonnegative_rank_two :
    ¬ ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope 2)
        (decoBottomTotalAffineExceptionalBase 2) i) := by
  intro h
  have hbad := h 2 (fun i : Nat => if i = 4 then -1 else 0)
  rw [eval_coordinateWronskian_affineSlope_exceptionalBase_two_rank_two] at hbad
  norm_num at hbad

end

end RealRooted.Applications.OEIS
