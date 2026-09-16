import RealRooted.Applications.OEIS.A144438.LayerTotalAffineRecurrence

/-!
# Two-rank Wronskian recurrence for the Deco layer total

The affine base in the next Deco recurrence is a shifted copy of one
two-rank companion polynomial.  Consequently every positive-coordinate
Wronskian required by the affine Rayleigh criterion is the corresponding
shifted Wronskian of the normal core against that companion.  This packages
the normal/exceptional compensation as one invariant rather than imposing
separate signs on its summands.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The two-rank companion whose shift is the affine base in the next Deco
recurrence. -/
def decoBottomTotalWronskianCompanion (n : Nat) : MvPolynomial Nat Real :=
  decoBottomTotal (n + 1) + MvPolynomial.X 1 *
    MvPolynomial.rename (fun i : Nat => i + 1) (decoBottomTotal n)

/-- The initial two-rank companion. -/
@[simp] theorem decoBottomTotalWronskianCompanion_zero :
    decoBottomTotalWronskianCompanion 0 = 1 + 2 * MvPolynomial.X 1 := by
  simp [decoBottomTotalWronskianCompanion]
  ring

/-- The companion has an exact one-step recurrence in the two preceding
layer totals.  Its normal core differs from the ordinary recurrence core by
the additional copy of the latest total. -/
theorem decoBottomTotalWronskianCompanion_succ (n : Nat) :
    decoBottomTotalWronskianCompanion (n + 1) =
      MvPolynomial.rename (fun i : Nat => i + 1)
          (decoBottomTotal (n + 1)) +
        MvPolynomial.X 1 * MvPolynomial.rename (fun i : Nat => i + 1)
          (decoBottomTotal (n + 1) +
            decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))) +
        MvPolynomial.X 2 * MvPolynomial.rename (fun i : Nat => i + 2)
          (decoBottomTotal n) := by
  unfold decoBottomTotalWronskianCompanion
  rw [decoBottomTotal_recurrence]
  simp only [decoNormalBottomStep, decoExceptionalBottomStep, map_add]
  ring

/-- The affine base is exactly the positive-coordinate shift of the two-rank
Wronskian companion. -/
theorem decoBottomTotalAffineBase_eq_rename_wronskianCompanion (n : Nat) :
    decoBottomTotalAffineBase n =
      MvPolynomial.rename (fun i : Nat => i + 1)
        (decoBottomTotalWronskianCompanion n) := by
  simp only [decoBottomTotalAffineBase,
    decoBottomTotalAffineNormalBase,
    decoBottomTotalAffineExceptionalBase,
    decoBottomTotalAffineExceptionalCore,
    decoBottomTotalWronskianCompanion, map_add, map_mul,
    MvPolynomial.rename_X, MvPolynomial.rename_rename]
  congr 2

/-- Rayleighness of the affine base is exactly Rayleighness of its unshifted
two-rank companion. -/
theorem decoBottomTotalAffineBase_isRayleigh_iff_companion (n : Nat) :
    MvPolynomial.IsRayleigh (decoBottomTotalAffineBase n) ↔
      MvPolynomial.IsRayleigh (decoBottomTotalWronskianCompanion n) := by
  rw [decoBottomTotalAffineBase_eq_rename_wronskianCompanion]
  exact MvPolynomial.isRayleigh_rename_iff (by intro i j hij; lia)

/-- Every positive-coordinate affine-base Wronskian is the shifted
Wronskian of the preceding normal core against the two-rank companion. -/
theorem coordinateWronskian_affineSlope_base_succ (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n) (decoBottomTotalAffineBase n) (i + 1) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
          (decoBottomTotalWronskianCompanion n) i) := by
  rw [decoBottomTotalAffineBase_eq_rename_wronskianCompanion]
  unfold decoBottomTotalAffineSlope
  exact MvPolynomial.coordinateWronskian_rename (fun j : Nat => j + 1)
    (by intro j k h; lia) _ _ i

/-- Evaluation of a positive-coordinate affine-base Wronskian is evaluation
of the lower two-rank Wronskian after shifting the assignment. -/
theorem eval_coordinateWronskian_affineSlope_base_succ
    (n i : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalAffineSlope n) (decoBottomTotalAffineBase n)
          (i + 1)) =
      MvPolynomial.eval (fun j => x (j + 1))
        (MvPolynomial.coordinateWronskian
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
          (decoBottomTotalWronskianCompanion n) i) := by
  rw [coordinateWronskian_affineSlope_base_succ]
  rw [MvPolynomial.eval_rename]
  change MvPolynomial.eval (fun j => x (j + 1)) _ = _
  rfl

/-- Nonnegativity of all affine-base Wronskians is exactly nonnegativity of
the lower two-rank companion Wronskians. -/
theorem eval_coordinateWronskian_affineSlope_base_nonneg_iff_companion
    (n : Nat) :
    (∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n) (decoBottomTotalAffineBase n) i)) ↔
      ∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
          (decoBottomTotalWronskianCompanion n) i) := by
  constructor
  · intro h i x
    let y : Nat → Real := fun k => match k with
      | 0 => 0
      | j + 1 => x j
    have hi := h (i + 1) y
    rw [eval_coordinateWronskian_affineSlope_base_succ] at hi
    simpa [y] using hi
  · intro h i x
    cases i with
    | zero =>
        have hbase : 0 ∉ (decoBottomTotalAffineBase n).vars := by
          intro hzero
          have hbounds := vars_decoBottomTotalAffineBase_subset_Icc n hzero
          rw [Finset.mem_Icc] at hbounds
          lia
        have hslope : 0 ∉ (decoBottomTotalAffineSlope n).vars := by
          intro hzero
          have hbounds := vars_decoBottomTotalAffineSlope_subset_Icc n hzero
          rw [Finset.mem_Icc] at hbounds
          lia
        rw [MvPolynomial.coordinateWronskian,
          MvPolynomial.pderiv_eq_zero_of_notMem_vars hslope,
          MvPolynomial.pderiv_eq_zero_of_notMem_vars hbase]
        simp
    | succ i =>
        rw [eval_coordinateWronskian_affineSlope_base_succ]
        exact h i _

end

end RealRooted.Applications.OEIS
