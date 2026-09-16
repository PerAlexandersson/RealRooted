import RealRooted.Applications.OEIS.A144438.LayerTotalCompanionDataRecurrence
import RealRooted.Applications.OEIS.A144438.LayerTotalRankThree
import RealRooted.Applications.OEIS.A144438.LayerTotalStabilityReduction

/-!
# Rank-four stability of the Deco layer total

The recurrence-defined ordinary-coordinate total at rank four is Rayleigh.
Its six distinct-coordinate Rayleigh differences are bivariate quadratics.
Three exact positive-quartic certificates control all their discriminants.
The same rank-four data also makes the three affine discriminants in the
rank-two companion/successor-slope interface explicitly nonpositive.
-/

namespace RealRooted.Applications.OEIS

open MvPolynomial

noncomputable section

local notation "X" => _root_.MvPolynomial.X

/-- The explicit ordinary-coordinate layer total at rank four. -/
theorem decoBottomTotal_four :
    decoBottomTotal 4 =
      1 + 18 * X 1 + 9 * X 2 + 4 * X 3 + 2 * X 4 +
        36 * X 1 * X 2 + 21 * X 1 * X 3 + 13 * X 1 * X 4 +
        10 * X 2 * X 3 + 7 * X 2 * X 4 + 2 * X 3 * X 4 +
        15 * X 1 * X 2 * X 3 + 11 * X 1 * X 2 * X 4 +
        5 * X 1 * X 3 * X 4 + 2 * X 2 * X 3 * X 4 +
        X 1 * X 2 * X 3 * X 4 := by
  norm_num [decoBottomTotal, decoNormalBottomStep, decoNormalBottomCore,
    decoExceptionalBottomStep, decoLayerBottomEmbedding, Fin.sum_univ_succ,
    map_ofNat, MvPolynomial.pderiv_C, MvPolynomial.pderiv_one,
    MvPolynomial.pderiv_ofNat, MvPolynomial.pderiv_mul]
  ring

theorem decoBottomTotal_four_rayleighDifference_one_two :
    MvPolynomial.rayleighDifference (decoBottomTotal 4) 1 2 =
      8 * X 3 ^ 2 * X 4 ^ 2 + 58 * X 3 ^ 2 * X 4 + 150 * X 3 ^ 2 +
        37 * X 3 * X 4 ^ 2 + 211 * X 3 * X 4 + 210 * X 3 +
        69 * X 4 ^ 2 + 160 * X 4 + 126 := by
  rw [decoBottomTotal_four]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

theorem decoBottomTotal_four_rayleighDifference_one_three :
    MvPolynomial.rayleighDifference (decoBottomTotal 4) 1 3 =
      15 * X 2 ^ 2 * X 4 ^ 2 + 68 * X 2 ^ 2 * X 4 + 225 * X 2 ^ 2 +
        11 * X 2 * X 4 ^ 2 + 59 * X 2 * X 4 + 120 * X 2 +
        16 * X 4 ^ 2 + 41 * X 4 + 51 := by
  rw [decoBottomTotal_four]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

theorem decoBottomTotal_four_rayleighDifference_one_four :
    MvPolynomial.rayleighDifference (decoBottomTotal 4) 1 4 =
      20 * X 2 ^ 2 * X 3 ^ 2 + 58 * X 2 ^ 2 * X 3 + 153 * X 2 ^ 2 +
        18 * X 2 * X 3 ^ 2 + 65 * X 2 * X 3 + 70 * X 2 +
        22 * X 3 ^ 2 + 21 * X 3 + 23 := by
  rw [decoBottomTotal_four]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

theorem decoBottomTotal_four_rayleighDifference_two_three :
    MvPolynomial.rayleighDifference (decoBottomTotal 4) 2 3 =
      42 * X 1 ^ 2 * X 4 ^ 2 + 198 * X 1 ^ 2 * X 4 + 486 * X 1 ^ 2 +
        29 * X 1 * X 4 ^ 2 + 111 * X 1 * X 4 + 138 * X 1 +
        10 * X 4 ^ 2 + 24 * X 4 + 26 := by
  rw [decoBottomTotal_four]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

theorem decoBottomTotal_four_rayleighDifference_two_four :
    MvPolynomial.rayleighDifference (decoBottomTotal 4) 2 4 =
      54 * X 1 ^ 2 * X 3 ^ 2 + 126 * X 1 ^ 2 * X 3 + 270 * X 1 ^ 2 +
        34 * X 1 * X 3 ^ 2 + 49 * X 1 * X 3 + 52 * X 1 +
        12 * X 3 ^ 2 + 8 * X 3 + 11 := by
  rw [decoBottomTotal_four]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

theorem decoBottomTotal_four_rayleighDifference_three_four :
    MvPolynomial.rayleighDifference (decoBottomTotal 4) 3 4 =
      129 * X 1 ^ 2 * X 2 ^ 2 + 228 * X 1 ^ 2 * X 2 + 183 * X 1 ^ 2 +
        134 * X 1 * X 2 ^ 2 + 197 * X 1 * X 2 + 53 * X 1 +
        52 * X 2 ^ 2 + 28 * X 2 + 6 := by
  rw [decoBottomTotal_four]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

private theorem quartic_one_pos (x : ℝ) :
    0 < 839 * x ^ 4 + 5514 * x ^ 3 + 22491 * x ^ 2 + 36612 * x + 31500 := by
  have hprod : 0 < (839 * 11268900 : ℝ) *
      (839 * x ^ 4 + 5514 * x ^ 3 + 22491 * x ^ 2 + 36612 * x + 31500) := by
    rw [show (839 * 11268900 : ℝ) *
        (839 * x ^ 4 + 5514 * x ^ 3 + 22491 * x ^ 2 + 36612 * x + 31500) =
      11268900 * (839 * x ^ 2 + 2757 * x) ^ 2 +
        (11268900 * x + 15358734) ^ 2 + 839 * 73813365396 by ring]
    positivity
  nlinarith

private theorem quartic_two_pos (x : ℝ) :
    0 < 1436 * x ^ 4 + 4444 * x ^ 3 + 13431 * x ^ 2 + 9088 * x + 9176 := by
  have hprod : 0 < (1436 * 14349632 : ℝ) *
      (1436 * x ^ 4 + 4444 * x ^ 3 + 13431 * x ^ 2 + 9088 * x + 9176) := by
    rw [show (1436 * 14349632 : ℝ) *
        (1436 * x ^ 4 + 4444 * x ^ 3 + 13431 * x ^ 2 + 9088 * x + 9176) =
      14349632 * (1436 * x ^ 2 + 2222 * x) ^ 2 +
        (14349632 * x + 6525184) ^ 2 + 1436 * 102021787136 by ring]
    positivity
  nlinarith

private theorem quartic_three_pos (x : ℝ) :
    0 < 8876 * x ^ 4 + 9076 * x ^ 3 + 13683 * x ^ 2 + 5086 * x + 1583 := by
  have hprod : 0 < (8876 * 100856864 : ℝ) *
      (8876 * x ^ 4 + 9076 * x ^ 3 + 13683 * x ^ 2 + 5086 * x + 1583) := by
    rw [show (8876 * 100856864 : ℝ) *
        (8876 * x ^ 4 + 9076 * x ^ 3 + 13683 * x ^ 2 + 5086 * x + 1583) =
      100856864 * (8876 * x ^ 2 + 4538 * x) ^ 2 +
        (100856864 * x + 22571668) ^ 2 + 8876 * 102256663988 by ring]
    positivity
  nlinarith

private theorem quadratic_one_pos (x : ℝ) : 0 < 8 * x ^ 2 + 58 * x + 150 := by
  simpa [pow_two] using quadratic_pos_of_pos_of_discrim_neg
    (a := (8 : ℝ)) (b := 58) (c := 150) (by norm_num)
      (by norm_num [discrim]) x

private theorem quadratic_two_pos (x : ℝ) : 0 < 15 * x ^ 2 + 68 * x + 225 := by
  simpa [pow_two] using quadratic_pos_of_pos_of_discrim_neg
    (a := (15 : ℝ)) (b := 68) (c := 225) (by norm_num)
      (by norm_num [discrim]) x

private theorem quadratic_three_pos (x : ℝ) : 0 < 42 * x ^ 2 + 198 * x + 486 := by
  simpa [pow_two] using quadratic_pos_of_pos_of_discrim_neg
    (a := (42 : ℝ)) (b := 198) (c := 486) (by norm_num)
      (by norm_num [discrim]) x

private theorem quadratic_four_pos (x : ℝ) : 0 < 20 * x ^ 2 + 58 * x + 153 := by
  simpa [pow_two] using quadratic_pos_of_pos_of_discrim_neg
    (a := (20 : ℝ)) (b := 58) (c := 153) (by norm_num)
      (by norm_num [discrim]) x

private theorem quadratic_five_pos (x : ℝ) : 0 < 54 * x ^ 2 + 126 * x + 270 := by
  simpa [pow_two] using quadratic_pos_of_pos_of_discrim_neg
    (a := (54 : ℝ)) (b := 126) (c := 270) (by norm_num)
      (by norm_num [discrim]) x

private theorem quadratic_six_pos (x : ℝ) : 0 < 129 * x ^ 2 + 228 * x + 183 := by
  simpa [pow_two] using quadratic_pos_of_pos_of_discrim_neg
    (a := (129 : ℝ)) (b := 228) (c := 183) (by norm_num)
      (by norm_num [discrim]) x

private theorem rayleighDifference_one_two_nonneg (x : Nat → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference (decoBottomTotal 4) 1 2) := by
  rw [decoBottomTotal_four_rayleighDifference_one_two]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  have hdisc : discrim
      (8 * x 4 ^ 2 + 58 * x 4 + 150)
      (37 * x 4 ^ 2 + 211 * x 4 + 210)
      (69 * x 4 ^ 2 + 160 * x 4 + 126) ≤ 0 := by
    rw [discrim]
    nlinarith [quartic_one_pos (x 4)]
  have hnonneg := quadratic_nonneg_of_pos_of_discrim_nonpos
    (quadratic_one_pos (x 4)) hdisc (x 3)
  nlinarith

private theorem rayleighDifference_one_three_nonneg (x : Nat → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference (decoBottomTotal 4) 1 3) := by
  rw [decoBottomTotal_four_rayleighDifference_one_three]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  have hdisc : discrim
      (15 * x 4 ^ 2 + 68 * x 4 + 225)
      (11 * x 4 ^ 2 + 59 * x 4 + 120)
      (16 * x 4 ^ 2 + 41 * x 4 + 51) ≤ 0 := by
    rw [discrim]
    nlinarith [quartic_one_pos (x 4)]
  have hnonneg := quadratic_nonneg_of_pos_of_discrim_nonpos
    (quadratic_two_pos (x 4)) hdisc (x 2)
  nlinarith

private theorem rayleighDifference_one_four_nonneg (x : Nat → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference (decoBottomTotal 4) 1 4) := by
  rw [decoBottomTotal_four_rayleighDifference_one_four]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  have hdisc : discrim
      (20 * x 3 ^ 2 + 58 * x 3 + 153)
      (18 * x 3 ^ 2 + 65 * x 3 + 70)
      (22 * x 3 ^ 2 + 21 * x 3 + 23) ≤ 0 := by
    rw [discrim]
    nlinarith [quartic_two_pos (x 3)]
  have hnonneg := quadratic_nonneg_of_pos_of_discrim_nonpos
    (quadratic_four_pos (x 3)) hdisc (x 2)
  nlinarith

private theorem rayleighDifference_two_three_nonneg (x : Nat → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference (decoBottomTotal 4) 2 3) := by
  rw [decoBottomTotal_four_rayleighDifference_two_three]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  have hdisc : discrim
      (42 * x 4 ^ 2 + 198 * x 4 + 486)
      (29 * x 4 ^ 2 + 111 * x 4 + 138)
      (10 * x 4 ^ 2 + 24 * x 4 + 26) ≤ 0 := by
    rw [discrim]
    nlinarith [quartic_one_pos (x 4)]
  have hnonneg := quadratic_nonneg_of_pos_of_discrim_nonpos
    (quadratic_three_pos (x 4)) hdisc (x 1)
  nlinarith

private theorem rayleighDifference_two_four_nonneg (x : Nat → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference (decoBottomTotal 4) 2 4) := by
  rw [decoBottomTotal_four_rayleighDifference_two_four]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  have hdisc : discrim
      (54 * x 3 ^ 2 + 126 * x 3 + 270)
      (34 * x 3 ^ 2 + 49 * x 3 + 52)
      (12 * x 3 ^ 2 + 8 * x 3 + 11) ≤ 0 := by
    rw [discrim]
    nlinarith [quartic_two_pos (x 3)]
  have hnonneg := quadratic_nonneg_of_pos_of_discrim_nonpos
    (quadratic_five_pos (x 3)) hdisc (x 1)
  nlinarith

private theorem rayleighDifference_three_four_nonneg (x : Nat → ℝ) :
    0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference (decoBottomTotal 4) 3 4) := by
  rw [decoBottomTotal_four_rayleighDifference_three_four]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  have hdisc : discrim
      (129 * x 2 ^ 2 + 228 * x 2 + 183)
      (134 * x 2 ^ 2 + 197 * x 2 + 53)
      (52 * x 2 ^ 2 + 28 * x 2 + 6) ≤ 0 := by
    rw [discrim]
    nlinarith [quartic_three_pos (x 2)]
  have hnonneg := quadratic_nonneg_of_pos_of_discrim_nonpos
    (quadratic_six_pos (x 2)) hdisc (x 1)
  nlinarith

/-- The recurrence-defined ordinary-coordinate total at rank four is
Rayleigh. -/
theorem decoBottomTotal_four_isRayleigh :
    MvPolynomial.IsRayleigh (decoBottomTotal 4) := by
  apply (decoBottomTotal_isMultiaffine 4).isRayleigh_of_vars_subset
    (Finset.Icc 1 4)
  · exact vars_decoBottomTotal_subset_Icc 4
  · intro i hi j hj hij x
    simp only [Finset.mem_Icc] at hi hj
    obtain ⟨hiLower, hiUpper⟩ := hi
    obtain ⟨hjLower, hjUpper⟩ := hj
    interval_cases i <;> interval_cases j <;> norm_num at hij
    · exact rayleighDifference_one_two_nonneg x
    · exact rayleighDifference_one_three_nonneg x
    · exact rayleighDifference_one_four_nonneg x
    · rw [MvPolynomial.rayleighDifference_comm]
      exact rayleighDifference_one_two_nonneg x
    · exact rayleighDifference_two_three_nonneg x
    · exact rayleighDifference_two_four_nonneg x
    · rw [MvPolynomial.rayleighDifference_comm]
      exact rayleighDifference_one_three_nonneg x
    · rw [MvPolynomial.rayleighDifference_comm]
      exact rayleighDifference_two_three_nonneg x
    · exact rayleighDifference_three_four_nonneg x
    · rw [MvPolynomial.rayleighDifference_comm]
      exact rayleighDifference_one_four_nonneg x
    · rw [MvPolynomial.rayleighDifference_comm]
      exact rayleighDifference_two_four_nonneg x
    · rw [MvPolynomial.rayleighDifference_comm]
      exact rayleighDifference_three_four_nonneg x

/-- The recurrence-defined ordinary-coordinate total at rank four is real
stable. -/
theorem decoBottomTotal_four_mvRealStable :
    MvRealStable (decoBottomTotal 4) :=
  (decoBottomTotal_mvRealStable_iff_isRayleigh 4).mpr
    decoBottomTotal_four_isRayleigh

/-- The homogeneous finite-coordinate layer total at rank four is real
stable. -/
theorem decoLayerTotal_four_mvRealStable :
    MvRealStable (decoLayerTotal 4) :=
  (decoLayerTotal_mvRealStable_iff_bottomTotal 4).mpr
    decoBottomTotal_four_mvRealStable

/-- The explicit rank-four stability certificate, repackaged as the exact
lower two-rank companion data at rank two. -/
theorem decoBottomTotalCompanionRayleighData_two :
    DecoBottomTotalCompanionRayleighData 2 :=
  (decoBottomTotal_add_two_isRayleigh_iff_stable_companionData
    2 decoLayerTotal_three_mvRealStable).mp decoBottomTotal_four_isRayleigh

/-- The explicit rank-two two-rank companion. -/
theorem decoBottomTotalWronskianCompanion_two :
    decoBottomTotalWronskianCompanion 2 =
      1 + 9 * X 1 + 4 * X 2 + 2 * X 3 +
        10 * X 1 * X 2 + 7 * X 1 * X 3 + 2 * X 2 * X 3 +
        2 * X 1 * X 2 * X 3 := by
  rw [decoBottomTotalWronskianCompanion, decoBottomTotal_three,
    decoBottomTotal_two]
  norm_num [MvPolynomial.rename_X, map_ofNat]
  ring

/-- The explicit successor slope paired with the rank-two companion. -/
theorem decoBottomTotalCompanionSlope_two :
    decoBottomTotalCompanionSlope 2 =
      19 + 44 * X 1 + 25 * X 2 + 15 * X 3 +
        22 * X 1 * X 2 + 16 * X 1 * X 3 + 7 * X 2 * X 3 +
        2 * X 1 * X 2 * X 3 := by
  norm_num [decoBottomTotalCompanionSlope,
    decoBottomTotalCompanionCore, decoNormalBottomCore,
    decoBottomTotal_three, Fin.sum_univ_succ, map_ofNat,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_one,
    MvPolynomial.pderiv_ofNat, MvPolynomial.pderiv_mul]
  ring

/-- The first rank-two companion/successor-slope affine discriminant is the
negative of an explicit positive quartic. -/
theorem
    affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_one_two :
    MvPolynomial.affineRayleighDiscriminant
      (decoBottomTotalWronskianCompanion 2)
      (decoBottomTotalCompanionSlope 2) 1 2 =
        -(35207 + 41864 * X 3 + 26346 * X 3 ^ 2 +
          6808 * X 3 ^ 3 + 1071 * X 3 ^ 4) := by
  rw [decoBottomTotalWronskianCompanion_two,
    decoBottomTotalCompanionSlope_two]
  norm_num [MvPolynomial.affineRayleighDiscriminant,
    MvPolynomial.mixedRayleighDifference,
    MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  simp only [map_ofNat]
  ring

/-- The second rank-two companion/successor-slope affine discriminant is the
negative of an explicit positive quartic. -/
theorem
    affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_one_three :
    MvPolynomial.affineRayleighDiscriminant
      (decoBottomTotalWronskianCompanion 2)
      (decoBottomTotalCompanionSlope 2) 1 3 =
        -(10188 + 10424 * X 2 + 15420 * X 2 ^ 2 +
          5536 * X 2 ^ 3 + 1856 * X 2 ^ 4) := by
  rw [decoBottomTotalWronskianCompanion_two,
    decoBottomTotalCompanionSlope_two]
  norm_num [MvPolynomial.affineRayleighDiscriminant,
    MvPolynomial.mixedRayleighDifference,
    MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  simp only [map_ofNat]
  ring

/-- The third rank-two companion/successor-slope affine discriminant is the
negative of an explicit positive quartic. -/
theorem
    affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_two_three :
    MvPolynomial.affineRayleighDiscriminant
      (decoBottomTotalWronskianCompanion 2)
      (decoBottomTotalCompanionSlope 2) 2 3 =
        -(1583 + 4860 * X 1 + 14076 * X 1 ^ 2 +
          8768 * X 1 ^ 3 + 11648 * X 1 ^ 4) := by
  rw [decoBottomTotalWronskianCompanion_two,
    decoBottomTotalCompanionSlope_two]
  norm_num [MvPolynomial.affineRayleighDiscriminant,
    MvPolynomial.mixedRayleighDifference,
    MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  simp only [map_ofNat]
  ring

private theorem companion_slope_quartic_one_pos (x : ℝ) :
    0 < 1071 * x ^ 4 + 6808 * x ^ 3 + 26346 * x ^ 2 +
      41864 * x + 35207 := by
  have hprod : 0 < (1071 * 16629350 : ℝ) *
      (1071 * x ^ 4 + 6808 * x ^ 3 + 26346 * x ^ 2 +
        41864 * x + 35207) := by
    rw [show (1071 * 16629350 : ℝ) *
          (1071 * x ^ 4 + 6808 * x ^ 3 + 26346 * x ^ 2 +
            41864 * x + 35207) =
        16629350 * (1071 * x ^ 2 + 3404 * x) ^ 2 +
          (16629350 * x + 22418172) ^ 2 +
          1071 * 116212349146 by ring]
    positivity
  nlinarith

private theorem companion_slope_quartic_two_pos (x : ℝ) :
    0 < 1856 * x ^ 4 + 5536 * x ^ 3 + 15420 * x ^ 2 +
      10424 * x + 10188 := by
  have hprod : 0 < (1856 * 20957696 : ℝ) *
      (1856 * x ^ 4 + 5536 * x ^ 3 + 15420 * x ^ 2 +
        10424 * x + 10188) := by
    rw [show (1856 * 20957696 : ℝ) *
          (1856 * x ^ 4 + 5536 * x ^ 3 + 15420 * x ^ 2 +
            10424 * x + 10188) =
        20957696 * (1856 * x ^ 2 + 2768 * x) ^ 2 +
          (20957696 * x + 9673472) ^ 2 +
          1856 * 163098870784 by ring]
    positivity
  nlinarith

private theorem companion_slope_quartic_three_pos (x : ℝ) :
    0 < 11648 * x ^ 4 + 8768 * x ^ 3 + 14076 * x ^ 2 +
      4860 * x + 1583 := by
  have hprod : 0 < (11648 * 144737792 : ℝ) *
      (11648 * x ^ 4 + 8768 * x ^ 3 + 14076 * x ^ 2 +
        4860 * x + 1583) := by
    rw [show (11648 * 144737792 : ℝ) *
          (11648 * x ^ 4 + 8768 * x ^ 3 + 14076 * x ^ 2 +
            4860 * x + 1583) =
        144737792 * (11648 * x ^ 2 + 4384 * x) ^ 2 +
          (144737792 * x + 28304640) ^ 2 +
          11648 * 160339649536 by ring]
    positivity
  nlinarith

/-- Every affine Rayleigh discriminant between the rank-two companion and
its successor slope is nonpositive.  The finite-support theorem reduces the
proof to the three explicit unordered coordinate pairs above. -/
theorem
    eval_affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_nonpos
    (i j : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion 2)
          (decoBottomTotalCompanionSlope 2) i j) ≤ 0 := by
  apply eval_affineRayleighDiscriminant_companion_slope_nonpos_of_Icc 2
  intro a ha b hb hab y
  simp only [Finset.mem_Icc, Nat.reduceAdd] at ha hb
  rcases ha with ⟨haLower, haUpper⟩
  rcases hb with ⟨hbLower, hbUpper⟩
  interval_cases a <;> interval_cases b <;> norm_num at hab
  · rw [affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_one_two]
    simp only [map_neg, map_add, map_mul, map_pow, map_ofNat,
      MvPolynomial.eval_X]
    nlinarith [companion_slope_quartic_one_pos (y 3)]
  · rw [affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_one_three]
    simp only [map_neg, map_add, map_mul, map_pow, map_ofNat,
      MvPolynomial.eval_X]
    nlinarith [companion_slope_quartic_two_pos (y 2)]
  · rw [affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_two_three]
    simp only [map_neg, map_add, map_mul, map_pow, map_ofNat,
      MvPolynomial.eval_X]
    nlinarith [companion_slope_quartic_three_pos (y 1)]

/-- After discharging the current companion/slope discriminants, the exact
rank-two successor criterion consists only of the finite zero-locus package,
the finite endpoint package, and the six supported next companion/core
discriminants. -/
theorem decoBottomTotalCompanionRayleighData_three_iff_finite_core :
    DecoBottomTotalCompanionRayleighData 3 ↔
      (∀ i : Fin 3, ∀ x,
        MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCoreCross
              2 i) = 0 →
          0 ≤ MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowDiscriminantCompanionCross
              2 i)) ∧
      ((∀ x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore 3)
          (decoBottomTotalWronskianCompanion 3) 1)) ∧
        DecoBottomTotalCompanionSuccessorCoreEndpointData 2) ∧
      ∀ i ∈ Finset.Icc 1 4, ∀ j ∈ Finset.Icc 1 4, i < j → ∀ x,
        MvPolynomial.eval x
          (MvPolynomial.affineRayleighDiscriminant
            (decoBottomTotalWronskianCompanion 3)
            (decoBottomTotalCompanionCore 3) i j) ≤ 0 := by
  rw [decoBottomTotalCompanionRayleighData_succ_iff_finite
    2 decoLayerTotal_three_mvRealStable
      decoBottomTotalCompanionRayleighData_two]
  simp only [
    eval_affineRayleighDiscriminant_decoBottomTotalWronskianCompanion_slope_two_nonpos,
    implies_true, true_and]

end

end RealRooted.Applications.OEIS
