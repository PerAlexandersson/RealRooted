import RealRooted.Applications.OEIS.A144438.LayerTotalStabilityReduction
import RealRooted.MultivariateStability.Rayleigh

/-!
# Rank-three stability of the Deco layer total

The recurrence-defined ordinary-coordinate total at rank three has an explicit
multiaffine form.  Treating its first two variables as a bivariate polynomial
reduces stability to positivity of a solved quotient.  The two real quadratic
forms in the quotient numerator have discriminant `-359`, so they are strictly
positive.
-/

namespace RealRooted.Applications.OEIS

open MvPolynomial

noncomputable section

/-- The explicit ordinary-coordinate layer total at rank three. -/
theorem decoBottomTotal_three :
    decoBottomTotal 3 =
      1 + 8 * MvPolynomial.X 1 + 4 * MvPolynomial.X 2 +
        2 * MvPolynomial.X 3 +
        7 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        5 * MvPolynomial.X 1 * MvPolynomial.X 3 +
        2 * MvPolynomial.X 2 * MvPolynomial.X 3 +
        MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  norm_num [decoBottomTotal, decoNormalBottomStep, decoNormalBottomCore,
    decoExceptionalBottomStep, decoLayerBottomEmbedding, Fin.sum_univ_succ,
    map_ofNat, MvPolynomial.pderiv_C, MvPolynomial.pderiv_one,
    MvPolynomial.pderiv_ofNat]
  ring

/-- The rank-three Rayleigh difference in the first two coordinates. -/
theorem decoBottomTotal_three_rayleighDifference_one_two :
    MvPolynomial.rayleighDifference (decoBottomTotal 3) 1 2 =
      25 + 21 * MvPolynomial.X 3 + 8 * MvPolynomial.X 3 ^ 2 := by
  rw [decoBottomTotal_three]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

/-- The rank-three Rayleigh difference in the first and third coordinates. -/
theorem decoBottomTotal_three_rayleighDifference_one_three :
    MvPolynomial.rayleighDifference (decoBottomTotal 3) 1 3 =
      11 + 9 * MvPolynomial.X 2 + 10 * MvPolynomial.X 2 ^ 2 := by
  rw [decoBottomTotal_three]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

/-- The rank-three Rayleigh difference in the last two coordinates. -/
theorem decoBottomTotal_three_rayleighDifference_two_three :
    MvPolynomial.rayleighDifference (decoBottomTotal 3) 2 3 =
      6 + 17 * MvPolynomial.X 1 + 27 * MvPolynomial.X 1 ^ 2 := by
  rw [decoBottomTotal_three]
  norm_num [MvPolynomial.rayleighDifference, MvPolynomial.pderiv_mul]
  ring

/-- The recurrence-defined ordinary-coordinate total at rank three is real
stable. -/
theorem decoBottomTotal_three_mvRealStable :
    MvRealStable (decoBottomTotal 3) := by
  rw [decoBottomTotal_three]
  unfold MvRealStable complexifyMv MvUpperHalfPlaneStable MvStableIn
  intro z hz
  have hz3 : 0 < (z 3).im := hz 3
  simp only [map_add, map_one, map_mul, map_ofNat, MvPolynomial.map_X,
    MvPolynomial.eval_X]
  let a : ℂ := 1 + 2 * z 3
  let b : ℂ := 8 + 5 * z 3
  let c : ℂ := 4 + 2 * z 3
  let d : ℂ := 7 + z 3
  have hd : d ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [d] at him
    simp only [Complex.add_im, Complex.im_ofNat, zero_add,
      Complex.zero_im] at him
    linarith
  have hcd : 0 < (c / d).im := by
    rw [Complex.div_im, ← sub_div]
    apply div_pos
    · dsimp only [c, d]
      simp only [Complex.add_re, Complex.re_ofNat, Complex.add_im,
        Complex.im_ofNat, zero_add, Complex.mul_re, Complex.mul_im]
      ring_nf
      nlinarith
    · exact Complex.normSq_pos.mpr hd
  have hq : ∀ x : ℂ, 0 < x.im →
      0 < ((a + b * x) / (c + d * x)).im := by
    intro x hx
    have hden : c + d * x ≠ 0 :=
      RealRooted.add_mul_ne_zero_of_im_div_pos c d x hcd (le_of_lt hx)
    rw [Complex.div_im, ← sub_div]
    apply div_pos
    · dsimp only [a, b, c, d]
      simp only [Complex.add_re, Complex.re_ofNat, Complex.add_im,
        Complex.im_ofNat, Complex.one_re, Complex.one_im, zero_add,
        Complex.mul_re, Complex.mul_im]
      ring_nf
      have hzquad : 0 <
          8 * (z 3).re ^ 2 + 21 * (z 3).re +
            8 * (z 3).im ^ 2 + 25 := by
        nlinarith [sq_nonneg (16 * (z 3).re + 21),
          sq_nonneg (z 3).im]
      have hxquad : 0 <
          27 * x.re ^ 2 + 17 * x.re + 27 * x.im ^ 2 + 6 := by
        nlinarith [sq_nonneg (54 * x.re + 17), sq_nonneg x.im]
      have hv := mul_pos hx hzquad
      have ht := mul_pos hz3 hxquad
      nlinarith
    · exact Complex.normSq_pos.mpr hden
  have htarget : a + b * z 1 + c * z 2 + d * z 1 * z 2 ≠ 0 := by
    apply RealRooted.bivariate_ne_zero_of_im_div_pos_of_quotient_im_pos
      a b c d (z 1) (z 2) hcd (le_of_lt (hz 1))
    · exact hq (z 1) (hz 1)
    · exact hz 2
  dsimp only [a, b, c, d] at htarget
  intro hzero
  apply htarget
  linear_combination hzero

/-- The homogeneous finite-coordinate layer total at rank three is real
stable. -/
theorem decoLayerTotal_three_mvRealStable :
    MvRealStable (decoLayerTotal 3) :=
  (decoLayerTotal_mvRealStable_iff_bottomTotal 3).mpr
    decoBottomTotal_three_mvRealStable

end

end RealRooted.Applications.OEIS
