module

public import RealRooted.Basic.ProperPosition
import RealRooted.Interlacing.Euclid
import RealRooted.MaWang.CriticalSign
import RealRooted.QuadraticRoot

/-!
# Interlacing from a division remainder

For a quadratic `R = a X² + b X + c` with `a > 0` and a cubic written as
`R * (p X + d) + (α X + β)` with `p > 0`, the cubic strictly interlaces `R` when `α < 0` and
`a β² - b α β + c α² < 0`;
the second condition says `R (-β / α) < 0`, so the root of the remainder lies strictly between the
roots of `R` (`strictInterl_quadratic_of_remainder`). The linear analogue needs only `β < 0`
(`strictInterl_linear_of_remainder`). Multiplying both rows by powers of a common real-rooted
factor `q` gives interlacing of `q ^ m * R` and `q ^ (m + 1) * S` from a certificate for `q * S`
(`Interlaces.pow_mul_of_quadratic_remainder`, `Interlaces.pow_mul_of_linear_remainder`): rows of
order-three recurrences with characteristic polynomial `(λ - q)³` have this shape.

Both certificates are derived from `strictInterl_of_eval_mul_derivative_neg`.
-/

public section

open Polynomial

namespace RealRooted

/-- Remainder certificates for an affine perturbation of a linear polynomial. -/
theorem strictInterl_linear_of_remainder {a b p d β : ℝ} (ha : 0 < a)
    (hp : 0 < p) (hβ : β < 0) :
    StrictInterl (C a * X + C b)
      ((C a * X + C b) * (C p * X + C d) + C β) := by
  have hform : (C a * X + C b) * (C p * X + C d) + C β =
      C (a * p) * X ^ 2 + C (a * d + b * p) * X + C (b * d + β) := by
    simp only [C_mul, C_add]; ring
  have hap : a * p ≠ 0 := by positivity
  have hfdeg : (C a * X + C b : ℝ[X]).natDegree = 1 := natDegree_linear ha.ne'
  refine strictInterl_of_eval_mul_derivative_neg
    (Splits.of_natDegree_le_one hfdeg.le) ?_ ?_ (by simp [hfdeg]) ?_ ?_ ?_
  · simpa [HasPosLeadingCoeff, leadingCoeff_linear ha.ne'] using ha
  · rw [HasPosLeadingCoeff, hform, leadingCoeff_quadratic hap]
    exact mul_pos ha hp
  · rw [hform, natDegree_quadratic hap, hfdeg]; norm_num
  · rw [hform, natDegree_quadratic hap, hfdeg]
  · intro r hr
    have : a * r + b = 0 := by simpa using hr
    simp [this]
    nlinarith

/-- Remainder certificates for an affine perturbation of a quadratic polynomial. -/
theorem strictInterl_quadratic_of_remainder {a b c p d α β : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hα : α < 0)
    (hcert : a * β ^ 2 - b * α * β + c * α ^ 2 < 0) :
    StrictInterl (C a * X ^ 2 + C b * X + C c)
      ((C a * X ^ 2 + C b * X + C c) * (C p * X + C d) +
        (C α * X + C β)) := by
  have hform : (C a * X ^ 2 + C b * X + C c) * (C p * X + C d) + (C α * X + C β) =
      C (a * p) * X ^ 3 + C (a * d + b * p) * X ^ 2 + C (b * d + c * p + α) * X
        + C (c * d + β) := by
    simp only [C_mul, C_add]; ring
  have hap : a * p ≠ 0 := by positivity
  have hα2 : 0 < α ^ 2 := by nlinarith
  have hD : 0 < b ^ 2 - 4 * a * c := by
    have hDα : 0 < α ^ 2 * (b ^ 2 - 4 * a * c) := by
      nlinarith [sq_nonneg (2 * a * β - b * α)]
    exact (pos_iff_pos_of_mul_pos hDα).mp hα2
  have hfdeg : (C a * X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 := natDegree_quadratic ha.ne'
  refine strictInterl_of_eval_mul_derivative_neg
    (quadraticPoly_splits_of_discrim_nonneg ha.ne' (by simpa [discrim] using hD.le)) ?_ ?_
    (by simp [hfdeg]) ?_ ?_ ?_
  · simpa [HasPosLeadingCoeff, leadingCoeff_quadratic ha.ne'] using ha
  · rw [HasPosLeadingCoeff, hform, leadingCoeff_cubic hap]
    exact mul_pos ha hp
  · rw [hform, natDegree_cubic hap, hfdeg]; norm_num
  · rw [hform, natDegree_cubic hap, hfdeg]
  · intro r hr
    have hroots := roots_quadratic_posLead ha hD.le
    have hr' : r ∈ (C a * X ^ 2 + C b * X + C c).roots := (mem_roots (by
      intro h0; rw [h0] at hfdeg; simp at hfdeg)).2 hr
    rw [hroots] at hr'
    set s := Real.sqrt (b ^ 2 - 4 * a * c) with hs_def
    have hs : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hD.le
    have hs0 : 0 < s := Real.sqrt_pos.mpr hD
    have hu : (2 * a * β - α * b) ^ 2 < (-(α * s)) ^ 2 := by
      rw [neg_sq, mul_pow, hs]; nlinarith
    have hu' := abs_lt_of_sq_lt_sq' hu (by nlinarith)
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr'
    have hrt : (C a * X ^ 2 + C b * X + C c).derivative.eval r = 2 * a * r + b := by
      simp
      ring
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, hrt]
    have h2a : 0 < 2 * a := by positivity
    have hz : a * r ^ 2 + b * r + c = 0 := by simpa using hr
    rw [hz, zero_mul, zero_add]
    rcases hr' with rfl | rfl
    · have h2 : 2 * a * ((-b - s) / (2 * a)) + b = -s := by field_simp; ring
      have h3 : (α * ((-b - s) / (2 * a)) + β) = ((2 * a * β - α * b) - α * s) / (2 * a) := by
        field_simp
        ring
      rw [h2, h3]
      refine mul_neg_of_pos_of_neg (div_pos ?_ h2a) (neg_neg_of_pos hs0)
      linarith [hu'.1]
    · have h2 : 2 * a * ((-b + s) / (2 * a)) + b = s := by field_simp; ring
      have h3 : (α * ((-b + s) / (2 * a)) + β) = ((2 * a * β - α * b) + α * s) / (2 * a) := by
        field_simp
        ring
      rw [h2, h3]
      refine mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos ?_ h2a) hs0
      linarith [hu'.2]

/-- Rows `q ^ m * R` and `q ^ (m + 1) * S` interlace when `q * S` leaves a
remainder certificate after division by the quadratic `R`. -/
theorem Interlaces.pow_mul_of_quadratic_remainder {q R S : ℝ[X]} (m : ℕ)
    {a b c p d α β : ℝ} (hR : R = C a * X ^ 2 + C b * X + C c)
    (hqS : q * S = R * (C p * X + C d) + (C α * X + C β))
    (hq : q.Splits) (hq0 : q ≠ 0) (ha : 0 < a) (hp : 0 < p) (hα : α < 0)
    (hcert : a * β ^ 2 - b * α * β + c * α ^ 2 < 0) :
    Interlaces (q ^ m * R) (q ^ (m + 1) * S) := by
  have hbase := strictInterl_quadratic_of_remainder (a := a) (b := b) (c := c)
    (p := p) (d := d) (α := α) (β := β) ha hp hα hcert
  have hstrict : StrictInterl R (q * S) := by
    rw [hR, hqS, hR]
    exact hbase
  have hRdeg : R.natDegree = 2 := by rw [hR]; exact natDegree_quadratic ha.ne'
  have hqSform : q * S =
      C (a * p) * X ^ 3 + C (a * d + b * p) * X ^ 2 +
        C (b * d + c * p + α) * X + C (c * d + β) := by
    rw [hqS, hR]; simp only [C_mul, C_add]; ring
  have hqSdeg : (q * S).natDegree = 3 := by
    rw [hqSform]; exact natDegree_cubic (mul_ne_zero ha.ne' hp.ne')
  have hdeg : R.natDegree + 1 = (q * S).natDegree := by rw [hRdeg, hqSdeg]
  have hmul := (hstrict.toInterlaces hdeg).mul_both_of_splits (hq.pow m)
    (pow_ne_zero m hq0)
  simpa [pow_succ, mul_assoc] using hmul

/-- Rows `q ^ m * R` and `q ^ (m + 1) * S` interlace when `q * S` leaves a
remainder certificate after division by the linear polynomial `R`. -/
theorem Interlaces.pow_mul_of_linear_remainder {q R S : ℝ[X]} (m : ℕ)
    {a b p d β : ℝ} (hR : R = C a * X + C b)
    (hqS : q * S = R * (C p * X + C d) + C β)
    (hq : q.Splits) (hq0 : q ≠ 0) (ha : 0 < a) (hp : 0 < p) (hβ : β < 0) :
    Interlaces (q ^ m * R) (q ^ (m + 1) * S) := by
  have hbase := strictInterl_linear_of_remainder (a := a) (b := b) (p := p)
    (d := d) (β := β) ha hp hβ
  have hstrict : StrictInterl R (q * S) := by
    rw [hR, hqS, hR]
    exact hbase
  have hRdeg : R.natDegree = 1 := by rw [hR]; exact natDegree_linear ha.ne'
  have hqSform : q * S =
      C (a * p) * X ^ 2 + C (a * d + b * p) * X + C (b * d + β) := by
    rw [hqS, hR]; simp only [C_mul, C_add]; ring
  have hqSdeg : (q * S).natDegree = 2 := by
    rw [hqSform]; exact natDegree_quadratic (mul_ne_zero ha.ne' hp.ne')
  have hdeg : R.natDegree + 1 = (q * S).natDegree := by rw [hRdeg, hqSdeg]
  have hmul := (hstrict.toInterlaces hdeg).mul_both_of_splits (hq.pow m)
    (pow_ne_zero m hq0)
  simpa [pow_succ, mul_assoc] using hmul

end RealRooted
