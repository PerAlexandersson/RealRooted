import RealRooted.Tactic.SideGoals

/-!
# Sign certificate tactic

The `rr_sign` tactic is a small arithmetic closer for coefficient-sign side
goals in Ma--Wang and Liu--Wang recurrence certificates.  It is intentionally
local: it does not apply an interlacing theorem, but it should close the
recurring polynomial-evaluation inequalities once the root interval and scalar
positivity hypotheses are in the context.
-/

open Polynomial

namespace RealRooted

lemma eval_X_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (X : ℝ[X]).eval r ≤ 0 := by
  simpa using hr

lemma eval_C_mul_X_nonpos_of_nonneg_of_nonpos {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X : ℝ[X]).eval r ≤ 0 := by
  simpa using mul_nonpos_of_nonneg_of_nonpos hc hr

lemma eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  have hone : 0 ≤ 1 - r := by linarith
  simpa [sub_eq_add_neg, mul_assoc] using mul_nonpos_of_nonpos_of_nonneg hcr hone

lemma eval_neg_C_mul_one_sub_X_sq_nonpos_of_nonneg {c r : ℝ}
    (hc : 0 ≤ c) :
    (-(C c) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ (1 - r) ^ 2 := sq_nonneg (1 - r)
  simpa [sub_eq_add_neg] using mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_neg_C_mul_X_sq_nonpos_of_nonneg {c r : ℝ}
    (hc : 0 ≤ c) :
    (-(C c) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ r ^ 2 := sq_nonneg r
  simpa using mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_neg_C_mul_one_add_X_sq_nonpos_of_nonneg {c r : ℝ}
    (hc : 0 ≤ c) :
    (-(C c) * (1 + X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ (1 + r) ^ 2 := sq_nonneg (1 + r)
  simpa [add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_C_neg_nonpos_of_nonneg {c r : ℝ} (hc : 0 ≤ c) :
    (C (-c) : ℝ[X]).eval r ≤ 0 := by
  simpa using neg_nonpos.mpr hc

namespace Tactic

syntax (name := rr_sign) "rr_sign" : tactic

macro_rules
  | `(tactic| rr_sign) =>
      `(tactic|
        solve
        | first
          | assumption
          | exact RealRooted.eval_X_nonpos_of_nonpos
              (by first | assumption | positivity | norm_num | nlinarith)
          | exact
              RealRooted.eval_C_mul_X_nonpos_of_nonneg_of_nonpos
                (by first | assumption | positivity | norm_num | nlinarith)
                (by first | assumption | positivity | norm_num | nlinarith)
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos
                (by first | assumption | positivity | norm_num | nlinarith)
                (by first | assumption | positivity | norm_num | nlinarith)
          | exact
              RealRooted.eval_neg_C_mul_one_sub_X_sq_nonpos_of_nonneg
                (by first | assumption | positivity | norm_num | nlinarith)
          | exact
              RealRooted.eval_neg_C_mul_X_sq_nonpos_of_nonneg
                (by first | assumption | positivity | norm_num | nlinarith)
          | exact
              RealRooted.eval_neg_C_mul_one_add_X_sq_nonpos_of_nonneg
                (by first | assumption | positivity | norm_num | nlinarith)
          | exact RealRooted.eval_C_neg_nonpos_of_nonneg
              (by first | assumption | positivity | norm_num | nlinarith)
          | simp_all [
              Polynomial.eval_add,
              Polynomial.eval_sub,
              Polynomial.eval_mul,
              Polynomial.eval_pow,
              Polynomial.eval_neg,
              Polynomial.eval_C,
              Polynomial.eval_X,
              sub_eq_add_neg]
            <;>
            first
              | positivity
              | norm_num
              | nlinarith
              | ring_nf <;> nlinarith
              | rr_side
          | positivity
          | norm_num
          | nlinarith
          | ring_nf <;> nlinarith
          | rr_side)

end Tactic
end RealRooted
