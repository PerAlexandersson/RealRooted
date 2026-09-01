import RealRooted.SignEvaluation
import RealRooted.Tactic.SideGoals

/-!
The `rr_sign` tactic is a small arithmetic closer for coefficient-sign side
goals in Ma--Wang and Liu--Wang recurrence certificates.  It is intentionally
local: it does not apply an interlacing theorem, but it should close the
recurring polynomial-evaluation inequalities once the root interval and scalar
positivity hypotheses are in the context.
-/

open Polynomial

namespace RealRooted

namespace Tactic

syntax (name := rr_sign_side) "rr_sign_side" : tactic

syntax (name := rr_sign_side_term) "rr_sign_side_term" : term

macro_rules
  | `(tactic| rr_sign_side) =>
      `(tactic|
        first
          | rr_side_nonneg
          | rr_side)
  | `(rr_sign_side_term) =>
      `(by rr_sign_side)

end Tactic


namespace Tactic

syntax (name := rr_sign) "rr_sign" : tactic

macro_rules
  | `(tactic| rr_sign) =>
      `(tactic|
        solve
        | first
          | assumption
          | exact
              RealRooted.eval_X_add_X_sq_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_neg_one_add_two_X_sub_X_sq_nonpos
          | exact RealRooted.eval_neg_one_sub_two_X_sub_X_sq_nonpos
          | exact
              RealRooted.eval_neg_two_fifths_add_four_fifths_X_sub_two_fifths_X_sq_nonpos
          | exact
              RealRooted.eval_neg_two_thirds_add_four_thirds_X_sub_two_thirds_X_sq_nonpos
          | exact
              RealRooted.eval_neg_eight_fifths_add_eight_fifths_X_sub_two_fifths_X_sq_nonpos
          | exact
              RealRooted.eval_X_mul_one_add_four_mul_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_add_four_mul_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_X_nonpos_of_nonpos
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_two_X_sub_two_X_sq_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_X_mul_one_sub_X_nonpos_of_nonpos
              rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_C_sub_X_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_C_sub_X_nonpos_of_nonneg_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_C_sub_C_mul_X_nonpos_of_nonneg_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_C_sub_C_mul_X_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_one_add_X_nonpos_of_le_neg_one
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_C_add_X_nonpos_of_le_neg
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_add_X_nonpos_of_nonneg_of_ge_neg_one
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_add_two_mul_X_nonpos_of_nonneg_of_ge_neg_half
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_X_sub_one_nonpos_of_le_one
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_add_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_add_C_mul_X_sq_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_add_C_mul_X_nonpos_of_nonpos_of_linear_nonneg
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_add_C_mul_X_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_sq_sub_one_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_sq_sub_one_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_one_add_X_mul_one_add_two_mul_X_nonpos_of_nonneg_of_mem_interval
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_sub_X_sq_nonpos_of_nonpos
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_sq_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_sub_X_mul_one_add_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_sub_X_pow_three_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_sub_X_pow_three_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_nonpos_of_nonpos_of_nonneg
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_sub_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_add_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact
              RealRooted.eval_C_neg_add_C_neg_two_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact RealRooted.eval_C_neg_nonpos_of_nonneg
              rr_sign_side_term
          | exact RealRooted.eval_neg_C_nonpos_of_nonneg
              rr_sign_side_term
          | exact RealRooted.eval_neg_C_mul_sq_nonpos_of_nonneg
              rr_sign_side_term
          | exact RealRooted.eval_neg_monic_quadratic_nonpos_of_discrim_nonpos
              rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_monic_quadratic_nonpos_of_nonneg_of_discrim_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_quadratic_nonpos_of_discrim_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
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
