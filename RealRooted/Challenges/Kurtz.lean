import RealRooted.Kurtz

/-!
# Kurtz challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "kurtz"
authors = ["Kurtz"]
years = [1992]

[[definitions]]
name = "RealRooted.Kurtz.PositiveCoeffsUpToDegree"
module = "RealRooted.Kurtz"
label = "Positive coefficients"

[[definitions]]
name = "RealRooted.Kurtz.KurtzStrictInequalities"
module = "RealRooted.Kurtz"
label = "Kurtz inequalities a_k² > 4 a_{k-1} a_{k+1}"

[[theorems]]
name = "RealRooted.Kurtz.coefficient_criterion"
module = "RealRooted.Kurtz"
label = "Kurtz's criterion"
-->

<!-- realrooted-catalog-content -->
# Kurtz’s coefficient criterion

If a polynomial has positive coefficients and
`aₖ² > 4 aₖ₋₁ aₖ₊₁` at every interior index, then all its roots are real and
distinct.

## References

D. C. Kurtz, “A sufficient condition for all the roots of a polynomial to be
real,” *American Mathematical Monthly* 99 (1992), 259–263.  See also the
[contextual account on symmetricfunctions.com](https://www.symmetricfunctions.com/realRooted.htm#kurtzTheorem).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRooted.htm#kurtzTheorem

Original references: J. I. Hutchinson, "On a remarkable class of entire
functions", Trans. Amer. Math. Soc. 25 (1923), 325--332, and D. C. Kurtz,
"A sufficient condition for all the roots of a polynomial to be real",
Amer. Math. Monthly 99 (1992), 259--263.

This module exposes the reusable theorem implementation in `RealRooted.Kurtz`.
-/

namespace RealRooted
namespace Challenges
namespace Kurtz

export RealRooted.Kurtz
  (PositiveCoeffsUpToDegree
    KurtzStrictInequalities
    ne_zero_of_kurtz
    hasPosLeadingCoeff_of_kurtz
    hasNonnegCoeffs_of_kurtz
    sum_range_succ_alternating
    antitone_of_succ_lt
    monotone_of_succ_gt
    antitone_capped_of_antitone
    antitone_rev_of_monotone
    alternating_sum_reflect
    lt_sqrt_mul_and_lt_of_lt
    monotone_of_lt_succ
    strictMono_of_lt_succ
    add_mul_sq_sqrt_div_lt_mul
    add_mul_self_lt_mul_self_of_add_mul_sq_lt
    div_lt_div_of_mul_lt_sq
    mul_neg_of_neg_mul_pos_of_mul_pos
    eval_neg_eq_sum_range
    sign_eval_neg_of_ratio_bounds
    ratio_lt_of_log_concave
    ratio_monotone_of_log_concave
    sqrt_ratio_between
    coefficient_criterion_card_roots
    coefficient_criterion
    coefficientCriterion)

end Kurtz
end Challenges
end RealRooted
