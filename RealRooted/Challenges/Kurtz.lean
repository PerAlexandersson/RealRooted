import RealRooted.Kurtz

/-!
# Kurtz challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "kurtz"

[[definitions]]
name = "RealRooted.Kurtz.PositiveCoeffsUpToDegree"
module = "RealRooted.Kurtz"

[[definitions]]
name = "RealRooted.Kurtz.KurtzStrictInequalities"
module = "RealRooted.Kurtz"

[[theorems]]
name = "RealRooted.Kurtz.coefficient_criterion"
module = "RealRooted.Kurtz"
-->

<!-- realrooted-catalog-content -->
# Kurtz’s coefficient criterion

Kurtz’s criterion gives a concrete sufficient condition for a polynomial to
have distinct real roots.  If all coefficients through the degree are
positive and each interior coefficient satisfies the strict quadratic
inequality `aₖ² > 4 aₖ₋₁ aₖ₊₁`, then the polynomial splits over the reals and
has no repeated root.  The selected theorem formalizes this implication with
the coefficient range and endpoint conditions made explicit.

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

This module preserves the established challenge-facing names as aliases for
the reusable theorem implementation in `RealRooted.Kurtz`.
-/

namespace RealRooted
namespace Challenges
namespace Kurtz

export RealRooted.Kurtz
  (PositiveCoeffsUpToDegree
    PositiveCoefficientsUpToDegree
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
