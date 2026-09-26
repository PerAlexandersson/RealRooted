import RealRooted.HermitePoulain

/-!
# Hermite--Poulain challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-poulain"

[[definitions]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator"
module = "RealRooted.HermitePoulain"

[[theorems]]
name = "RealRooted.HermitePoulain.differential_operator_preserves_real_rooted"
module = "RealRooted.HermitePoulain"
-->

<!-- realrooted-catalog-content -->
# Hermite–Poulain theorem

A polynomial `f` acts as a constant-coefficient differential operator by
replacing each power of its variable with the corresponding derivative.  The
selected theorem proves that when both the symbol `f` and the input polynomial
split over the reals, the output is either zero or also splits over the reals.

## References

This classical preservation theorem originates in work of Hermite and
Poulain; see the
[Hermite–Poulain overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainTheorem)
for context and further references.
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainTheorem

Original references include C. Hermite, G. Polya--I. Schur, N. Obreschkoff,
and B. Ya. Levin's account of entire functions.

This module preserves the established challenge-facing names as aliases for
the reusable theorem implementation in `RealRooted.HermitePoulain`.
-/

namespace RealRooted
namespace Challenges
namespace HermitePoulain

export RealRooted.HermitePoulain
  (applyAsDifferentialOperator
    applyAsDifferentialOperator_eq_sum_range
    applyAsDifferentialOperator_eq_sum_range_right
    coeff_applyAsDifferentialOperator_natDegree
    applyAsDifferentialOperator_monic
    natDegree_applyAsDifferentialOperator
    applyAsDifferentialOperator_ne_zero
    applyAsDifferentialOperator_zero_right
    applyAsDifferentialOperator_C
    applyAsDifferentialOperator_one
    applyAsDifferentialOperator_X_add_C
    applyAsDifferentialOperator_add
    applyAsDifferentialOperator_C_mul
    applyAsDifferentialOperator_X_mul
    applyAsDifferentialOperator_monomial
    applyAsDifferentialOperator_X_pow_mul
    applyAsDifferentialOperator_mul
    applyAsDifferentialOperator_C_eq_zero_or_splits
    applyAsDifferentialOperator_X_add_C_eq_zero_or_splits
    differential_operator_preserves_real_rooted
    differentialOperator_preserves_realRooted)

end HermitePoulain
end Challenges
end RealRooted
