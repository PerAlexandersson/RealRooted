import RealRooted.HermitePoulain

/-!
# Hermite--Poulain challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-poulain"
authors = ["Hermite", "Poulain"]

[[definitions]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator"
module = "RealRooted.HermitePoulain"

[[theorems]]
name = "RealRooted.HermitePoulain.differential_operator_preserves_real_rooted"
module = "RealRooted.HermitePoulain"
-->

<!-- realrooted-catalog-content -->
# Hermite–Poulain theorem

Replace each power in `f` by the corresponding derivative operator. If `f`
and the input polynomial are real-rooted, the output is zero or real-rooted.

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

The proof is in `RealRooted.HermitePoulain`.
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
