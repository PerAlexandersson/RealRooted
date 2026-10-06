import RealRooted.Hermite.PoulainInterlacing

/-!
# Hermite--Poulain challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-poulain"
authors = ["Hermite", "Poulain"]

[[definitions]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator"
module = "RealRooted.Hermite.Poulain"
label = "The operator f(D)"

[[theorems]]
name = "RealRooted.HermitePoulain.differential_operator_preserves_real_rooted"
module = "RealRooted.Hermite.Poulain"
label = "Hermite–Poulain theorem"

[[theorems]]
name = "RealRooted.HermitePoulain.interl_or_interl_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainInterlacing"
label = "Hermite–Poulain operators preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Hermite–Poulain theorem

For a polynomial $f(x) = \sum_k a_k x^k$, write $f(D) = \sum_k a_k D^k$, where
$D = d/dx$. If $f$ and $p$ are real-rooted, then $f(D)\,p$ is zero or
real-rooted.

Consequently, $f(D)$ preserves interlacing: if $f$ is nonzero and real-rooted
and $g$ and $h$ interlace, then $f(D)\,g$ and $f(D)\,h$ interlace in one of
the two orientations, where either image may be zero.

## References

The theorem goes back to Hermite and Poulain; see the
[Hermite–Poulain theorem on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainTheorem)
for further references, and the
[interlacing consequence](https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainTheorem

Original references include C. Hermite, G. Polya--I. Schur, N. Obreschkoff,
and B. Ya. Levin's account of entire functions.

The proof is in `RealRooted.Hermite.Poulain`; the interlacing consequence is in
`RealRooted.Hermite.PoulainInterlacing`.
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
    differentialOperator
    differentialOperator_apply
    preservesRealRootedOrZero_differentialOperator
    interl_or_interl_applyAsDifferentialOperator)

end HermitePoulain
end Challenges
end RealRooted
