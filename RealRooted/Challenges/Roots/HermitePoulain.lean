module

public import RealRooted.Hermite.PoulainInterlacing

/-!
# Hermite–Poulain theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-poulain"
formalized = "2026-07-18"
references = []
tags = []
authors = ["Hermite", "Poulain"]

[[definitions]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator"
module = "RealRooted.Hermite.Poulain"
label = "The operator f(D)"

[[theorems]]
name = "RealRooted.HermitePoulain.differential_operator_preserves_real_rooted"
module = "RealRooted.Hermite.Poulain"
label = "Hermite–Poulain theorem"
headline = true
symcat = "hermitePoulainTheorem"

[[theorems]]
name = "RealRooted.HermitePoulain.interl_or_interl_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainInterlacing"
label = "Hermite–Poulain operators preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Hermite–Poulain theorem

A constant-coefficient differential operator $f(D)$ with real-rooted symbol $f$ maps real-rooted
polynomials to zero or real-rooted polynomials, and preserves interlacing.

## Results

We write $g\ll h$ if $g$ interlaces $h$; repeated and common roots are allowed unless stated.
For $f(x)=\sum_ka_kx^k$ let $f(D)=\sum_ka_kD^k$ with $D=d/dx$.

**Theorem (Hermite–Poulain).** If $f$ and $p$ are nonzero and real-rooted, then $f(D)\,p$ is
zero or real-rooted.

**Corollary (interlacing).** Let $f$ be nonzero and real-rooted and let $g\ll h$. Then
$f(D)g\ll f(D)h$ or $f(D)h\ll f(D)g$, where we regard $0$ as interlacing every polynomial.

## References

The theorem goes back to Hermite and Poulain; see the
[Hermite–Poulain theorem on symmetricfunctions.com](sf:hermitePoulainTheorem)
for further references, and the
[interlacing consequence](sf:hermitePoulainInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
sf:hermitePoulainTheorem

Original references include C. Hermite, G. Polya--I. Schur, N. Obreschkoff,
and B. Ya. Levin's account of entire functions.

The proof is in `RealRooted.Hermite.Poulain`; the interlacing consequence is in
`RealRooted.Hermite.PoulainInterlacing`.
-/

public section

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
