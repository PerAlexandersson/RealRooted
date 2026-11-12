module

import RealRooted.PFPolynomial
import RealRooted.ReciprocalShift.Interlacing
import RealRooted.ReciprocalShift.Interlacing.Inversion
import RealRooted.ReciprocalShift.ProperPosition
import RealRooted.ReciprocalShift.Roots

/-!
# Reciprocal shifts and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "reciprocal-shift"
formalized = "2026-09-26"
authors = ["Fisk"]
tags = []
references = [
  "Fisk2006x",
]

[[theorems]]
name = "RealRooted.reciprocalShift_reverses_strictInterl"
module = "RealRooted.ReciprocalShift.ProperPosition"
label = "Reciprocal shifts reverse interlacing"
headline = true

[[theorems]]
name = "RealRooted.roots_reciprocalShift_eq"
module = "RealRooted.ReciprocalShift.Roots"
label = "Roots of a reciprocal shift"

[[theorems]]
name = "RealRooted.reciprocalShift_preserves_pf"
module = "RealRooted.PFPolynomial"
label = "PF preservation under reciprocal shifts"

[[theorems]]
name = "RealRooted.reciprocalShift_eq_X_pow_mul_reverse"
module = "RealRooted.PFPolynomial"
label = "Factorization of a reciprocal shift"

[[theorems]]
name = "RealRooted.interleaves_reverse_map_one_div_of_length_eq"
module = "RealRooted.ReciprocalShift.Interlacing.Inversion"
label = "Inversion of equal-length interleavings"

[[theorems]]
name = "RealRooted.interleaves_reverse_map_one_div_of_length_add_one_eq"
module = "RealRooted.ReciprocalShift.Interlacing.Inversion"
label = "Inversion of length-shifted interleavings"

[[theorems]]
name = "RealRooted.reciprocalShift_model_roots"
module = "RealRooted.ReciprocalShift.Interlacing"
label = "List model for reciprocal-shift roots"

[[theorems]]
name = "RealRooted.reciprocalShift_model_sorted"
module = "RealRooted.ReciprocalShift.Interlacing"
label = "Sorted reciprocal-shift root model"

[[theorems]]
name = "RealRooted.one_div_antitone_of_nonpos"
module = "RealRooted.ReciprocalShift.Interlacing"
label = "Antitonicity of inversion on negative numbers"
-->

<!-- realrooted-catalog-content -->
# Reciprocal shifts and interlacing

The reciprocal shift $x^Dp(1/x)$ inverts the nonzero roots of $p$, and it reverses interlacing of
Pólya frequency polynomials.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated. A
real polynomial $p$ is *PF* if it has nonnegative coefficients and is either zero or splits over
$\mathbb R$ with all roots at most $0$. For $D\ge\deg p$ the *reciprocal shift* is
$p_D(x)=x^Dp(1/x)$, the polynomial with coefficients reversed within degree $D$.

**Theorem (reversal).** Let $p,q$ be PF polynomials of degree at most $D$ with $p\ll q$. Then
$q_D\ll p_D$.

**Proposition (factorization and roots).** For $\deg p\le D$,
$$
p_D=x^{D-\deg p}\,p^{\mathrm{rev}},
$$
where $p^{\mathrm{rev}}$ is the reversed polynomial. If $p\ne0$ splits, then the roots of $p_D$,
with multiplicity, are $D-\deg p$ zeros together with the inverses of the nonzero roots of $p$.
If $p$ is PF, so is $p_D$.

**Lemma (root lists).** Let $\ell$ be a sorted list of the roots of a nonzero split polynomial
$p$ of degree at most $D$, all at most $0$. Remove the zeros from $\ell$, reverse it, invert each
entry, and append $D-\deg p$ zeros. The result is a sorted list of the roots of $p_D$.

**Lemma (interleaving lists).** Let $A,B$ be lists of negative reals that interleave. Inverting
and reversing both lists swaps them if $|A|=|B|$, and keeps their order if $|A|+1=|B|$. The step
uses that $t\mapsto 1/t$ is order-reversing on negative reals.

## References

Background on interlacing and polynomial reversal: [@Fisk2006x].
<!-- /realrooted-catalog-content -->
-/
