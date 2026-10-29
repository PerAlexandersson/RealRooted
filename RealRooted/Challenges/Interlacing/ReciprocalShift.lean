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

We write the degree-padded reciprocal shift as $t^D p(1/t)$. When
$\operatorname{natDegree}(p) \leq D$, the factorization theorem expresses it as
$X^{D-\operatorname{natDegree}(p)}p^{\mathrm{reverse}}$. A PF polynomial has
nonnegative coefficients and is either zero or split with all roots
nonpositive; this property is preserved by the transformation.

For a nonzero split polynomial, the roots theorem describes the new multiset:
we discard the zero roots, invert the remaining roots, and add
$D-\operatorname{natDegree}(p)$ zeros. The list-model theorems show that, when
the original roots are sorted and nonpositive, this construction is sorted and
has exactly the roots of the reciprocal shift.

We use the interleaving lemmas to handle the order reversal behind this
description. If two lists contain only strictly negative numbers and interleave,
then reversing and inverting them swaps the two lists when their lengths are
equal and keeps their order when the right list has one additional entry. The
antitonicity lemma for $x \mapsto 1/x$ supplies the order step.

Finally, we show that if $p$ and $q$ are PF polynomials with degrees at most the
same bound $D$ and $p\ll q$, the reciprocal shift
reverses the pair: $\operatorname{StrictInterl}(p,q)$ becomes
$\operatorname{StrictInterl}(\operatorname{reciprocalShift}(D,q),
\operatorname{reciprocalShift}(D,p))$.

## References

These results were promoted from proofs in the companion OEIS formalization
project. For background on interlacing and polynomial reversal, see [@Fisk2006x].
<!-- /realrooted-catalog-content -->
-/
