module

import RealRooted.EndpointDerivative.Basic
import RealRooted.EndpointDerivative.Sequence

/-!
# Endpoint derivative sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "endpoint-derivative"
formalized = "2026-09-26"
references = [
  "Fisk2006x",
]

[[theorems]]
name = "RealRooted.strictInterl_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "Interlacing after endpoint differentiation"
headline = true

[[theorems]]
name = "RealRooted.roots_endpointDerivative_mem_Icc"
module = "RealRooted.EndpointDerivative.Basic"
label = "Root interval after endpoint differentiation"

[[theorems]]
name = "RealRooted.strictInterl_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "Interlacing after differentiating the endpoint product"

[[theorems]]
name = "RealRooted.roots_derivative_endpointProduct_mem_Icc"
module = "RealRooted.EndpointDerivative.Basic"
label = "Root interval after differentiating the endpoint product"

[[theorems]]
name = "RealRooted.strictInterl_endpointDerivative_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Interlacing sequence for endpoint differentiation"

[[theorems]]
name = "RealRooted.strictInterl_derivative_endpointProduct_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Interlacing sequence for product differentiation"

[[theorems]]
name = "RealRooted.interlaces_endpointDerivative_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Interlacing sequence for endpoint differentiation"

[[theorems]]
name = "RealRooted.interlaces_derivative_endpointProduct_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Interlacing sequence for product differentiation"

[[theorems]]
name = "RealRooted.isRealRooted_endpointDerivative_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Real-rooted endpoint-derivative sequence"

[[theorems]]
name = "RealRooted.isRealRooted_derivative_endpointProduct_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Real-rooted product-derivative sequence"

[[theorems]]
name = "RealRooted.natDegree_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "Degree of endpoint differentiation"

[[theorems]]
name = "RealRooted.hasPosLeadingCoeff_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "Positive leading coefficient after endpoint differentiation"

[[theorems]]
name = "RealRooted.natDegree_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "Degree of product differentiation"

[[theorems]]
name = "RealRooted.hasPosLeadingCoeff_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "Positive leading coefficient after product differentiation"
-->

<!-- realrooted-catalog-content -->
# Endpoint derivative sequences

We fix $a \leq b$ and write $q=(X-a)(X-b)$. If a split polynomial $f$
has positive leading coefficient, positive degree, and all roots in $[a,b]$,
then `strictInterl_endpointDerivative` puts $f$ to the left of $qf'$ in
interlacing position. Here `StrictInterl` means that both polynomials are
nonzero and real-rooted; coinciding roots, for example at $a$ or $b$, are not
excluded. The roots of $qf'$ remain in the same interval, as recorded by
`roots_endpointDerivative_mem_Icc`.

We also apply the same argument to $(qf)'$. The product first adds the two
endpoint roots, and differentiation then gives the second pair of one-step
theorems. Thus `strictInterl_derivative_endpointProduct` gives strict
interlacing with $f$, while `roots_derivative_endpointProduct_mem_Icc`
preserves the root interval.

We use these one-step results inductively for a sequence $P$. Under the
corresponding recurrence, base splitting and root-window hypotheses, positive
leading coefficients, and positive degrees, the two sequence theorems give a
chain in this `StrictInterl` sense. Here $P(n+1)=qP(n)'$ for the first pair of
sequence theorems, while $P(n+1)=(qP(n))'$ for the second. In both cases
$a\le b$, $P(0)$ splits with all roots in $[a,b]$, and every $P(n)$ has
positive leading coefficient and degree at least $1$. With the additional
identity $\deg P(n)+1=\deg P(n+1)$, the
next two theorems convert that chain to `Interlaces`; the final two sequence
theorems state that every row is nonzero and split.

We keep the degree and leading-coefficient facts available as separate
supporting results. The first operator raises the degree by one under a
positive-degree hypothesis, and the second does so from positive leading
coefficient alone; the paired leading-coefficient theorems preserve positivity
for both operators.

## References

For derivative interlacing, see [@Fisk2006x, Ch. 1]. The first applications
are the rows of [OEIS A142071](https://oeis.org/A142071),
[OEIS A172106](https://oeis.org/A172106), [OEIS A172107](https://oeis.org/A172107),
and [OEIS A172108](https://oeis.org/A172108).
<!-- /realrooted-catalog-content -->
-/
