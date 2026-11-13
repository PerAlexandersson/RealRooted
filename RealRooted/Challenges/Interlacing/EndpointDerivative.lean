module

import RealRooted.EndpointDerivative.Basic
import RealRooted.EndpointDerivative.Sequence

/-!
# Interlacing and root intervals of endpoint-derivative sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "endpoint-derivative"
formalized = "2026-09-26"
authors = ["Fisk"]
tags = []
references = [
  "Fisk2006x",
]

[[theorems]]
name = "RealRooted.strictInterl_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "f interlaces (x-a)(x-b)f' when its roots lie in [a,b]"
headline = true

[[theorems]]
name = "RealRooted.roots_endpointDerivative_mem_Icc"
module = "RealRooted.EndpointDerivative.Basic"
label = "The roots of (x-a)(x-b)f' lie in [a,b]"

[[theorems]]
name = "RealRooted.strictInterl_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "f interlaces ((x-a)(x-b)f)' when its roots lie in [a,b]"

[[theorems]]
name = "RealRooted.roots_derivative_endpointProduct_mem_Icc"
module = "RealRooted.EndpointDerivative.Basic"
label = "The roots of ((x-a)(x-b)f)' lie in [a,b]"

[[theorems]]
name = "RealRooted.strictInterl_endpointDerivative_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Iterating (x-a)(x-b)f' gives a chain P_n ≪ P_{n+1}"

[[theorems]]
name = "RealRooted.strictInterl_derivative_endpointProduct_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Iterating ((x-a)(x-b)f)' gives a chain P_n ≪ P_{n+1}"

[[theorems]]
name = "RealRooted.interlaces_endpointDerivative_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Iterating (x-a)(x-b)f' with degrees rising by one: differ-by-one interlacing"

[[theorems]]
name = "RealRooted.interlaces_derivative_endpointProduct_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Iterating ((x-a)(x-b)f)' with degrees rising by one: differ-by-one interlacing"

[[theorems]]
name = "RealRooted.isRealRooted_endpointDerivative_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Iterating (x-a)(x-b)f' gives nonzero real-rooted rows"

[[theorems]]
name = "RealRooted.isRealRooted_derivative_endpointProduct_sequence"
module = "RealRooted.EndpointDerivative.Sequence"
label = "Iterating ((x-a)(x-b)f)' gives nonzero real-rooted rows"

[[theorems]]
name = "RealRooted.natDegree_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "(x-a)(x-b)f' has degree deg f + 1"

[[theorems]]
name = "RealRooted.hasPosLeadingCoeff_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "(x-a)(x-b)f' has positive leading coefficient"

[[theorems]]
name = "RealRooted.natDegree_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "((x-a)(x-b)f)' has degree deg f + 1"

[[theorems]]
name = "RealRooted.hasPosLeadingCoeff_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "((x-a)(x-b)f)' has positive leading coefficient"
-->

<!-- realrooted-catalog-content -->
# Interlacing and root intervals of endpoint-derivative sequences

Applying $f\mapsto(x-a)(x-b)f'$ or $f\mapsto((x-a)(x-b)f)'$ to a real-rooted polynomial with all
roots in $[a,b]$ gives a polynomial of one higher degree that is real-rooted, interlaced by $f$,
and has all roots in $[a,b]$.

## Results

Fix real numbers $a\le b$ and put $q=(x-a)(x-b)$.

**Theorem (one step).** Let $f$ be real-rooted with positive leading coefficient, degree at
least $1$, and all roots in $[a,b]$. Then
$$
f\ll qf'\qquad\text{and}\qquad f\ll(qf)',
$$
and all roots of $qf'$ and of $(qf)'$ lie in $[a,b]$. Moreover $qf'$ and $(qf)'$ have degree
$\deg f+1$ and positive leading coefficient.

**Theorem (sequences).** Let $P_0$ be real-rooted with all roots in $[a,b]$, and suppose that
every $P_n$ has positive leading coefficient and degree at least $1$. Suppose that
$P_{n+1}=qP_n'$ for all $n$, or that $P_{n+1}=(qP_n)'$ for all $n$. Then every $P_n$ is nonzero
and real-rooted and $P_n\ll P_{n+1}$ for all $n$. If moreover $\deg P_{n+1}=\deg P_n+1$ for all
$n$, then $P_n$ interlaces $P_{n+1}$ in the differ-by-one sense.

## Proof

Both maps have the form $f\mapsto uf+qf'$, with $u=0$ or $u=q'$. The derivative step of
Ma–Wang and Liu–Wang gives $f\ll uf+qf'$ when $q\le0$ at the roots of $f$ and $uf+qf'$ has
positive leading coefficient and degree $\deg f+1$; here $q\le0$ on $[a,b]$. The sequence
theorem follows by induction on $n$, since the one-step theorem preserves the hypotheses.

## References

For derivative interlacing, see [@Fisk2006x, Ch. 1]. The derivative step is on the
[Ma–Wang and Liu–Wang page](rr:ma-wang-liu-wang). Examples are the rows of
[OEIS A142071](https://oeis.org/A142071), [OEIS A172106](https://oeis.org/A172106),
[OEIS A172107](https://oeis.org/A172107) and [OEIS A172108](https://oeis.org/A172108).
<!-- /realrooted-catalog-content -->
-/
