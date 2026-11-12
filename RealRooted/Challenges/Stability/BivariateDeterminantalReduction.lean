module

import RealRooted.DeterminantalStability.ExactReduction
import RealRooted.DeterminantalStability.Constants
import RealRooted.DeterminantalStability.Closure

/-!
# Exact reduction of bivariate determinantal representations

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "bivariate-determinantal-reduction"
formalized = "2026-10-29"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.BivariateDetRep.normalizedExactReduction"
module = "RealRooted.DeterminantalStability.ExactReduction"
label = "The normalized ternary polynomial c⁻¹ H(Y, T + X, T - X)"

[[definitions]]
name = "RealRooted.symmetricPencilEvaluationRange"
module = "RealRooted.DeterminantalStability.Closure"
label = "Evaluation arrays of symmetric real characteristic pencils"

[[theorems]]
name = "RealRooted.BivariateDetRep.exactBackSubstitution_normalizedExactReduction"
module = "RealRooted.DeterminantalStability.ExactReduction"
label = "Back substitution recovers p up to the boundary constant"

[[theorems]]
name = "RealRooted.BivariateDetRep.eq_C_mul_realDetPencil_of_normalizedExactReduction_eq"
module = "RealRooted.DeterminantalStability.ExactReduction"
label = "A symmetric ternary determinantal form gives p = c det(N + z (I+M)/2 + w (I-M)/2)"
headline = true

[[theorems]]
name = "RealRooted.isClosed_symmetricPencilEvaluationRange"
module = "RealRooted.DeterminantalStability.Closure"
label = "The set of evaluation arrays of symmetric characteristic pencils is closed"
-->

<!-- realrooted-catalog-content -->
# Exact reduction of bivariate determinantal representations

A real polynomial $p(z,w)$ is *real stable* if it has no zero with both coordinates in the
upper half-plane. We formalize the exact coordinate reduction from the bivariate
determinantal representation problem to the normalized ternary hyperbolic statement
(the Helton--Vinnikov form).

Let $H$ be the ordinary homogenization of $p$ in variables $(Y,T,Z)$ and let
$c=H(0,1,1)$, assumed nonzero. The substitution $(Y,T,X)\mapsto(Y,T+X,T-X)$ turns $H$
into a homogeneous ternary polynomial $q=c^{-1}H(Y,T+X,T-X)$ with $q(0,1,0)=1$.

**Reduction.** If $p$ is real stable, then $q$ is hyperbolic at $(0,1,0)$. Conversely,
back substitution $Y=1$, $T=(z+w)/2$, $X=(z-w)/2$ returns $c^{-1}p$, and if
$q=\det(TI+XM+YN)$ for real matrices $M,N$, then
$$
p=c\,\det\bigl(N+z\,(I+M)/2+w\,(I-M)/2\bigr).
$$

## Related facts

The empty determinantal pencil is $1$, so constant polynomials such as $2$ and $-2$ are
nonunit scalar multiples of degree-zero pencils. The polynomial $\det(TI-XU-V)$ is
encoded by the coefficients in $T$ after evaluating $X$ at $0,1,\dots,d$, and the set of
arrays arising from symmetric real matrices $U,V$ is closed.

## What is new

These reductions were developed in this library; no published
source is cited, and we attribute none.

## References

No published source is cited for these results in the formalization. See also the
[real stability page](/RealRooted/theorems/real-stability/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.DeterminantalStability`
modules named in the metadata.
-/
