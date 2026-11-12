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
label = "A form q = det(T I + X M + Y N) gives p = c det(N + z (I+M)/2 + w (I-M)/2)"
headline = true

[[theorems]]
name = "RealRooted.isClosed_symmetricPencilEvaluationRange"
module = "RealRooted.DeterminantalStability.Closure"
label = "The set of evaluation arrays of symmetric characteristic pencils is closed"
-->

<!-- realrooted-catalog-content -->
# Exact reduction of bivariate determinantal representations

A real stable bivariate polynomial reduces, by an exact linear change of coordinates, to a
homogeneous ternary polynomial that is hyperbolic at $(0,1,0)$ (the normalized form in the
Helton–Vinnikov theorem), and determinantal forms of the
ternary polynomial give determinantal forms of $p$.

## Results

A real polynomial $p(z,w)$ is *real stable* if it has no zero with both coordinates in the upper
half-plane. Let $H$ be the ordinary homogenization of $p$ in variables $(Y,T,Z)$ and let
$c=H(0,1,1)$. For $c\ne0$ the substitution $(Y,T,X)\mapsto(Y,T+X,T-X)$ turns $H$ into the
ternary polynomial
$$q=c^{-1}H(Y,T+X,T-X),\qquad q(0,1,0)=1.$$

**Theorem (reduction).** Let $p$ be real stable with $c\ne0$. Then $q$ is hyperbolic at
$(0,1,0)$. The back substitution $Y=1$, $T=(z+w)/2$, $X=(z-w)/2$ returns $c^{-1}p$ from $q$.

**Theorem (determinantal forms).** Let $c\ne0$ and let $M,N$ be real $d\times d$ matrices with
$q=\det(TI+XM+YN)$. Then
$$p=c\,\det\bigl(N+z\,(I+M)/2+w\,(I-M)/2\bigr).$$

**Proposition (closure).** For each $d$, the evaluations of $\det(TI-XU-V)$ at
$X=0,1,\dots,d$, recorded as arrays of coefficients in $T$, form a closed set as $U,V$ range over
symmetric real $d\times d$ matrices.

The empty determinantal pencil is $1$, so constant polynomials such as $2$ and $-2$ are nonunit
scalar multiples of degree-zero pencils.

## References

See also the [real stability page](/RealRooted/theorems/real-stability/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.DeterminantalStability`
modules named in the metadata.
-/
