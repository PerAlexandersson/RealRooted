module

import RealRooted.DeterminantalStability.ExactReduction
import RealRooted.DeterminantalStability.Constants
import RealRooted.DeterminantalStability.Closure

/-!
# Reduction of bivariate determinantal representations

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
# Reduction of bivariate determinantal representations

A real stable bivariate polynomial becomes, after an explicit linear change of coordinates, a
homogeneous ternary polynomial that is hyperbolic at $(0,1,0)$. A determinantal form of this
ternary polynomial, as provided by the Helton–Vinnikov theorem, gives a determinantal
representation of the original polynomial.

## Results

A real polynomial $p(z,w)$ is *real stable* if it has no zero with both coordinates in the upper
half-plane. Let $H$ be the homogenization of $p$ in variables $(Y,T,Z)$ and let
$c=H(0,1,1)$. For $c\ne0$ put
$$
q=c^{-1}H(Y,T+X,T-X),\qquad q(0,1,0)=1.
$$

**Theorem (reduction).** Let $p$ be real stable with $c\ne0$. Then $q$ is hyperbolic at
$(0,1,0)$, and the substitution $Y=1$, $T=(z+w)/2$, $X=(z-w)/2$ returns $c^{-1}p$ from $q$.

**Theorem (determinantal forms).** Let $c\ne0$ and let $M,N$ be real $d\times d$ matrices with
$q=\det(TI+XM+YN)$. Then
$$
p=c\,\det\bigl(N+z\,(I+M)/2+w\,(I-M)/2\bigr).
$$

**Proposition (closure).** For each $d$, the evaluations of $\det(TI-XU-V)$ at
$X=0,1,\dotsc,d$, recorded as arrays of coefficients in $T$, form a closed set as $U,V$ range
over symmetric real $d\times d$ matrices.

## References

- [Bivariate determinantal representations](sf:bivariateStableDeterminantalRepresentation) on
  symmetricfunctions.com
- [Real stability](rr:real-stability)
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.DeterminantalStability`
modules named in the metadata.
-/
