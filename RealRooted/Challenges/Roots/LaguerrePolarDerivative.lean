module

import RealRooted.Apolarity
import RealRooted.GraceHalfPlane
import RealRooted.PolarDerivative

/-!
# Laguerre's theorem on polar derivatives

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "laguerre-polar-derivative"
formalized = "2026-07-01"
references = [
  "RahmanSchmeisser2002",
]
authors = ["Laguerre", "Rahman", "Schmeisser"]
years = [2002]

[[definitions]]
name = "RealRooted.polarDeriv"
module = "RealRooted.Apolarity"
label = "Polar derivative nA + (ζ − z)A′ of a degree-n polynomial"

[[definitions]]
name = "RealRooted.polarDerivative"
module = "RealRooted.PolarDerivative"
label = "Polar derivative of a real polynomial with respect to a real point"

[[theorems]]
name = "RealRooted.polarDeriv_rootsIn"
module = "RealRooted.Apolarity"
label = "Laguerre: a pole outside a closed disk keeps the zeros of the polar derivative in it"
headline = true

[[theorems]]
name = "RealRooted.polarDeriv_natDegree"
module = "RealRooted.Apolarity"
label = "With the pole outside the disk, the polar derivative has degree n − 1"

[[theorems]]
name = "RealRooted.polarDeriv_rootsIn_lowerHalf"
module = "RealRooted.GraceHalfPlane"
label = "Laguerre's theorem for a closed half-plane"

[[theorems]]
name = "RealRooted.splits_polarDerivative_of_splits"
module = "RealRooted.PolarDerivative"
label = "Laguerre: polar derivatives of real-rooted polynomials at real points are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Laguerre's theorem on polar derivatives

If all zeros of a polynomial of degree $n$ lie in a closed disk or half-plane, then its polar
derivative with respect to a point outside that set has degree $n-1$ and all its zeros in the
same set. On the real line, polar derivatives preserve real-rootedness.

## Results

For $A\in\mathbb C[z]$ of degree $n\ge1$ and $\zeta\in\mathbb C$, the *polar derivative* with
pole $\zeta$ is $D_\zeta A(z)=n\,A(z)+(\zeta-z)\,A'(z)$.

**Theorem (Laguerre).** Let $\deg A=n\ge1$, and let $D$ be a closed disk
$\{z:|z-c|\le r\}$ or a closed half-plane $\{z:\operatorname{Im}z\le b\}$. If all zeros of $A$
lie in $D$ and $\zeta\notin D$, then $\deg D_\zeta A=n-1$ and all zeros of $D_\zeta A$ lie in $D$.

**Corollary (real line).** If $f\in\mathbb R[z]$ is real-rooted, then so is
$n f+(a-z)f'$, with $n=\deg f$, for every real $a$.

## Use

Laguerre's theorem is the induction step in the proof of
[Grace's apolarity theorem](rr:grace-apolarity). The real form is one of the basic operators
preserving real-rootedness, next to differentiation.

## Proof

Let $w\notin D$ be a zero of $D_\zeta A$. Then $n/(w-\zeta)=\sum_j1/(w-z_j)$ over the zeros $z_j$
of $A$. The map $z\mapsto1/(w-z)$ sends $D$ to a convex set, which then contains the average of
the $1/(w-z_j)$, forcing $\zeta$ into $D$. For the real line, translating $a$ to $0$ turns the
polar derivative into $ng-zg'$, the reflection of the derivative of the reflection of $g$, and
Rolle's theorem applies.

## References

[@RahmanSchmeisser2002].
<!-- /realrooted-catalog-content -->
-/
