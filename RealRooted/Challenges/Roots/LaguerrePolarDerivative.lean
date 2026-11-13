module

import RealRooted.Apolarity
import RealRooted.GraceHalfPlane
import RealRooted.PolarDerivative

/-!
# Laguerre's theorem on polar derivatives

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "laguerre-polar-derivative"
formalized = "2026-07-01"
tags = []
references = [
  "RahmanSchmeisser2002",
]
authors = ["Rahman", "Schmeisser"]
years = [2002]

[[definitions]]
name = "RealRooted.polarDeriv"
module = "RealRooted.Apolarity"
label = "Polar derivative nA + (ζ − z)A′ of a degree-n polynomial"

[[definitions]]
name = "RealRooted.polarDerivative"
module = "RealRooted.PolarDerivative"
label = "Polar derivative of a polynomial with respect to a point"

[[definitions]]
name = "Polynomial.RootsIn"
module = "RealRooted.Apolarity"
label = "All roots lie in a set"

[[definitions]]
name = "RealRooted.lowerHalf"
module = "RealRooted.GraceHalfPlane"
label = "Closed lower half-plane"

[[theorems]]
name = "RealRooted.polarDeriv_rootsIn"
module = "RealRooted.Apolarity"
label = "Laguerre's theorem for a closed disk"
headline = true

[[theorems]]
name = "RealRooted.polarDeriv_rootsIn_lowerHalf"
module = "RealRooted.GraceHalfPlane"
label = "Laguerre's theorem for a closed half-plane"

[[theorems]]
name = "RealRooted.polarDeriv_natDegree"
module = "RealRooted.Apolarity"
label = "The polar derivative drops the degree by exactly one (closed disk)"

[[theorems]]
name = "RealRooted.polarDeriv_natDegree_lowerHalf"
module = "RealRooted.GraceHalfPlane"
label = "The polar derivative drops the degree by exactly one (closed half-plane)"
-->

<!-- realrooted-catalog-content -->
# Laguerre's theorem on polar derivatives

The polar derivative of a degree-$n$ polynomial with respect to a pole outside a closed disk or
half-plane containing all its zeros has degree $n-1$ and all its zeros in the same set.

## Results

For $A\in\mathbb C[z]$, $n\ge1$ and $\zeta\in\mathbb C$, the *polar derivative* of order $n$ with
pole $\zeta$ is
$$
D_\zeta A(z)=n\,A(z)+(\zeta-z)\,A'(z).
$$
For $n=\deg A$ it has degree at most $n-1$. For a real polynomial $f$ and $a\in\mathbb R$ we
write $D_af=n f+(a-z)f'$ with $n=\deg f$.

**Theorem (Laguerre, closed disk).** Let $\deg A=n\ge1$ and let $D=\{z:|z-c|\le r\}$ with
$r\ge0$. If all zeros of $A$ lie in $D$ and $\zeta\notin D$, then all zeros of $D_\zeta A$ lie in
$D$, and $\deg D_\zeta A=n-1$.

**Theorem (Laguerre, closed half-plane).** Let $\deg A=n\ge1$, let $b\in\mathbb R$ and
$H=\{z:\operatorname{Im}z\le b\}$. If all zeros of $A$ lie in $H$ and $\zeta\notin H$, then all
zeros of $D_\zeta A$ lie in $H$, and $\deg D_\zeta A=n-1$.

**Theorem (Laguerre, real line).** If $f\in\mathbb R[z]$ is zero or real-rooted, then so is
$D_af$ for every real $a$.

## Use

These statements drive [Grace's apolarity theorem](rr:grace-apolarity): the
polar derivative with a pole outside the disk or half-plane keeps all zeros in the region while
lowering the degree by one.

## Proof

For the disk and the half-plane, let $w$ outside the region be a zero of $D_\zeta A$. Then
$n/(w-\zeta)=\sum_j1/(w-z_j)$ over the zeros $z_j$ of $A$. The map $z\mapsto1/(w-z)$ sends the
region to a convex set, which then contains the average of the $1/(w-z_j)$, forcing $\zeta$ into
the region. For the real line, translating $a$ to $0$ turns $D_af$ into $ng-zg'$, which is the
reflection of the derivative of the reflection of $g$; reflection preserves real-rootedness, and
the derivative of a real-rooted polynomial is real-rooted by Rolle's theorem.

## References

See [@RahmanSchmeisser2002].
<!-- /realrooted-catalog-content -->

This module exposes Laguerre's theorem for closed disks, closed half-planes and the real
line. The proofs live in `RealRooted.Apolarity`, `RealRooted.GraceHalfPlane` and
`RealRooted.PolarDerivative`.
-/
