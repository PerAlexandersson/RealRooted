module

public import RealRooted.Apolarity
public import RealRooted.GraceHalfPlane
public import RealRooted.PolarDerivative

/-!
# Laguerre's theorem on polar derivatives

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "laguerre-polar-derivative"
formalized = "2026-07-01"
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
headline = true

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

Let $A \in \mathbb C[z]$ and $n \geq 1$. The **polar derivative** of $A$ of order $n$
with pole $\zeta \in \mathbb C$ is
$$
D_\zeta A(z) = n\,A(z) + (\zeta - z)\,A'(z).
$$
When $n = \deg A$ this lowers the degree by at most one. In the real setting, for
$f \in \mathbb R[z]$ and $a \in \mathbb R$, the polar derivative of $f$ with respect to $a$
is $n f + (a - z) f'$ with $n = \deg f$.

**Theorem** (Laguerre, closed disk). Let $A$ have degree exactly $n \geq 1$, and let
$D = \{z : |z - c| \leq r\}$ with $r \geq 0$. If all zeros of $A$ lie in $D$ and
$\zeta \notin D$, then all zeros of $D_\zeta A$ lie in $D$. Moreover,
$\deg D_\zeta A = n - 1$.

**Theorem** (Laguerre, closed half-plane). Let $A$ have degree exactly $n \geq 1$, let
$b \in \mathbb R$ and $H = \{z : \operatorname{Im} z \leq b\}$. If all zeros of $A$ lie in
$H$ and $\zeta \notin H$, then all zeros of $D_\zeta A$ lie in $H$. Moreover,
$\deg D_\zeta A = n - 1$.

**Theorem** (Laguerre, real line). If $f \in \mathbb R[z]$ splits over $\mathbb R$, that is,
$f$ is zero or real-rooted, then so does the polar derivative $n f + (a - z) f'$ with
respect to every real $a$, where $n = \deg f$.

These statements are the engine of [Grace's apolarity
theorem](/RealRooted/theorems/grace-apolarity/): there the polar derivative with a pole
outside the disk or half-plane keeps all zeros in the region while lowering the degree by
one.

## Proof idea

For the disk and the half-plane, suppose $w$ lies outside the region and
$D_\zeta A(w) = 0$. Then $A(w) \neq 0$, and the identity
$n A(w) + (\zeta - w) A'(w) = 0$ together with the logarithmic derivative
$A'(w)/A(w) = \sum_j 1/(w - z_j)$ over the zeros $z_j$ of $A$ says that
$n/(w - \zeta)$ equals $\sum_j 1/(w - z_j)$. The map $z \mapsto 1/(w - z)$ sends the region
to a convex set, which then contains the average of the $1/(w - z_j)$, so $\zeta$ lies in the
region, a contradiction. The degree statement computes the coefficient of $z^{n-1}$ in
$D_\zeta A$ as the leading coefficient of $A$ times $n\zeta - \sum_j z_j$, which is
nonzero because the average of the zeros lies in the region but $\zeta$ does not. For the real
line, translate $a$ to $0$. Then the polar derivative becomes $n g - z g'$, which is the
reflection of the derivative of the reflection of $g$. Reflection preserves splitting, and
the derivative of a real-rooted polynomial is real-rooted by Rolle's theorem.

## References

See [@RahmanSchmeisser2002].
<!-- /realrooted-catalog-content -->

This module exposes Laguerre's theorem for closed disks, closed half-planes and the real
line. The proofs live in `RealRooted.Apolarity`, `RealRooted.GraceHalfPlane` and
`RealRooted.PolarDerivative`.
-/
