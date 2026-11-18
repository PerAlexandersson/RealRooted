module

import RealRooted.Apolarity
import RealRooted.BorceaBranden.Applications.PolarizationIff
import RealRooted.GraceHalfPlane
import RealRooted.GraceWalshSzego
import RealRooted.LiebSokalGeneral
import RealRooted.Polarization

/-!
# Grace's apolarity theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "grace-apolarity"
formalized = "2026-10-06"
references = [
  "Grace1902",
  "Walsh1922",
  "Szego1922",
  "RahmanSchmeisser2002",
  "BorceaBranden2009II",
  "LiebSokal1981",
  "GribinskiMarcus2022",
]
authors = ["Grace", "Walsh", "Szegő", "Lieb", "Sokal", "Borcea", "Brändén"]
years = [1902, 1922, 1981, 2009]

[[definitions]]
name = "RealRooted.AreApolar"
module = "RealRooted.Apolarity"
label = "Apolar polynomials"

[[definitions]]
name = "RealRooted.polarization"
module = "RealRooted.Polarization"
label = "Polarization"

[[theorems]]
name = "RealRooted.exists_isRoot_mem_closedBall_of_areApolar"
module = "RealRooted.Apolarity"
label = "Grace: if F and G are apolar and F has all zeros in a closed disk, so has G one"
headline = true

[[theorems]]
name = "RealRooted.exists_isRoot_le_im_of_areApolar"
module = "RealRooted.GraceHalfPlane"
label = "Grace's theorem for closed half-planes"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_polarization"
module = "RealRooted.Polarization"
label = "The polarization of a polynomial without zeros in the upper half-plane is stable"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero"
module = "RealRooted.Polarization"
label = "Grace–Walsh–Szegő: a symmetric multiaffine polynomial is stable iff its diagonal is"

[[theorems]]
name = "RealRooted.mvRealStable_iff_aeval_X_ne_zero_and_splits"
module = "RealRooted.BorceaBranden.Applications.PolarizationIff"
label = "Grace–Walsh–Szegő, real form: real stable iff the diagonal is real-rooted"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_mem_closedBall"
module = "RealRooted.GraceWalshSzego"
label = "Grace–Walsh–Szegő coincidence theorem for closed disks"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_im_div_pos"
module = "RealRooted.GraceWalshSzego"
label = "Coincidence theorem for open half-planes"

[[theorems]]
name = "RealRooted.GraceApolarity.polarization_stable_iff"
module = "RealRooted.BorceaBranden.Applications.PolarizationIff"
label = "Blockwise polarization preserves and reflects stability"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.liebSokal"
module = "RealRooted.LiebSokalGeneral"
label = "Lieb–Sokal: F(−∂)G is zero or stable for stable F and G"
-->

<!-- realrooted-catalog-content -->
# Grace's apolarity theorem

If two polynomials of degree $n$ are apolar and all zeros of one lie in a closed disk or closed
half-plane, then the other has a zero there. Through polarization this gives the
Grace–Walsh–Szegő theorem, the basic link between univariate real-rootedness and multivariate
stability.

## Results

Let $F(z)=\sum_{k=0}^n\binom nk a_kz^k$ and $G(z)=\sum_{k=0}^n\binom nk b_kz^k$. We call $F$ and
$G$ *apolar* if $\sum_{k=0}^n(-1)^k\binom nk a_kb_{n-k}=0$. A polynomial in several variables
is *stable* if it does not vanish when all variables lie in the open upper half-plane.

**Theorem (Grace).** [@Grace1902] Let $F$ and $G$ be apolar of degree exactly $n$. If all
zeros of $F$ lie in a closed disk or in a closed half-plane, then $G$ has a zero in the same set.

The *polarization* of $p(z)=\sum_{k\le n}p_kz^k$ is the symmetric multiaffine polynomial
$\operatorname{Pol}_n(p)=\sum_{k=0}^n\binom nk^{-1}p_k\,e_k(z_1,\dots,z_n)$, whose diagonal
$z_1=\dots=z_n=z$ is $p(z)$.

**Theorem (Grace–Walsh–Szegő).** [@Walsh1922; @Szego1922] Let $P\in\mathbb C[z_1,\dots,z_n]$
be symmetric and multiaffine, with diagonal $p$. Then $P=\operatorname{Pol}_n(p)$, and $P$ is
stable if and only if $p$ has no zero in the open upper half-plane. If $P$ is real, then $P$ is
real stable if and only if $p$ is nonzero and real-rooted. Moreover, if $C$ is a disk or a
half-plane, then for all $\zeta_1,\dots,\zeta_n\in C$ there is $\zeta\in C$ with
$P(\zeta_1,\dots,\zeta_n)=P(\zeta,\dots,\zeta)$.

**Theorem (blockwise polarization).** Replace each variable $z_i$ of $P$, of degree at most
$\kappa_i$ in $z_i$, by $\kappa_i$ new variables and polarize in each block. The result is
stable if and only if $P$ is stable.

**Theorem (Lieb–Sokal).** [@LiebSokal1981] If $F,G\in\mathbb C[z_1,\dots,z_m]$ are stable, then
$F(-\partial)\,G$, obtained by substituting $-\partial/\partial z_i$ for $z_i$ in $F$, is zero
or stable.

## Use

Grace–Walsh–Szegő turns a univariate real-rootedness question into one about a multiaffine
polynomial, where [real stability](rr:real-stability) has good closure properties. It is the
first step in the [Borcea–Brändén classification](rr:borcea-branden-classification) of linear
preservers.

## Proof

We prove Grace's theorem by induction on $n$: by
[Laguerre's theorem](rr:laguerre-polar-derivative), the polar derivative of $F$ lowers the
degree by one and keeps the zeros in the disk or half-plane. For polarization,
$\operatorname{Pol}_n(p)(z)=0$ says that $p$ is apolar to $\prod_i(w-z_i)$, so Grace's theorem
puts some $z_i$ in the closed lower half-plane. The coincidence theorem follows by applying this
to $P-P(\zeta)$ and Möbius maps.

## References

[@Grace1902]; [@Walsh1922]; [@Szego1922]; [@RahmanSchmeisser2002]; [@LiebSokal1981];
[@BorceaBranden2009II]; [@GribinskiMarcus2022, Thm. 2.4]. See also
[apolar polynomials](sf:apolarPolynomial) and [polarization](sf:polarizationDefinition) on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
