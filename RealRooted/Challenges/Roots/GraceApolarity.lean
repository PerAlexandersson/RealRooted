module

public import RealRooted.Apolarity
public import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
public import RealRooted.BorceaBranden.Applications.PolarizationIff
public import RealRooted.GraceHalfPlane
public import RealRooted.GraceWalshSzego
public import RealRooted.LiebSokal
public import RealRooted.LiebSokalGeneral
public import RealRooted.LiebSokalOperator
public import RealRooted.Polarization

/-!
# Grace's apolarity theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "grace-apolarity"
formalized = "2026-10-06"
tags = []
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
name = "RealRooted.binomialLift"
module = "RealRooted.Apolarity"
label = "Polynomial with binomial-weighted coefficients"

[[definitions]]
name = "RealRooted.AreApolar"
module = "RealRooted.Apolarity"
label = "Apolar polynomials"

[[definitions]]
name = "RealRooted.polarization"
module = "RealRooted.Polarization"
label = "Polarization"

[[definitions]]
name = "RealRooted.diagonalProjection"
module = "RealRooted.Polarization"
label = "Diagonal of a multivariate polynomial"

[[definitions]]
name = "RealRooted.BorceaBranden.blockwisePolarizationDegreeBoxGeneral"
module = "RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization"
label = "Blockwise polarization in a degree box"

[[definitions]]
name = "RealRooted.applyNegDifferential"
module = "RealRooted.LiebSokalOperator"
label = "Differential action F(−∂)G"

[[theorems]]
name = "RealRooted.exists_isRoot_mem_closedBall_of_areApolar"
module = "RealRooted.Apolarity"
label = "Grace's apolarity theorem for closed disks"
headline = true

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_polarization"
module = "RealRooted.Polarization"
label = "Polarization preserves stability"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero"
module = "RealRooted.Polarization"
label = "Grace–Walsh–Szegő: a symmetric multiaffine polynomial is stable iff its diagonal is"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_mem_closedBall"
module = "RealRooted.GraceWalshSzego"
label = "Grace–Walsh–Szegő coincidence theorem for closed disks"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_mem_ball"
module = "RealRooted.GraceWalshSzego"
label = "Coincidence theorem for open disks"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_im_div_pos"
module = "RealRooted.GraceWalshSzego"
label = "Coincidence theorem for open half-planes"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_im_div_nonneg"
module = "RealRooted.GraceWalshSzego"
label = "Coincidence theorem for closed half-planes"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_lt_dist"
module = "RealRooted.GraceWalshSzego"
label = "Coincidence theorem for the exterior of a disk, when the diagonal has degree n"

[[theorems]]
name = "RealRooted.exists_eval_const_eq_of_le_dist"
module = "RealRooted.GraceWalshSzego"
label = "Coincidence theorem for the closed exterior of a disk"

[[theorems]]
name = "RealRooted.mvRealStable_iff_aeval_X_ne_zero_and_splits"
module = "RealRooted.BorceaBranden.Applications.PolarizationIff"
label = "Grace–Walsh–Szegő, real form: real stable iff the diagonal is real-rooted"

[[theorems]]
name = "RealRooted.polarization_diagonalProjection"
module = "RealRooted.Polarization"
label = "A symmetric multiaffine polynomial is the polarization of its diagonal"

[[theorems]]
name = "RealRooted.GraceApolarity.polarization_stable_iff"
module = "RealRooted.BorceaBranden.Applications.PolarizationIff"
label = "Blockwise polarization preserves and reflects stability"

[[theorems]]
name = "RealRooted.exists_isRoot_le_im_of_areApolar"
module = "RealRooted.GraceHalfPlane"
label = "Grace's apolarity theorem for closed half-planes"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.liebSokal_multiaffine"
module = "RealRooted.LiebSokal"
label = "Lieb–Sokal theorem for multiaffine polynomials"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.liebSokal"
module = "RealRooted.LiebSokalGeneral"
label = "Lieb–Sokal theorem without the multiaffine hypothesis"
-->

<!-- realrooted-catalog-content -->
# Grace's apolarity theorem

If two polynomials of degree $n$ are apolar and all zeros of one lie in a closed disk or closed
half-plane, then the other has a zero there. Through polarization this gives the
Grace–Walsh–Szegő theorem on symmetric multiaffine polynomials, the basic link between
univariate real-rootedness and multivariate stability, and the Lieb–Sokal theorem.

## Results

For coefficient sequences $a=(a_k)$ and $b=(b_k)$ and $n\ge0$ put
$$
F(z)=\sum_{k=0}^n\binom nk a_kz^k,\qquad G(z)=\sum_{k=0}^n\binom nk b_kz^k ,
$$
so that $F$ is the binomial lift of $f=\sum_ka_kz^k$. We call $F$ and $G$ *apolar* if
$$
\sum_{k=0}^n(-1)^k\binom nk a_kb_{n-k}=0 .
$$
A polynomial in several variables is *stable* if it does not vanish when all variables lie in
the open upper half-plane, and *real stable* if it has real coefficients and is stable.

**Theorem (Grace).** [@Grace1902] Let $F$ and $G$ be apolar polynomials of degree exactly $n$.
If all zeros of $F$ lie in a closed disk $\{z:|z-c|\le r\}$ with $r\ge0$, or in a closed
half-plane $\{z:\operatorname{Im}z\ge b\}$, then $G$ has a zero in the same set.

The *polarization* of a polynomial $p(z)=\sum_{k\le n}p_kz^k$ of degree at most $n$ is the
symmetric multiaffine polynomial
$$
\operatorname{Pol}_n(p)(z_1,\dots,z_n)=\sum_{k=0}^n\binom nk^{-1}p_k\,e_k(z_1,\dots,z_n),
$$
where $e_k$ is the elementary symmetric polynomial; its diagonal $z_1=\dots=z_n=z$ is $p(z)$.

**Theorem (polarization).** If $\deg p\le n$ and $p$ has no zero in the open upper half-plane,
then $\operatorname{Pol}_n(p)$ is stable.

**Theorem (Grace–Walsh–Szegő).** [@Walsh1922; @Szego1922] Let $P\in\mathbb C[z_1,\dots,z_n]$
be symmetric and multiaffine, with diagonal $p(z)=P(z,\dots,z)$. Then
$P=\operatorname{Pol}_n(p)$, and $P$ is stable if and only if $p$ has no zero in the open upper
half-plane. If $P$ has real coefficients, then $P$ is real stable if and only if $p$ is nonzero
and real-rooted.

**Theorem (coincidence).** Let $P\in\mathbb C[z_1,\dots,z_n]$ be symmetric and multiaffine, and
let $C$ be one of the following: an open disk, a closed disk, an open half-plane, a closed
half-plane, or the open or closed exterior of a disk, of radius $r>0$ (for a closed disk,
$r\ge0$). For an exterior we assume that $P(z,\dots,z)$ has degree $n$. Then for all
$\zeta_1,\dots,\zeta_n\in C$ there is $\zeta\in C$ with
$$
P(\zeta_1,\dots,\zeta_n)=P(\zeta,\dots,\zeta).
$$

**Theorem (blockwise polarization).** Let $\sigma$ be finite and let $P\in\mathbb C[z_i:i\in\sigma]$
have degree at most $\kappa_i$ in $z_i$. Replace each $z_i$ by a block of $\kappa_i$ new
variables and polarize $P$ in each block. The resulting multiaffine polynomial is stable if and
only if $P$ is stable.

**Theorem (Lieb–Sokal).** [@LiebSokal1981] Let $F$ and $G$ be stable polynomials in
$\mathbb C[z_1,\dots,z_m]$. Then $F(-\partial)\,G$, obtained by substituting $-\partial/\partial
z_i$ for $z_i$ in $F$ and applying the result to $G$, is zero or stable. This holds for
multiaffine $F,G$ and, with the blockwise polarization above, for arbitrary degrees.

## Proof

We prove Grace's theorem by induction on $n$: by
[Laguerre's theorem](rr:laguerre-polar-derivative), the polar derivative of $F$ lowers the
degree by one and keeps the zeros in the disk or half-plane. For polarization,
$\operatorname{Pol}_n(p)(z)=0$ says that $p$ is apolar to $\prod_i(w-z_i)$; since the zeros of
$p$ lie in the closed lower half-plane, Grace's theorem puts some $z_i$ there as well. The
coincidence theorem for the upper half-plane follows by applying this to $P-P(\zeta)$, and the
other regions follow by Möbius maps.

## References

The classical sources are [@Grace1902; @Walsh1922; @Szego1922] and
[@RahmanSchmeisser2002]. See also [@LiebSokal1981; @BorceaBranden2009II;
@GribinskiMarcus2022, Thm. 2.4], as well as
[apolar polynomials](sf:apolarPolynomial) and
[polarization](sf:polarizationDefinition) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes Grace's theorem for closed disks and closed upper
half-planes, univariate and blockwise polarization, the Grace–Walsh–Szegő
characterization of stable symmetric multiaffine polynomials, and the
multiaffine and general Lieb–Sokal theorems. The proofs live in `RealRooted.Apolarity`,
`RealRooted.GraceHalfPlane`, `RealRooted.Polarization`,
`RealRooted.BorceaBranden.Applications.PolarizationIff` and
`RealRooted.LiebSokal`.
-/
