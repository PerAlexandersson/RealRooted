module

public import RealRooted.BorceaBranden.MultivariateHKO
public import RealRooted.BorceaBranden.RealHKOConverse
public import RealRooted.MultivariateStability.AllCombo

/-!
# Multivariate Hermite–Kakeya–Obreschkoff theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "multivariate-obreschkoff"
formalized = "2026-10-13"
references = [
  "BorceaBranden2009I",
  "BorceaBranden2010",
  "Obreschkoff1963",
]
authors = ["Obreschkoff", "Borcea", "Brändén"]
years = [1963, 2009, 2010]

[[definitions]]
name = "RealRooted.MvProperPosition"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Proper position F ≪ G"

[[definitions]]
name = "RealRooted.MvStablePencil"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Stable affine pencil G + wF"

[[definitions]]
name = "RealRooted.AllComboMvRealStableOrZero"
module = "RealRooted.MultivariateStability.AllCombo"
label = "Every real combination is real stable or zero"

[[theorems]]
name = "RealRooted.AllComboMvRealStableOrZero.eq_zero_or_properPosition"
module = "RealRooted.BorceaBranden.RealHKOConverse"
label = "Hermite–Kakeya–Obreschkoff converse: a stable real span gives proper position"
headline = true

[[theorems]]
name = "RealRooted.MvProperPosition.allComboMvRealStableOrZero"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Hermite–Kakeya–Obreschkoff: proper position gives a stable real span"
headline = true

[[theorems]]
name = "RealRooted.mvProperPosition_iff_mvStablePencil"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Proper position is stability of the affine pencil G + wF"
-->

<!-- realrooted-catalog-content -->
# Multivariate Hermite–Kakeya–Obreschkoff theorem

A polynomial $P \in \mathbb C[z_i : i \in \sigma]$ is **stable** if
$P(z) \neq 0$ whenever every $z_i$ lies in the open upper half-plane. A polynomial
with real coefficients is **real stable** if it is stable when regarded as a complex
polynomial; in particular it is nonzero.

For $F, G \in \mathbb R[z_i : i \in \sigma]$ we say that $F$ and $G$ are in
**proper position**, written $F \ll G$, if the complex polynomial $G + iF$ is stable.

**Theorem** (Hermite–Kakeya–Obreschkoff, converse). [@Obreschkoff1963] Let
$\sigma$ be any index type and
$F, G \in \mathbb R[z_i : i \in \sigma]$. Suppose that for all real $\alpha, \beta$ the
polynomial $\alpha F + \beta G$ is zero or real stable. Then $F = G = 0$, or
$F \ll G$, or $G \ll F$.

**Theorem** (Hermite–Kakeya–Obreschkoff). Let $\sigma$ be finite and
$F, G \in \mathbb R[z_i : i \in \sigma]$ with $F \ll G$. Then for all real
$\alpha, \beta$ the polynomial $\alpha F + \beta G$ is zero or real stable.

The forward direction goes through the affine pencil. Adjoin a new variable $w$.

**Theorem.** For $\sigma$ arbitrary, $F \ll G$ if and only if the polynomial $G + wF$,
in the variables $z_i$ and $w$, is real stable.

The theorems are the multivariate analogues of the classical Hermite–Kakeya–Obreschkoff
theorem for interlacing polynomials; see the [univariate Obreschkoff
page](/RealRooted/theorems/obreschkoff/). Proper position is the multivariate counterpart of
interlacing through the Hermite–Biehler theorem; see the
[Hermite–Biehler page](/RealRooted/theorems/hermite-biehler-hurwitz/).

## Proof idea

For the equivalence with the pencil, restrict $G + iF$ to a line $z_i = a_i + b_i t$ with
$b_i > 0$, which turns proper position into a univariate Hermite–Biehler statement in $t$.
A norm comparison between a point and its complex conjugate then shows that the pencil
$G + wF$ is stable. Conversely, substituting $w = i$ gives $G + iF$. A stable pencil
yields the combinations $\alpha F + \beta G$ by specializing $w$ and, for the
direction polynomial $F$, differentiating in $w$; this is where finiteness of $\sigma$ is used.

For the converse, the cases $G = 0$ and $F = cG$ are direct. Otherwise, for every point $z$
with all $\operatorname{Im} z_i > 0$, the quotient $F(z)/G(z)$ is not real, since a real
value $c$ would make $F - cG$, which is real stable, vanish at $z$. The set of such points
is connected, so $\operatorname{Im}(F/G)$ has constant sign. A positive sign makes
$G + iF$ stable and a negative sign makes $F + iG$ stable.

## References

See [@BorceaBranden2009I, Lemma 1.8 and Thm. 1.9],
[@BorceaBranden2010], and [@Obreschkoff1963].
<!-- /realrooted-catalog-content -->

This module exposes the two directions of the multivariate Hermite–Kakeya–Obreschkoff
theorem and the pencil reformulation. The proofs live in
`RealRooted.BorceaBranden.MultivariateHKO` and `RealRooted.BorceaBranden.RealHKOConverse`.
-/

@[expose] public section
