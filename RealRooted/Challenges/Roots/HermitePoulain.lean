module

public import RealRooted.Hermite.BesselOperatorFamily
public import RealRooted.Hermite.ImaginaryCentralDifference
public import RealRooted.Hermite.Poulain
public import RealRooted.Hermite.PoulainInterlacing
public import RealRooted.Hermite.PoulainSymbolInterlacing
public import RealRooted.IteratedDerivativeShift

/-!
# Hermite–Poulain theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "hermite-poulain"
formalized = "2026-07-18"
references = [
  "SchurPolya1914",
  "Obreschkoff1963",
  "Levin1964",
]
authors = ["Hermite", "Poulain"]

[[definitions]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator"
module = "RealRooted.Hermite.Poulain"
label = "The operator f(D)"

[[definitions]]
name = "RealRooted.besselOperator"
module = "RealRooted.Hermite.BesselOperatorFamily"
label = 'The finite Bessel operator $∑_k (-λ)^k D^{2k+r} / (k!\,(k+r)!)$'

[[definitions]]
name = "RealRooted.imaginaryCentralDifference"
module = "RealRooted.Hermite.ImaginaryCentralDifference"
label = "The imaginary central difference (p(z + ih) - p(z - ih)) / (2ih)"

[[theorems]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator_eq_zero_or_splits"
module = "RealRooted.Hermite.Poulain"
label = "Hermite–Poulain: f(D) preserves real-rootedness when f is real-rooted"
headline = true
symcat = "hermitePoulainTheorem"

[[theorems]]
name = "RealRooted.HermitePoulain.interl_or_interl_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainInterlacing"
label = "Hermite–Poulain operators preserve interlacing"

[[theorems]]
name = "RealRooted.HermitePoulain.eq_zero_pair_or_stablePencil_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainSymbolInterlacing"
label = "Symbols in proper position give images in reversed proper position"

[[theorems]]
name = "RealRooted.splits_tDeriv_all"
module = "RealRooted.IteratedDerivativeShift"
label = "p − εp′ is real-rooted for every real ε when p is"

[[theorems]]
name = "RealRooted.strictInterl_tDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "p ≪ p − εp′ for ε > 0"

[[theorems]]
name = "RealRooted.hasSimpleRoots_iterateTDeriv_of_natDegree"
module = "RealRooted.IteratedDerivativeShift"
label = "deg p iterations of p ↦ p − εp′, ε > 0, give simple roots"

[[theorems]]
name = "RealRooted.nonneg_iff_forall_besselOperator_splits"
module = "RealRooted.Hermite.BesselOperatorFamily"
label = "The Bessel operator preserves real-rootedness exactly when λ ≥ 0"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.isSimpleRealRooted_imaginaryCentralDifference"
module = "RealRooted.Hermite.ImaginaryCentralDifference"
label = "The imaginary central difference of a real-rooted polynomial has simple real roots"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Hermite–Poulain theorem

If $f$ is real-rooted, the differential operator $f(D)$ maps real-rooted polynomials to
real-rooted polynomials and preserves interlacing. The shift $p\mapsto p-\varepsilon p'$, the
finite Bessel operators and imaginary central differences are instances; the first is the
standard way to perturb a real-rooted polynomial into one with simple roots.

## Results

For $f(x)=\sum_ka_kx^k$ let $f(D)=\sum_ka_kD^k$ with $D=d/dx$.

**Theorem (Hermite–Poulain).** [@Obreschkoff1963; @Levin1964] If $f$ and $p$ are nonzero and
real-rooted, then $f(D)\,p$ is zero or real-rooted.

**Corollary (interlacing).** Let $f$ be nonzero and real-rooted and let $g\ll h$. Then
$f(D)g\ll f(D)h$ or $f(D)h\ll f(D)g$, where $0$ interlaces every polynomial.

**Theorem (symbols in proper position).** Let $T$ be real-rooted, and let $P,Q$ be real
polynomials such that $Q(x)+yP(x)$ is real stable. Then either $P(D)T=Q(D)T=0$ or
$P(D)T+yQ(D)T$ is real stable.

**Corollary (derivative shifts).** [@SchurPolya1914; @Obreschkoff1963] Let $p\ne0$ be
real-rooted and $T_\varepsilon p=p-\varepsilon p'$. Then $T_\varepsilon p$ is real-rooted for
every real $\varepsilon$. If $\varepsilon>0$, then $p\ll T_\varepsilon p$, and
$T_\varepsilon^{\deg p}p$ has only simple roots.

**Corollary (Bessel operators).** For $\lambda\in\mathbb R$ and $r\in\mathbb N$ let
$$
B_{\lambda,r}=\sum_{k\ge0}\frac{(-\lambda)^k}{k!\,(k+r)!}\,D^{2k+r}.
$$
For every $r$, the operator $B_{\lambda,r}$ maps real-rooted polynomials to zero or real-rooted
polynomials if and only if $\lambda\ge0$.

**Corollary (imaginary central differences).** For $h>0$ and a real-rooted polynomial $p$ of
degree at least one,
$$
\delta_hp(z)=\frac{p(z+ih)-p(z-ih)}{2ih}=\sum_{k\ge0}\frac{(-1)^kh^{2k}}{(2k+1)!}\,p^{(2k+1)}(z)
$$
is real-rooted with only simple roots.

## Use

The symbols of $B_{\lambda,r}$ and $\delta_h$ are, up to scaling, the Bessel function
$J_r(2\sqrt\lambda\,x)$ and $\sin(hx)/h$; they are entire functions in the
[Laguerre–Pólya class](rr:laguerre-polya-class), for which $\varphi(D)$ still preserves
real-rootedness. Interlacing preservers of this kind are classified on the
[operator preservers](rr:operator-preservers) page.

## Proof

Write $f$ as a product of linear factors. Each factor gives
$(D-a)p=e^{ax}\frac{d}{dx}\bigl(e^{-ax}p\bigr)$, and by Rolle's theorem $e^{-ax}p$ has a
critical point between consecutive roots of $p$ and, if $a\ne0$, one beyond the extreme root,
so $(D-a)p$ is real-rooted.
The central difference is real-rooted with simple roots by the
[Hermite–Biehler theorem](rr:hermite-biehler-hurwitz).

## References

The theorem goes back to Hermite and Poulain; see [@Obreschkoff1963; @Levin1964] and
[@SchurPolya1914]. See also the [Hermite–Poulain theorem](sf:hermitePoulainTheorem) and its
[interlacing consequence](sf:hermitePoulainInterlacing) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Challenges.HermitePoulain

export RealRooted.HermitePoulain (applyAsDifferentialOperator)

end RealRooted.Challenges.HermitePoulain

@[deprecated (since := "2026-11-12")]
alias RealRooted.Challenges.HermitePoulain.differential_operator_preserves_real_rooted :=
  RealRooted.HermitePoulain.applyAsDifferentialOperator_eq_zero_or_splits
