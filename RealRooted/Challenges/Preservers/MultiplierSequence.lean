module

import RealRooted.BorceaBranden.Applications.BidiagonalSymbol.RealConsequences
import RealRooted.MultiplierSequence.Bidiagonal.Jensen.Contraction
import RealRooted.JensenPencilContraction
import RealRooted.JensenPencilPositiveContraction
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.MultiplierSequence.Laguerre
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.Sign
import RealRooted.MultiplierSequence.ProperPosition
import RealRooted.RootLocation.BernsteinDiagonal

/-!
# Multiplier sequences

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "multiplier-sequences"
formalized = "2026-09-07"
tags = []
references = [
  "SchurPolya1914",
  "KostovShapiro2006",
]
authors = ["Pólya", "Schur", "Kostov", "Shapiro"]
years = [1914]

[[definitions]]
name = "RealRooted.diagonalOperator"
module = "RealRooted.MultiplierSequence"
label = "Diagonal operator of a sequence"

[[definitions]]
name = "RealRooted.jensenPolynomial"
module = "RealRooted.MultiplierSequence"
label = "Jensen polynomials"

[[definitions]]
name = "RealRooted.IsFiniteMultiplierSequence"
module = "RealRooted.MultiplierSequence"
label = "Finite multiplier sequence"

[[definitions]]
name = "RealRooted.IsMultiplierSequence"
module = "RealRooted.MultiplierSequence.Infinite"
label = "Multiplier sequence"

[[definitions]]
name = "RealRooted.IsFinitePFMultiplierSequence"
module = "RealRooted.MultiplierSequence"
label = "Finite PF multiplier sequence"

[[definitions]]
name = "RealRooted.IsPFMultiplierSequence"
module = "RealRooted.MultiplierSequence.Infinite"
label = "PF multiplier sequence"

[[definitions]]
name = "RealRooted.complexExpGeneratingFunction"
module = "RealRooted.MultiplierSequence.PolyaSchur.Analytic"
label = "Exponential generating function"

[[definitions]]
name = "RealRooted.IsLaguerrePolyaTypeI"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI"
label = "Laguerre–Pólya class of type I"

[[definitions]]
name = "RealRooted.IsLaguerrePolyaTypeISigned"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned"
label = "Type I up to the signs ±f(±z)"

[[definitions]]
name = "RealRooted.BidiagonalPFPreserver"
module = "RealRooted.MultiplierSequence.Bidiagonal"
label = "A bidiagonal operator preserving PF polynomials of degree at most d"

[[definitions]]
name = "RealRooted.BidiagonalJensenPencilCertificate"
module = "RealRooted.MultiplierSequence.Bidiagonal.Jensen"
label = "Jensen-pencil certificate"

[[theorems]]
name = "RealRooted.isMultiplierSequence_iff_jensenPolynomial_isPF"
module = "RealRooted.MultiplierSequence.PolyaSchur"
label = "Pólya–Schur: multiplier sequences via Jensen polynomials"

[[theorems]]
name = "RealRooted.IsPFMultiplierSequence.iff_laguerrePolya_egf"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse"
label = "Pólya–Schur: PF multiplier sequences are the Laguerre–Pólya type I class"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.iff_signedLaguerrePolya_egf"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned"
label = "Pólya–Schur: classification of all multiplier sequences"
headline = true

[[theorems]]
name = "RealRooted.IsMultiplierSequence.exists_pf_sign_normalization"
module = "RealRooted.MultiplierSequence.Sign"
label = "Every multiplier sequence is a PF one up to signs"

[[theorems]]
name = "RealRooted.IsPFMultiplierSequence.logConcave"
module = "RealRooted.MultiplierSequence.PolyaSchur"
label = "PF multiplier sequences are log-concave"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_inv_ascPochhammer"
module = "RealRooted.MultiplierSequence.InvPochhammer"
label = "Reciprocal rising factorials 1/(α)ₖ form a PF multiplier sequence"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_inv_factorial"
module = "RealRooted.MultiplierSequence.InvPochhammer"
label = "1/k! is a PF multiplier sequence"

[[theorems]]
name = "RealRooted.isMultiplierSequence_eval_of_roots_nonpos"
module = "RealRooted.MultiplierSequence.Laguerre"
label = "Laguerre's theorem: φ(0), φ(1), … is a multiplier sequence"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_eval_of_roots_nonpos"
module = "RealRooted.MultiplierSequence.Laguerre"
label = "Laguerre's theorem in the PF convention"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_natCast_add"
module = "RealRooted.MultiplierSequence.Laguerre"
label = "k + r is a PF multiplier sequence for r ≥ 0"

[[theorems]]
name = "RealRooted.IsLaguerrePolyaTypeI.isPFMultiplierSequence_eval_natCast"
module = "RealRooted.MultiplierSequence.Laguerre"
label = "Type I functions sampled at 0, 1, 2, … are PF multiplier sequences"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.taylorDifferentialOperator_eq_zero_or_splits"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator"
label = "Laguerre–Pólya: φ(D) preserves real-rootedness"

[[theorems]]
name = "RealRooted.taylorDifferentialOperator_exp_neg_mul_sq_eq_zero_or_splits"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow"
label = "The heat operator exp(−aD²) preserves real-rootedness"

[[theorems]]
name = "RealRooted.BorceaBranden.bidiagonalPFPreserver_of_affineSymbol"
module = "RealRooted.BorceaBranden.Applications.BidiagonalSymbol.RealConsequences"
label = "Bidiagonal PF preservers from a stable symbol"

[[theorems]]
name = "RealRooted.BidiagonalJensenPencilCertificate.toPFPreserver"
module = "RealRooted.MultiplierSequence.Bidiagonal.Jensen.Contraction"
label = "Bidiagonal PF preservers from a Jensen-pencil certificate"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.strictInterl_diagonalOperator_of_pos"
module = "RealRooted.MultiplierSequence.ProperPosition"
label = "A positive multiplier sequence preserves interlacing"

[[theorems]]
name = "RealRooted.compatible_schurSzego_jensen_of_pos_coeff_zero"
module = "RealRooted.JensenPencilPositiveContraction"
label = "Schur–Szegő composition preserves Jensen-pencil compatibility, positive constant terms"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.compatible_jensen_translate"
module = "RealRooted.JensenPencilContraction"
label = "Positive translation preserves Jensen-pencil compatibility"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.of_continuous_curve"
module = "RealRooted.JensenPencilContraction"
label = "A coefficientwise continuous curve of PF sequences has a PF endpoint"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Compatible.schurSzegoComp_jensenPencil"
module = "RealRooted.JensenPencilContraction"
label = "Schur–Szegő composition by a PF polynomial preserves Jensen-pencil compatibility"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.bernsteinDiagonal"
module = "RealRooted.RootLocation.BernsteinDiagonal"
label = "The Bernstein-diagonal map L(B_k) = γ_k B_k on [−1, 0]"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.bernsteinDiagonal_maps_iff"
module = "RealRooted.RootLocation.BernsteinDiagonal"
label = "A Bernstein-diagonal map preserves [−1, 0]-rooted polynomials iff its symbol does"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.bernsteinDiagonal_ne_zero_iff"
module = "RealRooted.RootLocation.BernsteinDiagonal"
label = "A Bernstein-diagonal preserver is injective iff the symbol has roots in (−1, 0)"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Multiplier sequences

A real sequence is a multiplier sequence if the diagonal operator it defines preserves
real-rootedness; these are classified by Jensen polynomials and by the Laguerre–Pólya class.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A polynomial is *real-rooted* if it is zero or splits over $\mathbb R$, and *PF* (Pólya
frequency) if it is zero or has nonnegative coefficients and only real, nonpositive roots. For a
real sequence $\gamma=(\gamma_0,\gamma_1,\dots)$ the *diagonal operator* is
$$
a_0+a_1x+\dots+a_nx^n\ \mapsto\ \gamma_0a_0+\gamma_1a_1x+\dots+\gamma_na_nx^n .
$$
The sequence $\gamma$ is a *multiplier sequence* if this operator maps every real-rooted
polynomial to a real-rooted polynomial, and a *PF multiplier sequence* if it maps every PF
polynomial to a PF polynomial. The *finite* versions restrict to inputs of degree at most $n$.
The *Jensen polynomial* of $\gamma$ is $g_n(x)=\sum_k\binom nk\gamma_kx^k$.

**Theorem (Pólya--Schur).** Let $\gamma_k\ge0$ for all $k$. Then $\gamma$ is a multiplier
sequence if and only if every Jensen polynomial $g_n$ is PF.

**Theorem (Laguerre--Pólya classification).** Assume $\sum_k|\gamma_k|R^k/k!<\infty$ for some
$R>0$, and let $f(z)=\sum_k\gamma_kz^k/k!$.

- $\gamma$ is a PF multiplier sequence if and only if $f$ is in the
  [Laguerre--Pólya class](/RealRooted/concepts/laguerre-polya-class/) of type I, that is, a
  locally uniform limit of PF polynomials.
- $\gamma$ is a multiplier sequence if and only if one of $f(z)$, $-f(z)$, $f(-z)$, $-f(-z)$ is
  of type I.

Every multiplier sequence $\gamma$ satisfies one of the following: $\gamma$, $-\gamma$,
$\bigl((-1)^k\gamma_k\bigr)$ or $\bigl(-(-1)^k\gamma_k\bigr)$ is a PF multiplier sequence.

**Theorem (log-concavity).** If $\gamma$ is a PF multiplier sequence, then
$\gamma_k\gamma_{k+2}\le\gamma_{k+1}^2$ for all $k$.

**Theorem (Laguerre).** Let $\varphi$ be a real-rooted polynomial with only nonpositive roots.
Then $\varphi(0),\varphi(1),\varphi(2),\dots$ is a multiplier sequence, and a PF multiplier
sequence if $\varphi$ has nonnegative leading coefficient. In particular $k+r$ is a PF
multiplier sequence for every real $r\ge0$. More generally, if $f$ is of type I, then
$\bigl(\operatorname{Re}f(k)\bigr)_{k\ge0}$ is a PF multiplier sequence.

**Theorem (examples).** For real $\alpha>0$, the sequence $1/(\alpha)_k$, with
$(\alpha)_k=\alpha(\alpha+1)\cdots(\alpha+k-1)$, is a PF multiplier sequence. In particular
$1/k!$ is one.

**Theorem (operators).** If $\varphi$ is Laguerre--Pólya and $g$ is real-rooted, then
$\varphi(D)\,g=\sum_k\operatorname{Re}\bigl(\varphi^{(k)}(0)/k!\bigr)\,g^{(k)}$ is real-rooted.
In particular, for $a\ge0$ the operator $e^{-aD^2}$ maps real-rooted polynomials to
real-rooted polynomials.

**Theorem (interlacing).** If $\gamma$ is a multiplier sequence with $\gamma_k>0$ for all $k$
and $f\ll g$, then $\sum_k\gamma_kf_kx^k\ll\sum_k\gamma_kg_kx^k$.

**Theorem (bidiagonal preservers).** For sequences $\alpha,\beta$, the bidiagonal operator
sends $\sum_ka_kx^k$ to $\sum_k(\alpha_ka_k+\beta_{k-1}a_{k-1})x^k$, with the second term omitted
for $k=0$. It maps PF polynomials of degree at most $d$ to PF polynomials in each of the
following cases:

- its degree-$d$ Borcea--Brändén algebraic symbol is stable, and $\alpha_k,\beta_k\ge0$ for
  $k\le d$;
- with $J_\alpha=\sum_k\binom dk\alpha_kx^k$ and $J_\beta$ defined likewise, the polynomials
  $J_\alpha$, $xJ_\beta$ and $J_\alpha+\lambda xJ_\beta$ are PF for every $\lambda\ge0$.

**Theorem (Jensen-pencil contraction).** Call $(A,B)$ *compatible* if every nonnegative linear
combination of $A$ and $B$ is zero or real-rooted. Let $*_d$ be Schur--Szegő composition (see the
[Hadamard products](/RealRooted/theorems/hadamard-products/) page). Let $A$, $xB$ and $p$ be PF
of degree at most $d$ with $\deg B\le d$, and suppose $(A,xB)$ is compatible. Then
$(A*_dp,\ x\,(B*_dp))$ is compatible. Two ingredients are available separately.

- If $A,B\ne0$ are PF, $(A,xB)$ is compatible and $\varepsilon>0$, then
  $\bigl(A(x+\varepsilon),\ x\,B(x+\varepsilon)\bigr)$ is compatible.
- A coefficientwise continuous curve of PF sequences has a PF endpoint.

**Theorem (Bernstein-diagonal preservers).** Fix $D\ge1$, let $B_k=\binom Dk x^k(1+x)^{D-k}$,
let $\gamma$ be a real sequence, let $L$ be the linear map with $LB_k=\gamma_kB_k$, and put
$g=L\bigl((1+2x)^D\bigr)=\sum_k\gamma_kB_k$. Let $\mathcal C_D$ be the set of polynomials of
degree exactly $D$ with positive leading coefficient and all roots in $[-1,0]$. Then
$$
L(\mathcal C_D)\subseteq\mathcal C_D\cup\{0\}\iff g\in\mathcal C_D\cup\{0\}.
$$
If these hold, then $Lf\ne0$ for all $f\in\mathcal C_D$ if and only if $g$ is real-rooted with
all roots in $(-1,0)$.

## Proof

The Bernstein-diagonal map is conjugate by the Cayley change of variable
$J_Df(z)=(1-z)^Df\bigl(z/(1-z)\bigr)$ to the diagonal operator of $\gamma$, which turns
$B_k$ into $\binom Dkz^k$ and $L$ into Schur--Szegő composition with $J_Dg$, so the statement
follows from [@KostovShapiro2006, Prop. 1.2 and Thm. 1.3].

## References

[@SchurPolya1914], [@KostovShapiro2006]. The finite Pólya--Schur theorem through Schur--Szegő
composition is on the [Hadamard products](/RealRooted/theorems/hadamard-products/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.MultiplierSequence`.
-/
