module

import RealRooted.CoefficientShape
import RealRooted.CoefficientShape.Hoggar
import RealRooted.CoefficientShape.Liggett
import RealRooted.LaguerreSamuelson
import RealRooted.Maclaurin
import RealRooted.Mathlib.Algebra.Polynomial.MeanMode

/-!
# Newton's inequalities and log-concavity

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "newton-maclaurin"
formalized = "2026-10-07"
references = [
  "Gurvits2009",
]
authors = ["Newton", "Maclaurin", "Laguerre", "Darroch", "Samuelson", "Hoggar", "Liggett"]
years = [1707, 1729, 1880, 1964, 1968, 1974, 1997]

[[definitions]]
name = "RealRooted.CoeffUltraLogConcaveUpTo"
module = "RealRooted.CoefficientShape"
label = "Ultra-log-concavity of order d"

[[theorems]]
name = "RealRooted.hasUltraLogConcaveCoeffs_of_eq_zero_or_splits"
module = "RealRooted.CoefficientShape"
label = "Newton's inequalities for the coefficients of a real-rooted polynomial"
headline = true
symcat = "newtonInequalities"

[[theorems]]
name = "NewtonAux.newton_esymm_ineq"
module = "RealRooted.NewtonAux"
label = "Newton's inequalities for elementary symmetric functions"

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_of_natDegree_le"
module = "RealRooted.CoefficientShape"
label = "A real-rooted polynomial of degree at most n is ultra-log-concave of order n"

[[theorems]]
name = "RealRooted.hasLogConcaveCoeffs_of_eq_zero_or_splits"
module = "RealRooted.CoefficientShape"
label = "A real-rooted polynomial has log-concave coefficients"

[[theorems]]
name = "RealRooted.Maclaurin.esymm_div_choose_rpow_le"
module = "RealRooted.Maclaurin"
label = "Maclaurin: $E_1 ≥ E_2^{1/2} ≥ ⋯ ≥ E_n^{1/n}$ for nonnegative reals"

[[theorems]]
name = "RealRooted.Samuelson.sq_add_coeff_div_le"
module = "RealRooted.LaguerreSamuelson"
label = "Laguerre: the roots are bounded by the two top coefficients"

[[theorems]]
name = "RealRooted.Samuelson.abs_sub_mean_le"
module = "RealRooted.LaguerreSamuelson"
label = "Samuelson: each of n reals lies within √(n − 1) standard deviations of the mean"

[[theorems]]
name = "Polynomial.abs_sub_lt_one_of_isMode"
module = "RealRooted.Mathlib.Algebra.Polynomial.MeanMode"
label = "Darroch: a real-rooted p with nonnegative coefficients has its mode within 1 of the mean"

[[theorems]]
name = "RealRooted.coeffLogConcaveUpTo_mul"
module = "RealRooted.CoefficientShape.Hoggar"
label = "Hoggar: log-concavity without internal zeros is closed under products"

[[theorems]]
name = "RealRooted.coeffNoInternalZerosUpTo_mul"
module = "RealRooted.CoefficientShape.Hoggar"
label = "Products of polynomials without internal zeros have no internal zeros"

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_mul"
module = "RealRooted.CoefficientShape.Liggett"
label = "Liggett: ultra-log-concavity without internal zeros is closed under products"
-->

<!-- realrooted-catalog-content -->
# Newton's inequalities and log-concavity

The coefficients of a real-rooted polynomial satisfy Newton's inequalities; in particular they
are log-concave. Hoggar and Liggett showed that log-concavity and ultra-log-concavity of
coefficients are preserved under products. Related inequalities of Maclaurin, Laguerre,
Samuelson and Darroch bound symmetric means, roots and the mode.

## Results

A nonnegative sequence $a_0,\dotsc,a_d$ is *log-concave* if $a_{k-1}a_{k+1}\le a_k^2$ for
$0<k<d$, *ultra-log-concave of order $d$* if $a_k/\binom dk$ is log-concave, and has *no
internal zeros* if $a_ia_k\ne0$ and $i<j<k$ imply $a_j\ne0$. For reals $x_1,\dotsc,x_n$ let
$e_k$ be their elementary symmetric functions and $E_k=e_k/\binom nk$.

**Theorem (Newton).** $E_{k-1}E_{k+1}\le E_k^2$ for $0<k<n$. Equivalently, if
$p=\sum_kp_kx^k$ is real-rooted and $\deg p\le n$, then
$$
(k+1)(n-k+1)\,p_{k-1}p_{k+1}\le k(n-k)\,p_k^2\qquad(0<k<n).
$$
In particular the coefficients of a real-rooted polynomial are log-concave, and if they are
nonnegative they are ultra-log-concave of order $\deg p$.

**Theorem (Maclaurin).** If all $x_i\ge0$, then $E_1\ge E_2^{1/2}\ge\dotsb\ge E_n^{1/n}$.

**Theorem (Laguerre's root bound).** If $n\ge2$ and $x^n+ax^{n-1}+bx^{n-2}+\dotsb$ is
real-rooted, every root $r$ satisfies
$$
\Bigl(r+\frac an\Bigr)^2\le\frac{n-1}n\Bigl(\frac{n-1}na^2-2b\Bigr).
$$

**Theorem (Samuelson).** Every $x_j$ lies within $\sqrt{n-1}\,s$ of the mean $\mu$, where
$s^2=\frac1n\sum_i(x_i-\mu)^2$.

**Theorem (Darroch).** Let $p\ne0$ be real-rooted with nonnegative coefficients and
$\mu=p'(1)/p(1)$. Every index $k$ at which $p_k$ is maximal satisfies $|k-\mu|<1$.

**Theorem (Hoggar).** If $p$ and $q$ have nonnegative log-concave coefficients without internal
zeros, so does $pq$.

**Theorem (Liggett).** If $p$ and $q$ have nonnegative coefficients without internal zeros that
are ultra-log-concave of orders $\deg p$ and $\deg q$, then the coefficients of $pq$ are
ultra-log-concave of order $\deg p+\deg q$.

Both product theorems need the hypothesis on internal zeros: $1+x^3$ and $1+x$ have log-concave
coefficients, but $(1+x^3)(1+x)=1+x+x^3+x^4$ does not.

## Use

Real-rootedness is the usual way to prove that a combinatorial sequence is log-concave and
unimodal, and Darroch's theorem then locates its mode. Hoggar's and Liggett's theorems give
log-concavity for products where real-rootedness is not available.

## Proof

Newton's inequalities for a real-rooted polynomial reduce to quadratics: by Rolle's theorem,
repeated differentiation and reversal preserve real-rootedness, and they bring any three
consecutive coefficients to a real-rooted quadratic, whose discriminant is nonnegative. Hoggar's
theorem uses that log-concave sequences without internal zeros satisfy
$a_ia_{j+1}\le a_{i+1}a_j$ for $i\le j$, together with the $2\times2$ Cauchy–Binet identity.
Liggett's theorem is proved by induction on the order, splitting the sequence into two
ultra-log-concave pieces.

## References

I. Newton, *Arithmetica Universalis* (1707); C. Maclaurin, “A second letter to Martin
Folkes,” *Philosophical Transactions* 36 (1729); E. Laguerre, “Sur une méthode pour obtenir
par approximation les racines d'une équation algébrique qui a toutes ses racines réelles,”
*Nouvelles Annales de Mathématiques* (1880); J. N. Darroch, “On the distribution of the number
of successes in independent trials,” *Ann. Math. Statist.* 35 (1964), 1317–1321;
P. A. Samuelson, “How deviant can you be?”, *J. Amer. Statist. Assoc.* 63 (1968), 1522–1525;
S. G. Hoggar, “Chromatic polynomials and logarithmic concavity,” *J. Combin. Theory Ser. B* 16
(1974), 248–254; T. M. Liggett, “Ultra logconcave sequences and negative dependence,”
*J. Combin. Theory Ser. A* 79 (1997), 315–325; [@Gurvits2009] for a proof of Liggett's theorem
by mixed volumes. See also [Newton's inequalities](sf:newtonInequalities) and
[log-concave polynomials](sf:logConcavePolynomial) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
