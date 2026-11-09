module

import RealRooted.Toeplitz.SignedPerturbation
import RealRooted.Toeplitz.SignedPerturbation.Curve
import RealRooted.Toeplitz.SignedPerturbation.Rows

/-!
# Signed Toeplitz perturbations of the Chebyshev rows

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "signed-toeplitz-perturbations"
formalized = "2026-11-09"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.ToeplitzPerturbation.denominator"
module = "RealRooted.Toeplitz.SignedPerturbation.Rows"
label = "The denominator 1 - t z + z² + ∑ c_j z^(j+1) as a series with polynomial coefficients"

[[definitions]]
name = "RealRooted.ToeplitzPerturbation.row"
module = "RealRooted.Toeplitz.SignedPerturbation.Rows"
label = "The rows P_n, the coefficients of the reciprocal of the denominator"

[[definitions]]
name = "RealRooted.ToeplitzPerturbation.perturbationA"
module = "RealRooted.Toeplitz.SignedPerturbation.Rows"
label = "A(R) = ∑ j |c_j| R^(j+1)"

[[definitions]]
name = "RealRooted.ToeplitzPerturbation.perturbationB"
module = "RealRooted.Toeplitz.SignedPerturbation.Rows"
label = "B(R) = ∑ j (j - 1) |c_j| R^(j+1)"

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.strictInterl_row_succ"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "If A(R) ≤ R² - 1 and B(R) ≤ 1, consecutive rows strictly interlace"
headline = true

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.hasSimpleRoots_row"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "Every row has only simple roots"
headline = true

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.splits_row"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "Every row is real-rooted"

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.eval_row_ne_zero_of_isRoot_row_succ"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "Consecutive rows have no common root"

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.strictInterl_row_succ_of_sum_le"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "The bandwidth criterion ∑ j |c_j| ≤ (1/s)(1 - 1/s)^((s-1)/2) suffices"
headline = true

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.isMonicOfDegree_row"
module = "RealRooted.Toeplitz.SignedPerturbation.Rows"
label = "The row P_n is monic of degree n"

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.strictAntiOn_reB_rho"
module = "RealRooted.Toeplitz.SignedPerturbation.Curve"
label = "The real values of b along the curve Im b = 0 are strictly decreasing in the angle"
-->

<!-- realrooted-catalog-content -->
# Signed Toeplitz perturbations of the Chebyshev rows

For real $c_2,\dots,c_s$ with $s\ge2$ define monic polynomials $P_n(t)$ by
$$
\sum_{n\ge0}P_n(t)\,z^n=\frac1{1-tz+z^2+\sum_{j=2}^sc_jz^{j+1}} .
$$
For $c=0$ these are the Chebyshev polynomials of the second kind (in the variable
$t=2\cos\theta$). For $R>1$ put
$$
A(R)=\sum_{j=2}^s j\,|c_j|\,R^{j+1},\qquad B(R)=\sum_{j=2}^s j(j-1)\,|c_j|\,R^{j+1}.
$$

**Theorem.** If $A(R)\le R^2-1$ and $B(R)\le1$, then every row $P_n$ has only real
roots, all simple, and consecutive rows $P_n,P_{n+1}$ strictly interlace and have no common
root. The coefficients may have either sign, and equality in the hypotheses is allowed. In
particular this holds whenever
$$
\sum_{j=2}^s j\,|c_j|\le\frac1s\Bigl(1-\frac1s\Bigr)^{(s-1)/2}.
$$

**Proof idea.** Put $b(z)=z^{-1}+z+\sum_jc_jz^j$. Under the two hypotheses, for every angle
$\theta\in(0,\pi)$ there is a unique $\rho(\theta)\in(0,R]$ with
$\operatorname{Im}b(\rho e^{i\theta})=0$,
and $\lambda(\theta)=b(\rho(\theta)e^{i\theta})$ is real and strictly decreasing in $\theta$
(an implicit-function computation, $\lambda'=-\rho(a^2+b_1^2)/b_1<0$). At such a point the
rescaled denominator factors exactly as $(1-2\cos\theta\,z+z^2)\,C_\theta(z)$, where
$C_\theta-1$ has coefficient $\ell^1$-norm at most $1/2$ because $B(R)\le1$. The reciprocal
of $C_\theta$ then has $\sum_{k=1}^n|g_k|\le1-2^{-n}$, so
$\rho^nP_n(\lambda(\theta))=\sum_k g_k\,U_{n-k}(\cos\theta)$ has the sign pattern of
$\sin((n+1)\theta)$ at the grid angles $(2j+1)\pi/(2(n+1))$; this is where equality in the
hypotheses is harmless, since the finite sums are strictly positive. The intermediate value
theorem gives $n$ simple real roots, one in each grid interval, and at these roots
$P_{n-1}$ alternates in sign, which gives strict interlacing. No limiting spectrum and no
finite verified prefix are used.

## What is new

The proof is new, developed for RealRooted (issue #2486), and is of independent research
interest; no published source is cited, and we attribute none. The only external inputs are
classical: the Chebyshev polynomials of the second kind and the implicit function theorem.

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz.SignedPerturbation`
modules named in the metadata.
-/
