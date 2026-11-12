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
authors = []
references = []
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

Rows of a Chebyshev-type generating function with a small signed perturbation of the
denominator are real-rooted and interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
For real $c_2,\dots,c_s$ define monic polynomials $P_n(t)$ of degree $n$ by
$$
\sum_{n\ge0}P_n(t)\,z^n=\frac1{1-tz+z^2+\sum_{j=2}^sc_jz^{j+1}} .
$$
For $c=0$ these are the Chebyshev polynomials of the second kind in the variable $t=2\cos\theta$.
For $R>0$ put
$$
A(R)=\sum_{j=2}^s j\,|c_j|\,R^{j+1},\qquad B(R)=\sum_{j=2}^s j(j-1)\,|c_j|\,R^{j+1}.
$$

**Theorem.** Let $R>0$ with $A(R)\le R^2-1$ and $B(R)\le1$. Then every $P_n$ is real-rooted with
simple roots, $P_n\ll P_{n+1}$, and $P_n,P_{n+1}$ have no common root. The $c_j$ may have either
sign.

**Corollary (bandwidth criterion).** Let $s\ge2$. If
$$
\sum_{j=2}^s j\,|c_j|\le\frac1s\Bigl(1-\frac1s\Bigr)^{(s-1)/2},
$$
then $P_n\ll P_{n+1}$ for all $n$.

## Proof

With $b(z)=z^{-1}+z+\sum_jc_jz^j$, the real values of $b$ along the curve
$\operatorname{Im}b(\rho e^{i\theta})=0$ are strictly decreasing in the angle $\theta\in(0,\pi)$
under the two hypotheses.

## References

No published source.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz.SignedPerturbation`
modules named in the metadata.
-/
