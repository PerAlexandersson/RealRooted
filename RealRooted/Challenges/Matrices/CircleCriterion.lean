module

public import RealRooted.Toeplitz.CircleCriterion

/-!
# Circle criterion for Hessenberg Toeplitz matrices

<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "hessenberg-circle-criterion"
formalized = "2026-11-13"
authors = ["Shapiro", "Štampach"]
years = [2017]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.Toeplitz.Circle.row"
module = "RealRooted.Toeplitz.CircleCriterion"
label = '$P_n = \det(tI - T_n)$ for the Toeplitz Hessenberg sections of $b$'

[[definitions]]
name = "RealRooted.Toeplitz.Circle.CircleNonneg"
module = "RealRooted.Toeplitz.CircleCriterion"
label = "The circle condition $Q_R(u) ≥ 0$ for $-1 ≤ u ≤ 1$"

[[theorems]]
name = "RealRooted.Toeplitz.Circle.strictInterl_of_circleNonneg"
module = "RealRooted.Toeplitz.CircleCriterion"
label = "Toeplitz Hessenberg sections: simple real interlacing spectra if Im b ≥ 0 on a half-circle"
headline = true

[[theorems]]
name = "RealRooted.Toeplitz.Circle.roots_card_of_circleNonneg"
module = "RealRooted.Toeplitz.CircleCriterion"
label = "Under the circle condition $P_n$ has exactly $n$ distinct real roots"

[[theorems]]
name = "RealRooted.Toeplitz.Circle.not_isRoot_succ_of_circleNonneg"
module = "RealRooted.Toeplitz.CircleCriterion"
label = "Consecutive rows have no common root"

[[theorems]]
name = "RealRooted.Toeplitz.Circle.energy_identity"
module = "RealRooted.Toeplitz.CircleCriterion"
label = "The exact correlation energy identity at a row root"
-->

<!-- realrooted-catalog-content -->
# Circle criterion for Hessenberg Toeplitz matrices

Let $b(z)=z^{-1}+b_0+b_1z+\dots+b_sz^s$ be real, $T_n$ the $n\times n$ Toeplitz Hessenberg matrix
of $b$, and $P_n=\det(tI-T_n)$. If $\operatorname{Im}b(Re^{i\theta})\ge0$ for $0<\theta<\pi$ and
some $R>0$, then every $P_n$ has $n$ simple real zeros and $P_n\ll P_{n+1}$.

## Results

The matrix $T_n=(b_{i-j})_{i,j=1}^n$ has $b_{-1}=1$ above the diagonal and zeros further up, so
$P_0=1$ and
$$
P_{n+1}(t)=(t-b_0)P_n(t)-\sum_{k=1}^n b_kP_{n-k}(t).
$$
Equivalently, $\sum_nP_n(t)z^n=1/(zb(z)-tz)$. Let $U_k$ be the Chebyshev polynomials of the
second kind and put
$$
Q_R(u)=-R^{-1}+\sum_{k\ge1}b_kR^kU_{k-1}(u),
$$
so that $Q_R(\cos\theta)\sin\theta=\operatorname{Im}b(Re^{i\theta})$.

**Theorem (circle criterion).** If $Q_R(u)\ge0$ for $-1\le u\le1$ and some $R>0$, then every
$P_n$ has $n$ simple real zeros, and $P_n$ and $P_{n+1}$ strictly interlace and have no common
zero.

## Use

The criterion certifies real-rootedness and interlacing for recurrences of Toeplitz type, where
the classical three-term theory does not apply; for $b(z)=z^{-1}+z$ the $P_n$ are the Chebyshev
polynomials of the second kind in $t=2\cos\theta$. As $n\to\infty$, the zeros of $P_n$
accumulate on the curve described by Schmidt and Spitzer; compare
[limits of zeros](rr:limits-of-zeros). Shapiro and Štampach characterize banded Toeplitz matrices
whose principal submatrices all have real spectrum via symbols that are real on a Jordan curve;
the circle criterion gives an explicit sufficient condition on a circle of radius $R$, with
simple roots and interlacing. Further interlacing rows of $1/(Q(z)-tz)$ are on the
[Hessenberg rows](rr:hessenberg-rows) page.

## Proof

At each real zero $\xi$ of $P_n$, the quantity $-R^{2n+1}P_{n-1}(\xi)P_{n+1}(\xi)$ equals $R$
plus a quadratic form in the values $R^jP_{j-1}(\xi)$, and the circle condition makes this form
nonnegative. So $P_{n-1}$ and $P_{n+1}$ have opposite signs at the zeros of $P_n$, and induction
on $n$ gives the interlacing.

## References

Found by Per Alexandersson and [sqrt-of-2](https://github.com/sqrt-of-2) (2026), inspired by
B. Shapiro and F. Štampach, “Non-self-adjoint Toeplitz matrices whose principal submatrices
have real spectrum,” *Constr. Approx.*, [arXiv:1702.00741](https://arxiv.org/abs/1702.00741).
P. Schmidt and F. Spitzer, “The Toeplitz matrices of an arbitrary Laurent polynomial,”
*Math. Scand.* 8 (1960), 15–38.
<!-- /realrooted-catalog-content -->
-/
