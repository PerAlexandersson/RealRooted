module

public import RealRooted.Toeplitz.CircleCriterion

/-!
# Circle criterion for Hessenberg Toeplitz matrices

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hessenberg-circle-criterion"
formalized = "2026-11-13"
tags = []

[[definitions]]
name = "RealRooted.Toeplitz.Circle.row"
module = "RealRooted.Toeplitz.CircleCriterion"

[[definitions]]
name = "RealRooted.Toeplitz.Circle.CircleNonneg"
module = "RealRooted.Toeplitz.CircleCriterion"

[[theorems]]
name = "RealRooted.Toeplitz.Circle.strictInterl_of_circleNonneg"
module = "RealRooted.Toeplitz.CircleCriterion"
label = "The circle criterion gives simple real roots and consecutive interlacing"
headline = true

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

If the symbol of a lower Hessenberg Toeplitz matrix has nonnegative imaginary part on an upper
half-circle, then the characteristic polynomials of its sections have simple real roots and
consecutive ones strictly interlace.

## Results

Let $b(z)=z^{-1}+b_0+\sum_{k\ge1}b_kz^k$ with finitely many real coefficients. The
characteristic polynomials $P_n(t)=\det(tI-T_n)$ of the Toeplitz sections
$T_n=(b_{i-j})_{i,j=1}^n$ satisfy $P_0=1$ and
$$
P_{n+1}(t)=(t-b_0)P_n(t)-\sum_{k=1}^n b_kP_{n-k}(t).
$$

**Theorem (circle criterion).** If $\operatorname{Im}b(Re^{i\theta})\ge0$ for $0<\theta<\pi$
and some $R>0$, then every $P_n$ has $n$ simple real zeros and $P_n$ and $P_{n+1}$ strictly
interlace. Equivalently, the hypothesis says that
$$
Q_R(u)=-R^{-1}+\sum_{k\ge1}b_kR^kU_{k-1}(u)\ge0\qquad(-1\le u\le1),
$$
since $Q_R(\cos\theta)\sin\theta=\operatorname{Im}b(Re^{i\theta})$.

## Proof

At a real zero $\xi$ of $P_n$, an exact identity writes $-R^{2n+1}P_{n-1}(\xi)P_{n+1}(\xi)$ as
$R$ plus a quadratic form in the values $R^jP_{j-1}(\xi)$; integrating over the circle of
radius $R$ shows that the form is nonnegative. So $P_{n-1}$ and $P_{n+1}$ have opposite signs at
the zeros of $P_n$, and induction gives the interlacing.

## References

- Unpublished manuscript.
<!-- /realrooted-catalog-content -->
-/
