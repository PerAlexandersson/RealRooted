module

import RealRooted.MultiplierSequence.FallingFactorial

/-!
# Falling-factorial truncations and the scalar big-block reduction

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "falling-factorial-truncations"
formalized = "2026-11-13"
authors = []
references = []

[[definitions]]
name = "RealRooted.fallingSchur"
module = "RealRooted.ArrayPolynomialSchur"
label = "Multiply coefficient j by the falling factorial (p)_j"

[[definitions]]
name = "RealRooted.weightedBell"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "The distinguished-block recurrence with two block weights"

[[definitions]]
name = "RealRooted.bigBlockScalar"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "The scalar big-block row"

[[definitions]]
name = "RealRooted.normalizedBigBlock"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "The normalized row R(m,p)"

[[theorems]]
name = "RealRooted.splits_fallingSchur"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "Falling-factorial truncation preserves real splitting"

[[theorems]]
name = "RealRooted.forall_splits_fallingSchur_iff"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "All falling-factorial truncations split exactly when the polynomial splits"
headline = true

[[theorems]]
name = "RealRooted.forall_splits_normalizedBigBlock_iff"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "The scalar big-block row splits exactly when all its normalized rows split"
-->

<!-- realrooted-catalog-content -->
# Falling-factorial truncations and the scalar big-block reduction

For a real polynomial $f(t)=\sum_j c_jt^j$, we set
$$
T_p f(t)=\sum_j (p)_{\underline j}c_jt^j,
\qquad (p)_{\underline j}=p(p-1)\cdots(p-j+1).
$$
Terms with $j>p$ vanish. We prove that $f$ splits over the reals if and only if
$T_p f$ splits for every natural number $p$, including zero. Splitting includes
the zero polynomial; no sign condition on the coefficients is needed.

For the forward direction, we reuse Schur's factorial-product theorem with
the PF factor $(t+1)^p$. We also verify that $T_p f$ is the degree-$p$
reflection of $f(D)t^p$, the identity underlying the Hermite–Poulain argument.
Conversely, $T_p f(t/p)$ converges coefficientwise to $f(t)$ with uniformly
bounded degree, so real splitting passes to the limit.

We also define the two-weight Bell rows by the distinguished-block recurrence
$$
F_0=1,\qquad
F_{n+1}=\sum_{r=1}^{n+1}\binom n{r-1}(\alpha_r+t\beta_r)F_{n+1-r}.
$$
The scalar big-block row $\mathcal B_m$ uses $\alpha_r=[r=1]$ and
$\beta_r=2/((r+1)(r+2))$. Its first rows are
$$
\mathcal B_1=1+t/3,\quad
\mathcal B_2=1+5t/6+t^2/9,\quad
\mathcal B_3=1+8t/5+t^2/2+t^3/27.
$$
Writing $R_{m,p}=T_p\mathcal B_m$, the checked equivalence is
$$
(\forall p\ge0,\ R_{m,p}\text{ splits})
\quad\Longleftrightarrow\quad \mathcal B_m\text{ splits}.
$$
The intended partition interpretation of $R_{m,p}$ counts partitions of
$m+2p$ elements with exactly $p$ nonsingleton blocks, marking blocks of size
at least three, and normalizes by $2^p p!m!/(m+2p)!$. The Lean definition uses
the coefficient transform; the partition-enumeration identity is not formalized here.

Real-rootedness of every $\mathcal B_m$ remains **open**. The supplied notes
report exact checks through $m=25$; these are finite evidence, not a proof.

## References

- [Issue #1773: big-block thresholds](https://github.com/PerAlexandersson/RealRooted/issues/1773).
- [Issue #2415: two-weight Bell rows](https://github.com/PerAlexandersson/RealRooted/issues/2415).
<!-- /realrooted-catalog-content -->
-/
