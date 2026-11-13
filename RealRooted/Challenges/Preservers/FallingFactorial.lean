module

import RealRooted.MultiplierSequence.FallingFactorial

/-!
# Falling-factorial truncations

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "falling-factorial-truncations"
formalized = "2026-11-13"
authors = []
references = ["SchurPolya1914"]

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
label = "The big-block row"

[[definitions]]
name = "RealRooted.normalizedBigBlock"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "The truncated big-block row R(m,p)"

[[theorems]]
name = "RealRooted.splits_fallingSchur"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "Falling-factorial truncation preserves real-rootedness"

[[theorems]]
name = "RealRooted.forall_splits_fallingSchur_iff"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "All falling-factorial truncations are real-rooted exactly when the polynomial is"
headline = true

[[theorems]]
name = "RealRooted.forall_splits_normalizedBigBlock_iff"
module = "RealRooted.MultiplierSequence.FallingFactorial"
label = "The big-block row is real-rooted exactly when all its truncations are"
-->

<!-- realrooted-catalog-content -->
# Falling-factorial truncations

A real polynomial is real-rooted exactly when all its falling-factorial truncations are. Each
truncation applies a finite multiplier sequence, and together the truncations detect
real-rootedness.

## Results

For a real polynomial $f(t)=\sum_j c_jt^j$ and $p\in\mathbb N$ let
$$
T_p f(t)=\sum_j p^{\underline j}\,c_jt^j,
\qquad p^{\underline j}=p(p-1)\dotsm(p-j+1),
$$
so that the terms with $j>p$ vanish. Here a polynomial is real-rooted if it is zero or splits
over $\mathbb R$.

**Theorem.** A real polynomial $f$ is real-rooted if and only if $T_pf$ is real-rooted for every
$p\ge0$.

The forward direction is due to Pólya and Schur [@SchurPolya1914, §2, p. 97], since
$T_pf=\sum_j\binom pj\,j!\,c_jt^j$.

**Corollary (big-block rows).** Define the two-weight Bell rows by
$$
F_0=1,\qquad
F_{n+1}=\sum_{r=1}^{n+1}\binom n{r-1}(\alpha_r+t\beta_r)F_{n+1-r},
$$
and let $\mathcal B_m$ be the row with $\alpha_r=[r=1]$ and $\beta_r=2/((r+1)(r+2))$, so that
$$
\mathcal B_1=1+t/3,\quad
\mathcal B_2=1+5t/6+t^2/9,\quad
\mathcal B_3=1+8t/5+t^2/2+t^3/27.
$$
Then $\mathcal B_m$ is real-rooted if and only if $R_{m,p}=T_p\mathcal B_m$ is real-rooted for
every $p\ge0$.

Up to the factor $2^pp!\,m!/(m+2p)!$, $R_{m,p}$ is the generating polynomial of partitions of an
$(m+2p)$-element set with exactly $p$ nonsingleton blocks, with $t$ marking the blocks of size at
least three. Whether every $\mathcal B_m$ is real-rooted is open.

## Proof

For the forward direction, $T_pf$ is Schur's composition of $f$ with $(1+t)^p$, which is
real-rooted by [Schur's theorem](rr:hadamard-products). Conversely, $T_pf(t/p)$ converges
coefficientwise to $f(t)$ as $p\to\infty$ with bounded degree, and real-rootedness passes to the
limit.

## References

- [@SchurPolya1914]
- [Multiplier sequences](sf:multiplierSequences) on symmetricfunctions.com
- [Finite multiplier sequences](sf:finiteMultiplierSequenceCriterion) on symmetricfunctions.com
<!-- /realrooted-catalog-content -->
-/
