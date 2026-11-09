module

import RealRooted.LaguerreInequalities
import RealRooted.LaguerreInequalities.CriticalPoint
import RealRooted.LaguerreInequalities.SignAlternation
import RealRooted.LaguerreInequalities.Rows

/-!
# Two Laguerre inequalities and derivative descent

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "laguerre-inequalities"
formalized = "2026-11-09"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.laguerreForm"
module = "RealRooted.Wronskian.PolarLaguerre"
label = "First Laguerre form L₁ f = f′² − f f''"
tags = []

[[definitions]]
name = "RealRooted.secondLaguerreForm"
module = "RealRooted.LaguerreInequalities.Forms"
label = "Second Laguerre form L₂ f = (3 f''² − 4 f′ f''' + f f⁽⁴⁾) / 12"
tags = []

[[definitions]]
name = "RealRooted.BrandenLeite.affineNegativePowerRow"
module = "RealRooted.LaguerreInequalities.Rows"
label = "Row n of (Q − t z)^(−κ), zero for negative n"

[[theorems]]
name = "RealRooted.splits_iff_splits_derivative_and_forms_nonneg"
module = "RealRooted.LaguerreInequalities"
label = "f splits iff f′ splits and both Laguerre forms are nonnegative"
headline = true

[[theorems]]
name = "RealRooted.splits_derivative_and_forms_nonneg_of_splits"
module = "RealRooted.LaguerreInequalities.Forms"
label = "Forward direction: Rolle and the two Laguerre inequalities"
tags = []

[[theorems]]
name = "RealRooted.splits_of_splits_derivative_of_forms_nonneg"
module = "RealRooted.LaguerreInequalities"
label = "Converse: a split derivative and both forms nonnegative give a split polynomial"

[[theorems]]
name = "RealRooted.eval_mul_eval_derivative_derivative_neg_of_forms_nonneg"
module = "RealRooted.LaguerreInequalities.CriticalPoint"
label = "At a non-root critical point, f f'' < 0"

[[theorems]]
name = "RealRooted.splits_of_eval_mul_derivative_neg"
module = "RealRooted.LaguerreInequalities.SignAlternation"
label = "Sign alternation at the roots of G forces F to split"

[[theorems]]
name = "RealRooted.exists_splits_derivative_laguerreForm_nonneg_not_splits"
module = "RealRooted.LaguerreInequalities"
label = "The second inequality cannot be dropped: X⁴ − 1"

[[theorems]]
name = "RealRooted.BrandenLeite.derivative_affineNegativePowerRow"
module = "RealRooted.LaguerreInequalities.Rows"
label = "The t-derivative of a coefficient row is κ times a row"

[[theorems]]
name = "RealRooted.BrandenLeite.splits_affineNegativePowerRow_of_inequalities"
module = "RealRooted.LaguerreInequalities.Rows"
label = "Coefficient-row induction: the two Laguerre inequalities force every row to split"
headline = true
-->

<!-- realrooted-catalog-content -->
# Two Laguerre inequalities and derivative descent

For a real polynomial $f$ we write
$$
L_1(f)=(f')^2-ff'',\qquad
L_2(f)=\frac{3(f'')^2-4f'f'''+ff^{(4)}}{12}.
$$
By Laguerre's classical inequality, $L_1(f)\ge 0$ on $\mathbb R$ when $f$ splits over
$\mathbb R$; $L_1$ and $L_2$ are the coefficients of $y^2$ and $y^4$ in
$f(t+iy)f(t-iy)$.

**Theorem** (derivative descent). A real polynomial $f$ splits over $\mathbb R$ if and only if
$f'$ splits over $\mathbb R$ and $L_1(f)(t)\ge 0$ and $L_2(f)(t)\ge 0$ for every real $t$.
Repeated roots are allowed; zero, constants and linear polynomials are the base cases.

**The second inequality is needed.** For $f=t^4-1$ the derivative $4t^3$ splits and
$L_1(f)=4t^6+12t^2\ge 0$, but $L_2(f)(0)=-2$, and $f$ does not split. Checking the second
inequality only at the critical points of $f$ would not suffice: at a critical point of
multiplicity at least five of $f'$ the form $L_2$ vanishes but is negative nearby.

**Theorem** (coefficient rows). Let $Q$ be a power series with $Q(0)=1$ (for example a real
polynomial) and
$$
F_n^\alpha(t)=[z^n]\,(Q(z)-tz)^{-\alpha},\qquad n\ge 0,\ \alpha\in\mathbb Z_{>0},
$$
with $F_n^\alpha=0$ for $n<0$. Then $\partial_tF_n^\alpha=\alpha F_{n-1}^{\alpha+1}$. If
$$
\alpha^2(F_{n-1}^{\alpha+1})^2-\alpha(\alpha+1)F_n^\alpha F_{n-2}^{\alpha+2}\ge 0
$$
and
$$
3(\alpha)_2^2(F_{n-2}^{\alpha+2})^2
-4\alpha(\alpha)_3F_{n-1}^{\alpha+1}F_{n-3}^{\alpha+3}
+(\alpha)_4F_n^\alpha F_{n-4}^{\alpha+4}\ge 0
$$
hold on $\mathbb R$ for every $n$ and every positive integer $\alpha$, where $(\alpha)_k$ is
the rising factorial, then every row $F_n^\alpha$ splits. No factorization hypothesis on $Q$
is imposed.

## Proof idea

*Forward.* Adjoining a factor $t-a$ to $g$ changes the two forms as follows:
$L_1((t-a)g)=g^2+(t-a)^2L_1(g)$ and
$L_2((t-a)g)=L_1(g)+(t-a)^2L_2(g)$. Induction on the roots shows that both forms are
nonnegative; the derivative splits by Rolle's theorem.

*Converse.* Put $d=\gcd(f,f')$, $f=dF$, $f'=dG$. Then $G$ splits and $F,G$ are coprime. At a
root $\rho$ of $G$ the polynomial $d$ does not vanish, since a common root of $d$ and $G$ would
make the multiplicity of $\rho$ in $f'$ larger than its multiplicity in $f$ minus one. So $\rho$
is a critical point of $f$ with $f(\rho)\neq 0$. Write $f'=(t-\rho)^{j+1}h$ with
$h(\rho)\neq 0$. Then $L_1(f)=(t-\rho)^jK_1$ with $K_1(\rho)=-(j+1)f(\rho)h(\rho)\neq 0$, and a
polynomial $(t-\rho)^jK$ with $K(\rho)\ne 0$ that is nonnegative on $\mathbb R$ has even $j$ and
$K(\rho)>0$. Hence $f(\rho)h(\rho)<0$. If $j=k+2\ge 2$, then
$12L_2(f)=(t-\rho)^kK_2$ with $K_2(\rho)=(k+1)(k+2)(k+3)f(\rho)h(\rho)<0$, and $k$ is even, so
$L_2(f)$ is negative near $\rho$, a contradiction. Thus $j=0$: the roots of $G$ are simple and
$f(\rho)f''(\rho)<0$, that is $F(\rho)G'(\rho)<0$. Consequently $F$ has alternating signs at the
roots of $G$, which has degree $\deg F-1$ and a leading coefficient of the same sign as that of
$F$. By the intermediate value theorem $F$ has a root in each gap between consecutive roots of
$G$, one below the smallest root and one above the largest: $\deg F$ distinct real roots.
So $F$ and $f=dF$ split.

*Rows.* The coefficient of $t^k$ in $F_n^\alpha$ is
$\mathrm{multichoose}(\alpha,k)\,[z^{n-k}]\,Q^{-\alpha-k}$, which gives
$\partial_tF_n^\alpha=\alpha F_{n-1}^{\alpha+1}$. The two displayed inequalities are exactly
$L_1(F_n^\alpha)\ge 0$ and $12L_2(F_n^\alpha)\ge 0$, because the $j$th derivative of
$F_n^\alpha$ is $(\alpha)_jF_{n-j}^{\alpha+j}$. Induction on $n$, for all positive integers
$\alpha$ at once: the derivative $\alpha F_{n-1}^{\alpha+1}$ of $F_n^\alpha$ splits, so the
derivative descent theorem shows that $F_n^\alpha$ splits.

## What is new

The proof of the converse direction and of the coefficient-row induction is new: it was
developed for RealRooted (issue #2481) and is of independent research interest. We make no
claim of historical priority for the statement. Classical inputs are Laguerre's inequality
and the product formula for $f(t+iy)f(t-iy)$ in the forward direction, and Rolle's theorem.

## References

No published source is cited for the converse direction.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.LaguerreInequalities`,
`RealRooted.LaguerreInequalities.Forms`, `RealRooted.LaguerreInequalities.CriticalPoint`,
`RealRooted.LaguerreInequalities.SignAlternation` and `RealRooted.LaguerreInequalities.Rows`.
-/
