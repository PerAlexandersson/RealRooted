module

import RealRooted.LaguerreInequalities
import RealRooted.LaguerreInequalities.CriticalPoint
import RealRooted.LaguerreInequalities.SignAlternation
import RealRooted.LaguerreInequalities.Rows

/-!
# Laguerre inequalities

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "laguerre-inequalities"
formalized = "2026-11-09"
authors = []
references = []
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
label = "f is real-rooted iff f′ is real-rooted and both Laguerre forms are nonnegative"
headline = true

[[theorems]]
name = "RealRooted.splits_derivative_and_forms_nonneg_of_splits"
module = "RealRooted.LaguerreInequalities.Forms"
label = "Forward direction: Rolle and the two Laguerre inequalities"
tags = []

[[theorems]]
name = "RealRooted.splits_of_splits_derivative_of_forms_nonneg"
module = "RealRooted.LaguerreInequalities"
label = "Converse: a real-rooted derivative and nonnegative forms give a real-rooted polynomial"

[[theorems]]
name = "RealRooted.eval_mul_eval_derivative_derivative_neg_of_forms_nonneg"
module = "RealRooted.LaguerreInequalities.CriticalPoint"
label = "At a non-root critical point, f f'' < 0"

[[theorems]]
name = "RealRooted.splits_of_eval_mul_derivative_neg"
module = "RealRooted.LaguerreInequalities.SignAlternation"
label = "Sign alternation at the roots of G forces F to be real-rooted"

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
label = "The two Laguerre inequalities force every coefficient row to be real-rooted"
-->

<!-- realrooted-catalog-content -->
# Laguerre inequalities

A real polynomial is real-rooted if and only if its derivative is real-rooted and two Laguerre
forms are nonnegative on the real line. This reduces real-rootedness to one degree lower, which
suits families closed under differentiation, such as the coefficient rows of
$(Q(z)-tz)^{-\alpha}$.

## Results

For a real polynomial $f$ let
$$
L_1(f)=(f')^2-ff'',\qquad
L_2(f)=\frac{3(f'')^2-4f'f'''+ff^{(4)}}{12}.
$$
These are the coefficients of $y^2$ and of $y^4$ in $f(t+iy)f(t-iy)$.

**Theorem (derivative descent).** A real polynomial $f$ is real-rooted if and only if $f'$ is
real-rooted and $L_1(f)(t)\ge0$ and $L_2(f)(t)\ge0$ for every real $t$. Here the zero polynomial
and constants count as real-rooted.

**Example.** For $f=t^4-1$ the derivative $4t^3$ is real-rooted and $L_1(f)=4t^6+12t^2\ge0$, but
$L_2(f)(0)=-2$ and $f$ is not real-rooted. Thus the second inequality is needed.

**Proposition (sign at critical points).** Let $f'\ne0$ and let both forms be nonnegative on
$\mathbb R$. If $f'(\rho)=0$ and $f(\rho)\ne0$, then $f(\rho)f''(\rho)<0$, so $\rho$ is a simple
root of $f'$.

**Proposition (sign alternation).** Let $G$ be real-rooted, let $F$ be real with
$\deg F=\deg G+1$ and leading coefficients of the same sign. If $F(\rho)G'(\rho)<0$ at every
root $\rho$ of $G$, then $F$ is real-rooted.

**Theorem (coefficient rows).** Let $Q$ be a real power series with $Q(0)=1$, for example a
polynomial, and let
$$
F_n^\alpha(t)=[z^n]\,(Q(z)-tz)^{-\alpha},
$$
for $n\ge0$ and $\alpha>0$, with $F_n^\alpha=0$ for $n<0$. Then
$\partial_tF_n^\alpha=\alpha F_{n-1}^{\alpha+1}$. Let $(\alpha)_k$ be the rising factorial. If
$$
\alpha^2(F_{n-1}^{\alpha+1})^2-\alpha(\alpha+1)F_n^\alpha F_{n-2}^{\alpha+2}\ge0
$$
and
$$
3(\alpha)_2^2(F_{n-2}^{\alpha+2})^2-4\alpha(\alpha)_3F_{n-1}^{\alpha+1}F_{n-3}^{\alpha+3}
+(\alpha)_4F_n^\alpha F_{n-4}^{\alpha+4}\ge0
$$
on $\mathbb R$ for every integer $n$ and every positive integer $\alpha$, then every row
$F_n^\alpha$ with $n\ge0$ and positive integer $\alpha$ is real-rooted.

## Proof

For the forward direction, $L_1((t-a)g)=g^2+(t-a)^2L_1(g)$ and
$L_2((t-a)g)=L_1(g)+(t-a)^2L_2(g)$, so induction on the roots gives nonnegativity, and $f'$ is
real-rooted by Rolle's theorem. For the converse, write $f=dF$ and $f'=dG$ with $d=\gcd(f,f')$;
the critical-point proposition gives $F(\rho)G'(\rho)<0$ at each root $\rho$ of $G$, so $F$ and
$f$ are real-rooted by sign alternation. For the rows, the $j$th derivative of $F_n^\alpha$ is
$(\alpha)_jF_{n-j}^{\alpha+j}$, so the displayed inequalities say $L_1(F_n^\alpha)\ge0$ and
$L_2(F_n^\alpha)\ge0$, and we conclude by induction on $n$.

## References

For rows of $(Q(z)-tB(z))^{-\alpha}$ with real-rooted $Q$ and $B$, see the
[chain polynomial page](rr:branden-leite).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.LaguerreInequalities`,
`RealRooted.LaguerreInequalities.Forms`, `RealRooted.LaguerreInequalities.CriticalPoint`,
`RealRooted.LaguerreInequalities.SignAlternation` and `RealRooted.LaguerreInequalities.Rows`.
-/
