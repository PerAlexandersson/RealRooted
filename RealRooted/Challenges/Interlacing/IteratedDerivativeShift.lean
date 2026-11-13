module

import RealRooted.IteratedDerivativeShift
import RealRooted.Tactic.IteratedDerivativeShift
import RealRooted.Tactic.IteratedDerivativeShiftProduct

/-!
# Iterated derivative shifts

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "iterated-derivative-shift"
formalized = "2026-10-05"
authors = ["Schur", "Pólya", "Obreschkoff"]
tags = []
references = [
  "SchurPolya1914",
  "Obreschkoff1963",
]

[[theorems]]
name = "RealRooted.splits_tDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Positive shifts preserve splitness"

[[theorems]]
name = "RealRooted.splits_tDeriv_all"
module = "RealRooted.IteratedDerivativeShift"
label = "All real shifts preserve splitness"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_tDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Positive shifts give interlacing"

[[theorems]]
name = "RealRooted.derivative_strictInterl_tDeriv_of_nonpos"
module = "RealRooted.IteratedDerivativeShift"
label = "Nonpositive shifts from the derivative"

[[theorems]]
name = "RealRooted.derivative_strictInterl_tDeriv_of_nonpos_of_common_factor"
module = "RealRooted.IteratedDerivativeShift"
label = "Common-factor derivative interlacing"

[[theorems]]
name = "RealRooted.hasSimpleRoots_iterateTDeriv_of_natDegree"
module = "RealRooted.IteratedDerivativeShift"
label = "Simple roots after degree-many shifts"

[[theorems]]
name = "RealRooted.hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le"
module = "RealRooted.IteratedDerivativeShift"
label = "Simple roots after enough negative shifts"

[[theorems]]
name = "RealRooted.exists_delta_and_real_root_near_iterateTDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots for monic regularizations"

[[theorems]]
name = "RealRooted.exists_root_near_iterateTDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots after normalization"

[[theorems]]
name = "RealRooted.exists_root_near_derivative_iterateTDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots in a derivative tower"

[[theorems]]
name = "RealRooted.exists_root_near_iterateTDeriv_of_lt_multiplicity"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots from multiplicity"

[[theorems]]
name = "RealRooted.Tactic.iterateTDeriv_sequence_splits"
module = "RealRooted.Tactic.IteratedDerivativeShift"
label = "Sequence iterates preserve splitness"

[[theorems]]
name = "RealRooted.Tactic.iterateTDeriv_sequence_strictInterl_succ"
module = "RealRooted.Tactic.IteratedDerivativeShift"
label = "Sequence iterates interlace"

[[theorems]]
name = "RealRooted.isRealRooted_iterateTDeriv"
module = "RealRooted.Tactic.IteratedDerivativeShiftProduct"
label = "An iterate remains real-rooted"

[[theorems]]
name = "RealRooted.isRealRooted_of_iteratedTDeriv_product_sequence"
module = "RealRooted.Tactic.IteratedDerivativeShiftProduct"
label = "Left-factor product recurrence"

[[theorems]]
name = "RealRooted.isRealRooted_of_iteratedTDeriv_product_right_sequence"
module = "RealRooted.Tactic.IteratedDerivativeShiftProduct"
label = "Right-factor product recurrence"
-->

<!-- realrooted-catalog-content -->
# Iterated derivative shifts

The shift $p\mapsto p-\varepsilon p'$ preserves real-rootedness for every real $\varepsilon$ and,
for $\varepsilon>0$, produces an interlacing polynomial and, after $\deg p$ iterations, simple
roots.

## Results

For real $\varepsilon$ let $T_\varepsilon p=p-\varepsilon p'$.

**Theorem (real-rootedness).** If $p$ is real-rooted, then $T_\varepsilon p$ is real-rooted for
every real $\varepsilon$, and so is every iterate $T_\varepsilon^kp$. If $p\ne0$, then
$T_\varepsilon^kp\ne0$.

**Theorem (interlacing).** If $p\ne0$ is real-rooted and $\varepsilon>0$, then
$p\ll T_\varepsilon p$.

**Theorem (derivative).** Let $p$ be real-rooted with positive leading coefficient and
$\deg p\ge1$. If $\varepsilon\le0$, then $p'\ll T_\varepsilon p$. The same holds without the
assumption on the leading coefficient of $p$ if $p=dq$ and $p'=dr$, where $d\ne0$ is
real-rooted, $r\ll q$, and $q,r$ have positive leading coefficients.

**Theorem (simple roots).** Let $f\ne0$ be real-rooted and $\varepsilon>0$. If $\deg f=n$, then
$T_\varepsilon^nf$ has simple roots. If $\deg f\le k$, then $T_{-\varepsilon}^kf$ has simple
roots.

**Theorem (nearby roots).** Let $p$ be real-rooted, $a$ a root of $p$, $n\ge0$ and $\eta>0$.
Then there is $\delta>0$ such that for every $0<\varepsilon<\delta$ the polynomial
$T_\varepsilon^np$ has a real root $b$ with
$$
|a-b|<\bigl((\deg p+1)\eta\bigr)^{1/\deg p}\max(|a|,1).
$$
The same holds for the roots of the $k$-th derivative of $p$, and for $a$ with
$k<\operatorname{mult}_a(p)$ it gives a root of $(T_\varepsilon^np)^{(k)}$ near $a$, with
$\deg p$ replaced by $\deg p^{(k)}$ in the bound.

**Theorem (sequences).** Let $P_i\ne0$ be real-rooted, $\varepsilon_i>0$ and $k_i\in\mathbb N$.
Then $T_{\varepsilon_i}^{k_i}P_i$ is real-rooted and
$T_{\varepsilon_i}^{k_i}P_i\ll T_{\varepsilon_i}^{k_i+1}P_i$. Moreover, let $P_0\ne0$ and
$F_n\ne0$ be real-rooted, and let $\varepsilon_n$ be real. If
$P_{n+1}=F_n\,T_{\varepsilon_n}^{k_n}P_n$, or $P_{n+1}=T_{\varepsilon_n}^{k_n}P_n\,F_n$, then
every $P_n$ is nonzero and real-rooted.

## References

[@SchurPolya1914; @Obreschkoff1963].
<!-- /realrooted-catalog-content -->
-/
