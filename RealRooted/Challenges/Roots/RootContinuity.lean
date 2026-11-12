module

import RealRooted.DegreeIncreasingLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootContinuity.Path

/-!
# Root continuity and root-count stability

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "root-continuity"
formalized = "2026-10-06"
authors = []
references = []
tags = []

[[theorems]]
name = "RealRooted.splits_of_isPreconnected"
module = "RealRooted.RootContinuity.Path"
label = "Transport along a preconnected parameter set"

[[theorems]]
name = "RealRooted.splits_of_path"
module = "RealRooted.RootContinuity.Path"
label = "Transport along a squarefree path"

[[theorems]]
name = "RealRooted.splits_of_path_of_separable"
module = "RealRooted.RootContinuity.Path"
label = "Transport from fibrewise separability"

[[theorems]]
name = "RealRooted.splits_of_monic_of_coeff_approx"
module = "RealRooted.RootContinuity"
label = "Closure under coefficient approximation"

[[theorems]]
name = "RealRooted.splits_of_monic_of_coeff_tendsto"
module = "RealRooted.RootContinuity"
label = "Closure under coefficientwise limits"
headline = true

[[theorems]]
name = "RealRooted.exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close"
module = "RealRooted.RootContinuity"
label = "A nearby root under coefficient control"

[[theorems]]
name = "RealRooted.exists_real_root_near_in_left_family"
module = "RealRooted.RootContinuity"
label = "A nearby real root in a left pencil"

[[theorems]]
name = "RealRooted.exists_complex_aroot_near_in_left_family"
module = "RealRooted.RootContinuity"
label = "A nearby complex root in a left pencil"

[[theorems]]
name = "RealRooted.exists_t_pos_with_normalized_left_family_bound"
module = "RealRooted.RootContinuity"
label = "Large-parameter coefficient control"

[[theorems]]
name = "RealRooted.splits_of_symmetric_substitution"
module = "RealRooted.RootContinuity"
label = "Splitting from a symmetric substitution"

[[theorems]]
name = "RealRooted.add_right_roots_eq_add_left_inv"
module = "RealRooted.RootContinuity"
label = "Reciprocal scaling of root multisets"

[[theorems]]
name = "RealRooted.add_right_roots_gt_card_eq_add_left_inv"
module = "RealRooted.RootContinuity"
label = "Reciprocal scaling of upper root counts"

[[theorems]]
name = "RealRooted.eval_endpoint_pos_of_forall_ne_zero"
module = "RealRooted.RootContinuity"
label = "Endpoint signs across a nonvanishing family"

[[theorems]]
name = "RealRooted.card_roots_filter_le_eq_of_no_isRoot_Icc"
module = "RealRooted.RootContinuity"
label = "Constancy of lower root counts"

[[theorems]]
name = "RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Icc"
module = "RealRooted.RootContinuity"
label = "Constancy of upper root counts"

[[theorems]]
name = "RealRooted.card_roots_filter_all_eq_of_no_isRoot_Icc"
module = "RealRooted.RootContinuity"
label = "Bundled root-count constancy"

[[theorems]]
name = "RealRooted.card_roots_filter_le_sub_eq_of_no_isRoot_Icc"
module = "RealRooted.RootContinuity"
label = "Stability of lower count differences"

[[theorems]]
name = "RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Icc"
module = "RealRooted.RootContinuity"
label = "Stability of upper count differences"

[[theorems]]
name = "RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Ioo"
module = "RealRooted.RootContinuity"
label = "Count differences at interior samples"

[[theorems]]
name = "RealRooted.odd_card_roots_filter_gt_sub_iff_of_no_isRoot_Ioo"
module = "RealRooted.RootContinuity"
label = "Parity of interior count differences"

[[theorems]]
name = "RealRooted.degreeIncreasing_local_lower_count"
module = "RealRooted.DegreeIncreasingLocalLowerCount"
label = "Roots of f survive near their positions in a degree-increasing perturbation f + μg"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Root continuity and root-count stability

Splitting over $\mathbb R$ is closed under coefficientwise limits and is transported along
continuous squarefree families, and root counts are constant across intervals without roots.

## Results

We write $\lVert p\rVert_1$ for the sum of the absolute values of the coefficients of $p$
(`coeffSumRange`). A polynomial *splits* if it is real-rooted. Roots are counted with multiplicity.

**Theorem (closure).** Let $f$ be monic. If for every $\varepsilon>0$ there is a monic split
polynomial $g$ of degree $\deg f$ with all coefficients within $\varepsilon$ of those of $f$, then
$f$ splits. In particular a monic $f$ is split if it is the coefficientwise limit of a sequence of
monic split polynomials of degree $\deg f$.

**Theorem (nearby roots).** Let $f,g$ be monic of the same degree $m$, let $g$ split, and let all
coefficients of $g$ be within $\varepsilon>0$ of those of $f$. For every complex root $z$ of $f$
there is a complex root $w$ of $g$ with
$$|z-w|<\bigl((m+1)\varepsilon\bigr)^{1/m}\max(|z|,1).$$

**Theorem (left pencil).** Let $f,g$ be monic of the same degree $m$, let $t>0$ and
$\varepsilon>0$ with $(t+1)^{-1}(\lVert f\rVert_1+\lVert g\rVert_1)<\varepsilon$, and let $tf+g$
be nonzero and split. For every real root $a$ of $f$ there is a real root $b$ of $tf+g$, and for
every complex root $z$ of $f$ there is a complex root $w$ of $tf+g$, within
$((m+1)\varepsilon)^{1/m}\max(|a|,1)$, respectively $((m+1)\varepsilon)^{1/m}\max(|z|,1)$.
Such $t>0$ exists for every $\varepsilon>0$.

**Theorem (reciprocal scaling).** For real $\mu\ne0$, the polynomials $f+\mu g$ and
$g+\mu^{-1}f$ have the same roots with multiplicity, hence the same number of roots larger than
any given $x$.

**Theorem (symmetric substitution).** Let $h\ne0$ be split and $n\in\mathbb N$ with
$f(-u^2)=u^n\,h\bigl((1-u^2)/u\bigr)$ for all nonzero $u\in\mathbb C$. Then $f$ splits.

**Theorem (continuous families).** Let $P_t$ be real polynomials of constant degree $d$ for $t$
in a preconnected set $S$, with each coefficient continuous in $t$ and each $P_t$ squarefree. If
$P_a$ splits for some $a\in S$, then $P_b$ splits for all $b\in S$. For $S=[0,1]$ the same holds
if each $P_t$ is separable instead of squarefree.

**Theorem (root counts).** Let $a\le b$ and let $p$ have no root in $[a,b]$. Then $p$ has equally
many roots $\le a$ and $\le b$, equally many roots $>a$ and $>b$, and no root in $(a,b]$. If
$f,g$ both have no root in $[a,b]$, then the differences $\#\{\text{roots}\le t\}$ of $f$ minus
that of $g$, and likewise for $\#\{\text{roots}>t\}$, agree at $t=a$ and $t=b$. If $f,g$ have no
root in the open interval $(a,b)$, the difference of the counts of roots $>t$ takes the same
value at all $t\in(a,b)$, and its parity is the same for all such $t$.

**Proposition (sign).** If $t\mapsto P_t(a)$ is continuous and nonvanishing on $[t_0,t_1]$, then
$P_{t_0}(a)\,P_{t_1}(a)>0$.

**Theorem (degree-increasing perturbation).** Let $f$ split, $\deg f<\deg g$ and $\rho>0$. There
is $\delta>0$ such that for all $0<\mu<\delta$ with $f+\mu g$ split, every root $a$ of $f$ of
multiplicity $k$ has at least $k$ roots of $f+\mu g$, counted with multiplicity, within distance
$\rho$ of $a$. Here the normalized left pencil is not available, since the leading coefficient
of $f+\mu g$ tends to zero with $\mu$.

## References

The continuity and root-count results come from the formal proofs for
[OEIS A358628](https://oeis.org/A358628), [OEIS A355144](https://oeis.org/A355144) and
[OEIS A176331](https://oeis.org/A176331).
<!-- /realrooted-catalog-content -->
-/
