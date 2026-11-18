module

import RealRooted.DegreeIncreasingLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootContinuity.Path

/-!
# Continuity of roots

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "root-continuity"
formalized = "2026-10-06"
references = [
  "RahmanSchmeisser2002",
]

[[theorems]]
name = "RealRooted.splits_of_monic_of_coeff_tendsto"
module = "RealRooted.RootContinuity"
label = "A coefficientwise limit of monic real-rooted polynomials of fixed degree is real-rooted"
headline = true

[[theorems]]
name = "RealRooted.splits_of_monic_of_coeff_approx"
module = "RealRooted.RootContinuity"
label = "A monic polynomial approximable by real-rooted ones of its degree is real-rooted"

[[theorems]]
name = "RealRooted.splits_of_isPreconnected"
module = "RealRooted.RootContinuity.Path"
label = "Real-rootedness persists over a preconnected family of squarefree polynomials"

[[theorems]]
name = "RealRooted.splits_of_path"
module = "RealRooted.RootContinuity.Path"
label = "Real-rootedness persists along a path of squarefree polynomials of fixed degree"

[[theorems]]
name = "RealRooted.exists_aroot_near_of_monic_of_coeff_close"
module = "RealRooted.RootContinuity"
label = 'Coefficients within $ε$ move every root by at most $((m + 1)ε)^{1/m} \max(|z|, 1)$'

[[theorems]]
name = "RealRooted.exists_real_root_near_in_left_family"
module = "RealRooted.RootContinuity"
label = "For large t, every real root of f is close to a real root of tf + g"

[[theorems]]
name = "RealRooted.degreeIncreasing_local_lower_count"
module = "RealRooted.DegreeIncreasingLocalLowerCount"
label = "For small μ > 0, a root of f of multiplicity k keeps k nearby roots in f + μg"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.card_roots_filter_all_eq_of_no_isRoot_Icc"
module = "RealRooted.RootContinuity"
label = "Root counts on either side are constant across an interval without roots"

[[theorems]]
name = "RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Ioo"
module = "RealRooted.RootContinuity"
label = "The difference of upper root counts of f and g is constant where both are nonzero"
-->

<!-- realrooted-catalog-content -->
# Continuity of roots

Roots depend continuously on coefficients. Hence real-rootedness of monic polynomials of fixed
degree is closed under coefficientwise limits, persists along continuous families of squarefree
polynomials, and root counts do not change across intervals free of roots.

## Results

Roots are counted with multiplicity.

**Theorem (closure).** Let $f$ be monic. If for every $\varepsilon>0$ there is a monic
real-rooted polynomial of degree $\deg f$ whose coefficients are within $\varepsilon$ of those
of $f$, then $f$ is real-rooted. In particular, a coefficientwise limit of monic real-rooted
polynomials of degree $\deg f$ is real-rooted.

**Theorem (continuous families).** Let $P_t$ be real polynomials of constant degree, indexed by
a preconnected set $S$, with coefficients continuous in $t$ and each $P_t$ squarefree. If one
$P_a$ is real-rooted, then every $P_b$ is real-rooted.

**Theorem (nearby roots).** Let $f,g$ be monic of degree $m$, with $g$ real-rooted and all
coefficients of $g$ within $\varepsilon>0$ of those of $f$. Every complex root $z$ of $f$ has a
root $w$ of $g$ with $|z-w|<\bigl((m+1)\varepsilon\bigr)^{1/m}\max(|z|,1)$. The same bound
holds between a real root of $f$ and a real root of $tf+g$ when $tf+g$ is real-rooted and
$t>0$ is large compared with the coefficients of $f$ and $g$.

**Theorem (degree-increasing perturbation).** Let $f$ be real-rooted, $\deg f<\deg g$ and
$\rho>0$. There is $\delta>0$ such that whenever $0<\mu<\delta$ and $f+\mu g$ is real-rooted,
each root of $f$ of multiplicity $k$ has at least $k$ roots of $f+\mu g$ within distance
$\rho$.

**Theorem (root counts).** If $p$ has no root in $[a,b]$, then $p$ has as many roots $\le a$ as
$\le b$, and as many roots $>a$ as $>b$. If $f$ and $g$ have no root in $(a,b)$, then the
number of roots of $f$ greater than $t$ minus that of $g$ is the same for all $t\in(a,b)$.

## Use

To prove that a family is real-rooted, we deform it to a known real-rooted member and check that
no member along the way has a repeated root, or we approximate it by real-rooted polynomials of
the same degree. Counting roots across root-free intervals is the basic step in sign-change
proofs of [interlacing](rr:interlacing).

## References

[@RahmanSchmeisser2002] for the continuity of zeros.
<!-- /realrooted-catalog-content -->
-/
