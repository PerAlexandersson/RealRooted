module

public import RealRooted.RootContinuity
public import RealRooted.RootContinuity.Path

/-!
# Root continuity and root-count stability

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "root-continuity"
formalized = "2026-10-06"

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
-->

<!-- realrooted-catalog-content -->
# Root continuity and root-count stability

We study how real roots behave under coefficient perturbations and along
continuous polynomial families. A monic polynomial remains split when it is
approximated coefficientwise by monic split polynomials of the same degree,
and the sequential form applies to coefficientwise limits. For a monic split
polynomial close to another one, the complex-root estimate gives a root within
an explicit distance of each prescribed root.

For the normalized left pencil

$$
\frac{t f+g}{t+1},
$$

the coefficient error from $f$ is bounded by
$(t+1)^{-1}(\operatorname{coeffSumRange}(f)+\operatorname{coeffSumRange}(g))$.
We can choose a positive $t$ making this bound smaller than any prescribed
positive precision. If $f$ and $g$ are monic of the same degree and the pencil
is split, the nearby-root results produce either a real root near a real root
of $f$, or a complex algebraic root near any complex root of $f$. Reciprocal
scaling exchanges $f+\mu g$ with $g+\mu^{-1}f$, preserving both its root
multiset and its upper-threshold root count. A symmetric substitution gives
another route from a nonzero split polynomial to a split polynomial.

The path theorems transport splitting across a preconnected parameter set when
the coefficients vary continuously, the degree is constant, and every fibre
is squarefree. Their unit-interval form applies on $[0,1]$; the separable form
replaces squarefreeness by fibrewise separability. The proof combines the
openness of strict sign alternations between ordered roots with the closedness
of the coefficientwise splitting condition.

Finally, if $t \mapsto P_t(a)$ is continuous and never vanishes on a closed
parameter interval, then its two endpoint values have the same sign. For a
fixed polynomial with no root in a closed interval, the lower and upper root
counts are constant as the threshold moves across that interval. The bundled
count theorem records both threshold equalities and the absence of roots in
the window. For two polynomials, the corresponding integer differences are
also constant, and the open-interval forms allow any two interior sample
points; the final theorem records the resulting parity invariance.

## References

The path-transport and root-count results were promoted from the formal proofs for
[OEIS A358628](https://oeis.org/A358628), [OEIS A355144](https://oeis.org/A355144), and
[OEIS A176331](https://oeis.org/A176331) in the companion OEIS formalization project.
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Challenges.RootContinuity

end RealRooted.Challenges.RootContinuity
