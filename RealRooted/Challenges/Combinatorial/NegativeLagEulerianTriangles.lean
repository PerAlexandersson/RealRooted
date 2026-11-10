module

public import RealRooted.EulerianTriangles.NegativeLagCone

/-!
# Negative-lag Eulerian recurrences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "negative-lag-eulerian-recurrences"
formalized = "2026-11-10"
tags = ["realrooted-original"]
years = [2026]

[[definitions]]
name = "RealRooted.negativeLagEulerRow"
module = "RealRooted.EulerianTriangles.NegativeLagCone"
label = "Negative-lag Euler polynomial rows"

[[definitions]]
name = "RealRooted.a371898Row"
module = "RealRooted.EulerianTriangles.NegativeLagCone"
label = "OEIS A371898 row polynomials"

[[theorems]]
name = "RealRooted.eq_negativeLagEulerRow_of_recurrence"
module = "RealRooted.EulerianTriangles.NegativeLagCone"
label = "The seeds and recurrence determine the rows"

[[theorems]]
name = "RealRooted.negativeLagEulerRow_degree_pos_rooted"
module = "RealRooted.EulerianTriangles.NegativeLagCone"
label = "Negative-lag Euler rows are rooted in [−1, 0]"
headline = true

[[theorems]]
name = "RealRooted.a371898Row_degree_pos_rooted"
module = "RealRooted.EulerianTriangles.NegativeLagCone"
label = "A371898 is rooted in [−1, 0]"
-->

<!-- realrooted-catalog-content -->
# Negative-lag Eulerian recurrences

**Provenance.** This proof is new, developed for RealRooted (issue #2511),
and is of independent research interest. It uses a nonnegative Bernstein-cone
certificate for Brändén's ordered-Bell transform.

Let $L f=xf+x(1+x)f'$. For nonnegative $r_n$, positive $s_n$, and
$n r_n\le s_n$, the rows determined by

$$
P_n=r_nP_{n-1}+s_nLP_{n-1}-r_ns_{n-1}LP_{n-2}
$$

have degree $n$, positive leading coefficient, split over the reals, and
have every root in $[-1,0]$. The proof first derives
$P_n=s_nLP_{n-1}+\prod_{i=1}^n r_i$, then identifies the normalized rows
with Brändén transforms whose explicit Bernstein coefficients are
nonnegative alternating sums.

The bound is sharp already for constant $r_n=r$ and $s_n=ns$: the second
row has discriminant $4(1-a)(1+3a)$, where $a=r/s$. The specialization
$r_n=1$, $s_n=n$ gives the row recurrence for
[OEIS A371898](https://oeis.org/A371898).

The existing Bernstein-image interlacing theorem is the classical input;
the recurrence reduction and alternating-sum certificate are the new parts.

## References

P. Brändén, *On linear transformations preserving the Pólya frequency property*, Trans. Amer.
Math. Soc. 358 (2006), 3697–3716 (the transform `E`). The application is
[OEIS A371898](https://oeis.org/A371898); see also the
[lag-two Eulerian triangles](/RealRooted/theorems/lag-two-eulerian-triangles/) page for the
positive-lag counterpart.
<!-- /realrooted-catalog-content -->
-/

public section

