module

public import RealRooted.CombinatorialExamples.PathPowerClique
public import RealRooted.Applications.OEIS.PathPowerRows

/-!
# Path-power clique polynomials and OEIS rows

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "path-power-cliques-and-rows"
formalized = "2026-10-13"
references = [
  "ChudnovskySeymour2007",
]

[[definitions]]
name = "RealRooted.pathPowerCliquePolynomial"
module = "RealRooted.CombinatorialExamples.PathPowerClique"
label = "The path-power clique polynomial"

[[definitions]]
name = "RealRooted.PathPowerRows.a109955"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A109955 row family"

[[definitions]]
name = "RealRooted.PathPowerRows.a127893"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A127893 row family"

[[definitions]]
name = "RealRooted.PathPowerRows.a206294"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A206294 row family"

[[definitions]]
name = "RealRooted.PathPowerRows.a109960"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A109960 row family"

[[definitions]]
name = "RealRooted.PathPowerRows.a116088"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A116088 row family"

[[definitions]]
name = "RealRooted.PathPowerRows.a116089"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A116089 row family"

[[definitions]]
name = "RealRooted.PathPowerRows.a277627"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "The OEIS A277627 row family"

[[theorems]]
name = "RealRooted.splits_pathPowerCliquePolynomial"
module = "RealRooted.CombinatorialExamples.PathPowerClique"
label = "Path-power clique polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_pathPowerCliquePolynomial_add"
module = "RealRooted.CombinatorialExamples.PathPowerClique"
label = "Path-power clique polynomials form interlacing cliques"
headline = true

[[theorems]]
name = "RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial"
module = "RealRooted.CombinatorialExamples.PathPowerClique"
label = "Reciprocal shifts of path-power subsequences are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a109955"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A109955 rows are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a109955"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A109955 rows strictly interlace"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a127893"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A127893 rows are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a127893"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A127893 rows strictly interlace"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a206294"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A206294 rows are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a206294"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A206294 rows strictly interlace"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a109960"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A109960 rows are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a109960"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A109960 rows strictly interlace"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a116088"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A116088 rows are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a116088"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A116088 rows strictly interlace"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a116089"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A116089 rows are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a116089"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A116089 rows strictly interlace"

[[theorems]]
name = "RealRooted.PathPowerRows.splits_a277627"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A277627 rows are real-rooted"

[[theorems]]
name = "RealRooted.PathPowerRows.strictInterl_a277627"
module = "RealRooted.Applications.OEIS.PathPowerRows"
label = "OEIS A277627 rows strictly interlace"
-->

<!-- realrooted-catalog-content -->
# Path-power clique polynomials and OEIS rows

For $k \ge 2$ let
$$
Q(k,N) = \sum_i \binom{N-(k-1)i}{i} X^i .
$$
This is the independence polynomial of the $(k-1)$-th power of a path, so it is
real-rooted because powers of paths are claw-free. We show that these polynomials form
interlacing cliques of width $k$: for $1 \le j \le k$, $Q(k,N)$ strictly interlaces
$Q(k,N+j)$. Degree-padded reciprocal shifts transfer this to every subsequence of step at
most $k$, and the Graeffe transforms of $1 - s - Y s^k$ give the row recurrences.

As applications we prove that the OEIS row families A193636, A109955, A127893, A206294,
A109960, A116088, A116089 and A277627 are real-rooted and that consecutive rows strictly
interlace.

## References

Real-rootedness follows from [@ChudnovskySeymour2007]. The row families are
OEIS [A193636](https://oeis.org/A193636), [A109955](https://oeis.org/A109955),
[A127893](https://oeis.org/A127893), [A206294](https://oeis.org/A206294),
[A109960](https://oeis.org/A109960), [A116088](https://oeis.org/A116088),
[A116089](https://oeis.org/A116089), and [A277627](https://oeis.org/A277627).
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Challenges.PathPowerCliques

end RealRooted.Challenges.PathPowerCliques
