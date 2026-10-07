import RealRooted.LeeYang

/-!
# Lee–Yang circle theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "lee-yang"
authors = ["Lee", "Yang", "Asano", "Ruelle"]
years = [1952, 1970]

[[theorems]]
name = "RealRooted.LeeYang.lee_yang_circle"
module = "RealRooted.LeeYang"
label = "Lee–Yang: all zeros lie on the unit circle"
headline = true

[[theorems]]
name = "RealRooted.LeeYang.lee_yang_polydisc"
module = "RealRooted.LeeYang"
label = "No zeros in the open unit polydisc"

[[theorems]]
name = "RealRooted.LeeYang.ising_norm_eq_one"
module = "RealRooted.LeeYang"
label = "Ferromagnetic Ising partition function"

[[theorems]]
name = "RealRooted.LeeYang.asano_contraction"
module = "RealRooted.LeeYang"
label = "Asano contraction"
-->

<!-- realrooted-catalog-content -->
# The Lee–Yang circle theorem

Let $a = (a_{ij})$ be a real symmetric matrix with $|a_{ij}| \le 1$, indexed by a finite
set $V$. The multiaffine polynomial
$$
P(z) = \sum_{S \subseteq V} \Bigl(\prod_{i \in S} \prod_{j \notin S} a_{ij}\Bigr)
  \prod_{i \in S} z_i
$$
has no zeros when every $|z_i| < 1$, and none when every $|z_i| > 1$.

**Theorem (Lee–Yang).** All zeros of $P(z, z, \dotsc, z)$ lie on the unit circle $|z| = 1$.

For the ferromagnetic Ising model, $a_{ij} = e^{-2\beta J_{ij}}$ with $J_{ij} \ge 0$, so the
zeros of the partition function in the fugacity lie on the unit circle.

The proof uses Asano contractions. The two-site polynomial $1 + c(z_1 + z_2) + z_1 z_2$
with $|c| \le 1$ has no zeros in the open bidisc. If
$\alpha + \beta u + \gamma v + \delta u v$ has no zeros there, then neither does
$\alpha + \delta z$. Building $P$ edge by edge as a product of two-site factors in separate
variables, and contracting the copies of each variable, gives the polydisc statement. The
exterior statement follows from the identity $P(z) = (\prod_i z_i)\, P(1/z)$.

## References

T. D. Lee and C. N. Yang, “Statistical theory of equations of state and phase transitions.
II. Lattice gas and Ising model,” *Physical Review* 87 (1952), 410–419; T. Asano, “Lee–Yang
theorem and the Griffiths inequality for the anisotropic Heisenberg ferromagnet,” *Physical
Review Letters* 24 (1970), 1409–1411; D. Ruelle, “Characterization of Lee–Yang polynomials,”
*Annals of Mathematics* 171 (2010), 589–603.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proof lives in `RealRooted.LeeYang`.
-/
