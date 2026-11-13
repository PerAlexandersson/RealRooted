module

import RealRooted.LeeYang

/-!
# Lee–Yang circle theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "lee-yang"
formalized = "2026-10-07"
tags = []
references = [
  "LeeYang1952",
  "Asano1970",
  "Ruelle2010",
]
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
name = "RealRooted.LeeYang.lee_yang_exterior"
module = "RealRooted.LeeYang"
label = "No zeros in the exterior of the polydisc"

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
# Lee–Yang circle theorem

The zeros of the partition function of a ferromagnetic Ising model in the fugacity lie on the
unit circle.

## Results

Let $a=(a_{ij})$ be a real symmetric matrix with $|a_{ij}|\le1$, indexed by a finite set $V$.
Define the multiaffine polynomial
$$P(z)=\sum_{S\subseteq V}\Bigl(\prod_{i\in S}\prod_{j\notin S}a_{ij}\Bigr)\prod_{i\in S}z_i.$$

**Theorem (Lee–Yang)** [@LeeYang1952]. All zeros of $P(z,z,\dotsc,z)$ lie on the unit circle
$|z|=1$. More precisely, $P(z)\ne0$ whenever every $|z_i|<1$, and whenever every $|z_i|>1$.

**Corollary (Ising model).** For $a_{ij}=e^{-2\beta J_{ij}}$ with $\beta\ge0$ and symmetric
$J_{ij}\ge0$, the zeros of the ferromagnetic Ising partition function in the fugacity lie on the
unit circle.

**Lemma (Asano contraction)** [@Asano1970]. If $\alpha+\beta u+\gamma v+\delta uv\ne0$ for all
$|u|,|v|<1$, then $\alpha+\delta z\ne0$ for all $|z|<1$.

## Proof

The two-site polynomial $1+c(z_1+z_2)+z_1z_2$ with $|c|\le1$ has no zeros in the open bidisc.
Building $P$ edge by edge as a product of two-site factors in separate variables, and contracting
the copies of each variable by the Asano lemma, gives the polydisc statement. The exterior
statement follows from $P(z)=(\prod_iz_i)\,P(1/z)$.

## References

- [@LeeYang1952]
- [@Asano1970]
- [@Ruelle2010]
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proof lives in `RealRooted.LeeYang`.
-/
