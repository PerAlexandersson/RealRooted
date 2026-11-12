module

import RealRooted.Kurtz

/-!
# Kurtz's coefficient criterion

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "kurtz"
formalized = "2026-07-18"
tags = []
references = [
  "Kurtz1992",
]
authors = ["Kurtz"]
years = [1992]

[[definitions]]
name = "RealRooted.Kurtz.PositiveCoeffsUpToDegree"
module = "RealRooted.Kurtz"
label = "Positive coefficients"

[[definitions]]
name = "RealRooted.Kurtz.KurtzStrictInequalities"
module = "RealRooted.Kurtz"
label = "Kurtz inequalities a_k² > 4 a_{k-1} a_{k+1}"

[[theorems]]
name = "RealRooted.Kurtz.coefficient_criterion"
module = "RealRooted.Kurtz"
label = "Kurtz's criterion"
headline = true
-->

<!-- realrooted-catalog-content -->
# Kurtz's coefficient criterion

A polynomial with positive coefficients that satisfy $a_k^2>4a_{k-1}a_{k+1}$ is real-rooted.

## Results

**Theorem (Kurtz).** Let $\sum_{k=0}^na_kx^k$ be a real polynomial of degree $n\ge2$ with
$a_k>0$ for $0\le k\le n$ and $a_k^2>4a_{k-1}a_{k+1}$ for $0<k<n$. Then all its roots are real.

## References

See [@Kurtz1992] and the
[contextual account on symmetricfunctions.com](sf:kurtzTheorem).
<!-- /realrooted-catalog-content -->

Human statement:
sf:kurtzTheorem

Original references: J. I. Hutchinson, "On a remarkable class of entire
functions", Trans. Amer. Math. Soc. 25 (1923), 325--332, and D. C. Kurtz,
"A sufficient condition for all the roots of a polynomial to be real",
Amer. Math. Monthly 99 (1992), 259--263.

This module exposes the reusable theorem implementation in `RealRooted.Kurtz`.
-/
