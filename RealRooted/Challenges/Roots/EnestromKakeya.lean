module

import RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya

/-!
# Eneström–Kakeya theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "enestrom-kakeya"
formalized = "2026-10-07"
references = []
tags = []
authors = ["Eneström", "Kakeya"]
years = [1893, 1912]

[[theorems]]
name = "Polynomial.norm_le_one_of_isRoot_of_coeff_monotone"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya"
label = "Eneström–Kakeya: increasing coefficients give zeros in the unit disk"
headline = true

[[theorems]]
name = "Polynomial.norm_mem_Icc_of_isRoot_of_coeff_pos"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya"
label = "Eneström–Kakeya annulus for positive coefficients"
-->

<!-- realrooted-catalog-content -->
# Eneström–Kakeya theorem

If the coefficients of a real polynomial are positive and nondecreasing, all its complex zeros
lie in the closed unit disk.

## Results

**Theorem (Eneström–Kakeya).** If $0<a_0\le a_1\le\dotsb\le a_n$, then every complex zero $z$
of $a_0+a_1z+\dotsb+a_nz^n$ satisfies $|z|\le1$.

**Theorem (annulus form).** If $a_0,\dots,a_n>0$ and $m\,a_{i+1}\le a_i\le M\,a_{i+1}$ for
$0\le i<n$, then every complex zero $z$ of $a_0+a_1z+\dotsb+a_nz^n$ satisfies
$m\le|z|\le M$. The upper bound $|z|\le M$ needs only $a_0>0$, $M>0$ and
$a_i\le M\,a_{i+1}$.

## Proof

We multiply by $z-1$: the product is $a_nz^{n+1}-\sum_{k=1}^n(a_k-a_{k-1})z^k-a_0$, and the
coefficients $a_k-a_{k-1}$ and $a_0$ are nonnegative with sum $a_n$. For $|z|>1$ the triangle
inequality bounds the lower terms by $a_n|z|^n<a_n|z|^{n+1}$.

## References

G. Eneström, *Härledning af en allmän formel för antalet pensionärer …*,
Öfversigt af Kongl. Vetenskaps-Akademiens Förhandlingar 50 (1893);
S. Kakeya, *On the limits of the roots of an algebraic equation with positive
coefficients*, Tôhoku Math. J. 2 (1912), 140–142.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya`.
-/
