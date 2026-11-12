module

import RealRooted.Hutchinson

/-!
# Hutchinson's theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hutchinson"
formalized = "2026-10-07"
tags = []
references = [
  "Hutchinson1923",
  "Kurtz1992",
]
authors = ["Hutchinson"]
years = [1923]

[[theorems]]
name = "RealRooted.Hutchinson.isLaguerrePolya_tsum"
module = "RealRooted.Hutchinson"
label = "Hutchinson: such power series are Laguerre–Pólya entire functions"
headline = true

[[theorems]]
name = "RealRooted.IsLaguerrePolya.of_tendstoLocallyUniformly"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure"
label = "The Laguerre–Pólya class is closed under locally uniform limits"
-->

<!-- realrooted-catalog-content -->
# Hutchinson's theorem

If $a_k>0$ and $a_{k+1}^2\ge4a_ka_{k+2}$ for all $k$, then $\sum_ka_kz^k$ is a locally uniform
limit of real-rooted polynomials.

## Results

**Theorem (Hutchinson).** [@Hutchinson1923] If $a_k>0$ and $a_{k+1}^2\ge4a_ka_{k+2}$ for all
$k\ge0$, then $\sum_ka_kz^k$ is an entire function in the Laguerre–Pólya class: a locally
uniform limit of real polynomials, each zero or real-rooted.

**Proposition (closure).** The Laguerre–Pólya class is closed under locally uniform limits of
sequences.

## Use

This is the entire-function form of [Kurtz's criterion](/RealRooted/theorems/kurtz/), which
requires strict inequalities and concerns polynomials.

## Proof

The coefficients decay like $4^{-k^2/2}$, so the series is entire. On a disc we approximate by a
partial sum, and then by $\sum_{k<N}a_kq^{k^2}z^k$ with $q<1$ close to $1$; these polynomials
satisfy Kurtz's strict inequalities and so are real-rooted.

## References

See [@Hutchinson1923; @Kurtz1992].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Hutchinson`
and `RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure`.
-/
