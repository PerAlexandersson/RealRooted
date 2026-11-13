module

import RealRooted.MultiplierSequence.ProperPositionPF

/-!
# Diagonal operators of PF multiplier sequences and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "pf-multiplier-proper-position"
formalized = "2026-10-11"
authors = ["Borcea", "Brändén"]
tags = []
references = [
  "BorceaBranden2009I",
  "BorceaBranden2010",
  "Branden2015",
]

[[theorems]]
name = "RealRooted.IsFinitePFMultiplierSequence.interl_diagonalOperator"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Finite PF multipliers preserve directed interlacing"
headline = true

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Nonpositive adjacent multipliers reverse strict interlacing"

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_of_ratio_nonneg"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Nonnegative ratio preserves strict orientation"

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse_of_ratio_nonpos"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Nonpositive ratio reverses strict orientation"

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_both_of_ratio_eq_zero"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Zero ratio gives both strict orientations"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.strictInterl_weightedSum_left_of_pos"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Positive multipliers preserve common-left weighted sums"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.strictInterl_weightedSum_right_of_pos"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Positive multipliers preserve common-right weighted sums"

[[theorems]]
name = "RealRooted.IsInterlacingSeq0NonnegRealRooted.diagonalOperator_of_finitePF"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Finite PF multipliers preserve ordered PF lists"
-->

<!-- realrooted-catalog-content -->
# Diagonal operators of PF multiplier sequences and interlacing

A diagonal operator $x^n\mapsto\gamma_nx^n$ coming from a finite PF multiplier sequence
preserves interlacing of PF polynomials. For [multiplier sequences](rr:multiplier-sequences) of
real-rootedness, the orientation of the image pair is decided by the sign of one ratio
$\gamma_{d-1}/\gamma_d$.

## Results

For $\gamma:\mathbb N\to\mathbb R$ let $\Gamma\bigl(\sum a_nx^n\bigr)=\sum\gamma_na_nx^n$. A
polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. We say $\gamma$ is a *finite PF multiplier sequence of degree $N$* if
$\Gamma$ maps PF polynomials of degree at most $N$ to PF polynomials, and a *finite
multiplier sequence of degree $N$* if $\Gamma$ maps real-rooted polynomials of degree at most
$N$ to zero or to real-rooted polynomials. On this page $f\ll g$ also holds when $f$ or $g$ is
zero, as in the [zero-aware convention](rr:about), unless $f$ and $g$ are said to be nonzero.

**Theorem (PF multipliers).** Let $\gamma$ be a finite PF multiplier sequence of degree $N$,
and let $f,g$ be PF polynomials of degree at most $N$ with $f\ll g$. Then
$\Gamma f\ll\Gamma g$.

**Theorem (orientation).** Let $\gamma$ be a finite multiplier sequence of degree $N$, let
$f\ll g$ be nonzero with $\deg f,\deg g\le N$, and suppose $\gamma_{\deg f}\ne0$ and
$\gamma_{\deg g}\ne0$. Put $d=\deg f$ and $\rho=\gamma_{d-1}/\gamma_d$, reading $d-1$ as $0$
when $d=0$.

- If $\rho\ge0$, then $\Gamma f\ll\Gamma g$.
- If $\deg g=d$ and $\rho\le0$, equivalently $\gamma_{d-1}\gamma_d\le0$, then
  $\Gamma g\ll\Gamma f$.
- If $\deg g=d$ and $\rho=0$, both orientations hold.

In each case the images are nonzero.

**Theorem (weighted sums).** Let $\gamma$ be a multiplier sequence with $\gamma_k>0$ for all
$k$, let $h$ be a nonzero polynomial, and let $a_1,\dotsc,a_r\ge0$ with some $a_i>0$. Let
$p_1,\dotsc,p_r$ have positive leading coefficients. If $h\ll p_i$ for all $i$, then
$\Gamma h\ll\sum_ia_i\,\Gamma p_i$, and both sides are nonzero. If $p_i\ll h$ for all $i$, then
$\sum_ia_i\,\Gamma p_i\ll\Gamma h$.

**Theorem (lists).** Let $\gamma$ be a finite PF multiplier sequence of degree $N$ and let
$f_1,\dotsc,f_r$ be polynomials of degree at most $N$ such that $f_i\ll f_j$ for $i<j$, every
$f_i$ has nonnegative coefficients, and every nonzero $f_i$ is real-rooted. Then
$\Gamma f_1,\dotsc,\Gamma f_r$ has the same three properties.

## References

- [@BorceaBranden2009I]
- [@BorceaBranden2010]
- [@Branden2015]
<!-- /realrooted-catalog-content -->
-/
