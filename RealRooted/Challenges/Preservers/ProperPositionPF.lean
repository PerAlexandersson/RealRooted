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
preserves interlacing of PF polynomials, with zero outputs and degree drops allowed.

## Results

For $\gamma:\mathbb N\to\mathbb R$ let $\Gamma\bigl(\sum a_nx^n\bigr)=\sum\gamma_na_nx^n$. A
polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. We say $\gamma$ is a *finite PF multiplier sequence of degree $N$* if
$\Gamma$ maps PF polynomials of degree at most $N$ to PF polynomials, and a *finite
multiplier sequence of degree $N$* if $\Gamma$ maps real-rooted polynomials of degree at most
$N$ to zero or to real-rooted polynomials. We write $f\ll g$ for weak interlacing: either
polynomial may be zero, and repeated and common roots are allowed. `StrictInterl` is the
library predicate for nonzero real-rooted pairs; it allows repeated and common roots.

**Theorem (PF multipliers).** Let $\gamma$ be a finite PF multiplier sequence of degree $N$,
and let $f,g$ be PF polynomials of degree at most $N$ with $f\ll g$. Then
$\Gamma f\ll\Gamma g$. No top multiplier is assumed to be nonzero, and $\Gamma f$ or
$\Gamma g$ may vanish.

**Theorem (orientation).** Let $\gamma$ be a finite multiplier sequence of degree $N$, let
$f\ll g$ in the `StrictInterl` sense with $\deg f,\deg g\le N$, and suppose
$\gamma_{\deg f}\ne0$ and $\gamma_{\deg g}\ne0$. Put $d=\deg f$ and $\rho=\gamma_{d-1}/\gamma_d$,
reading $d-1$ as $0$ when $d=0$.

- If $\rho\ge0$, then $\Gamma f\ll\Gamma g$ in the `StrictInterl` sense.
- If $\deg g=d$ and $\rho\le0$, equivalently $\gamma_{d-1}\gamma_d\le0$, then
  $\Gamma g\ll\Gamma f$ in the `StrictInterl` sense.
- If $\deg g=d$ and $\rho=0$, both orientations hold.

**Theorem (weighted sums).** Let $\gamma$ be a multiplier sequence with $\gamma_k>0$ for all
$k$, let $h$ be a polynomial, and let $a_1,\dots,a_r\ge0$ with some $a_i>0$. Let
$p_1,\dots,p_r$ have positive leading coefficients. If $h\ll p_i$ for all $i$ in the
`StrictInterl` sense, then $\Gamma h\ll\sum_ia_i\,\Gamma p_i$ in the same sense. If
$p_i\ll h$ for all $i$, then $\sum_ia_i\,\Gamma p_i\ll\Gamma h$.

**Theorem (lists).** Let $\gamma$ be a finite PF multiplier sequence of degree $N$ and let
$f_1,\dots,f_r$ be polynomials of degree at most $N$ such that $f_i\ll f_j$ for $i<j$, every
$f_i$ has nonnegative coefficients, and every nonzero $f_i$ splits. Then
$\Gamma f_1,\dots,\Gamma f_r$ has the same three properties.

## References

See [@BorceaBranden2009I; @BorceaBranden2010; @Branden2015].
<!-- /realrooted-catalog-content -->
-/
