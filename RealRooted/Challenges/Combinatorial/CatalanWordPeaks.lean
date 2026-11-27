module

import RealRooted.CombinatorialExamples.CatalanWordPeaks.Main
import RealRooted.CombinatorialExamples.CatalanWordPeaks.GeneratingFunction

/-!
# Strict peaks of Catalan words

<!-- realrooted-catalog
version = 1
kind = "conjecture"
conjecture = "Alexandersson (2026), peaks of Catalan words"
section = "theorems"
slug = "catalan-word-peaks"
formalized = "2026-11-27"
references = [
  "ProgramComputer2026CatalanPeaks",
  "BarilHarrisHarryMcClintonRamirez2025",
]
authors = ["ProgramComputer"]
years = [2026]
symcat = ["conjCatalanWordPeaks"]

[[definitions]]
name = "RealRooted.CatalanWordPeaks.polynomial"
module = "RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic"
label = "The peak polynomial $C_n(t)$ of Catalan words, by its $(t-1)$-expansion"

[[theorems]]
objects = ["Peak polynomials of Catalan words"]
property = "real-rooted"
name = "RealRooted.CatalanWordPeaks.all_lengths"
module = "RealRooted.CombinatorialExamples.CatalanWordPeaks.Main"
label = "ProgramComputer: simple negative zeros and strict interlacing of $C_n$, $C_{n+1}$"
headline = true

[[theorems]]
name = "RealRooted.CatalanWordPeaks.polynomial_roots"
module = "RealRooted.CombinatorialExamples.CatalanWordPeaks.Main"
label = "$C_n$ has $\\lfloor (n-1)/2\\rfloor$ simple negative zeros"

[[theorems]]
name = "RealRooted.CatalanWordPeaks.polynomial_strictInterl"
module = "RealRooted.CombinatorialExamples.CatalanWordPeaks.Main"
label = "$C_n$ and $C_{n+1}$ strictly interlace; the rightmost zero belongs to $C_{n+1}$"

[[theorems]]
name = "RealRooted.CatalanWordPeaks.GeneratingFunction.series_eq"
module = "RealRooted.CombinatorialExamples.CatalanWordPeaks.GeneratingFunction"
label = "The rows satisfy $G=1+(1-t)x^2G+x(1-x+tx)G^2$"
-->

<!-- realrooted-catalog-content -->
# Strict peaks of Catalan words

A Catalan word $w_1\dotsm w_n$ has $w_1=0$ and $0\le w_{i+1}\le w_i+1$. Let $C_n(t)$ count these
words by strict peaks $w_{i-1}<w_i>w_{i+1}$. Then
$$
C_n(t)=\sum_{i\ge0}\frac{1}{n-i}\binom{n-i}{i}\binom{2n-3i}{n-2i-1}(t-1)^i ,
$$
and the generating function was found by Baril, Harris, Harry, McClinton and Ramírez
[@BarilHarrisHarryMcClintonRamirez2025]. Alexandersson conjectured that $C_n$ is real-rooted and
that consecutive rows interlace.

## Results

**Theorem (ProgramComputer).** For every $n$, $C_n$ has only simple negative zeros, and $C_n$ and
$C_{n+1}$ strictly interlace with no common zero; the rightmost zero belongs to $C_{n+1}$
[@ProgramComputer2026CatalanPeaks].

The rows are defined here by the coefficient formula above; the identification with word counts
is the enumeration of Baril et al. and is not formalized.

## Proof

For $n\ge150$ the coefficients of the algebraic generating function are written as integrals
along four branch cuts. Beta-type moment bounds then fix the sign of $C_{n+1}$ at every zero of
$C_n$: the interior zeros through a phase function, the two extreme zeros through a pole
evaluation and Vieta's formulas. Exact interval certificates cover $n<150$.

Ported from ProgramComputer's formalization (ISC licence), with the word model replaced by the
coefficient formula, smaller finite certificates, and standard interlacing criteria.

## References

[@ProgramComputer2026CatalanPeaks, Thm. 1]; [@BarilHarrisHarryMcClintonRamirez2025].
<!-- /realrooted-catalog-content -->
-/
