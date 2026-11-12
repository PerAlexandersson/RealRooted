module

import RealRooted.FiniteMemory.Defect

/-!
# Finite-memory degree-defect bridges

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-memory-defect-bridges"
formalized = "2026-10-11"
authors = ["Bøgvad", "Hägg", "Nyandwi", "Kurujyibwami", "Uwimbabazi"]
tags = []
references = [
  "BogvadHagg2017",
  "NyandwiHaggKurujyibwamiUwimbabazi2026x",
]

[[definitions]]
name = "RealRooted.FiniteMemory.sharpResidueMinimizers_of_setGcd_eq_one"
module = "RealRooted.FiniteMemory.Defect"
label = "Coprime active lags produce sharp residue-defect bridges"

[[theorems]]
name = "RealRooted.HasNonnegCoeffs.natDegree_add_eq_max"
module = "RealRooted.FiniteMemory.Defect"
label = "Nonnegative sums have maximal degree"

[[theorems]]
name = "RealRooted.HasNonnegCoeffs.natTrailingDegree_add_eq_min"
module = "RealRooted.FiniteMemory.Defect"
label = "Nonnegative sums have minimal trailing degree"

[[theorems]]
name = "RealRooted.FiniteMemory.symbolSeries_mul_one_sub_lagSeries"
module = "RealRooted.FiniteMemory.Defect"
label = "Fundamental symbol-series identity"

[[theorems]]
name = "RealRooted.FiniteMemory.symbolRow_eq_sum_mul_coeff_lagSeries"
module = "RealRooted.FiniteMemory.Defect"
label = "Fundamental-row convolution recurrence"

[[theorems]]
name = "RealRooted.FiniteMemory.symbolRow_hasNonnegCoeffs"
module = "RealRooted.FiniteMemory.Defect"
label = "Fundamental rows have nonnegative coefficients"

[[theorems]]
name = "RealRooted.FiniteMemory.SharpResidueMinimizers.exists_exact_minimizer"
module = "RealRooted.FiniteMemory.Defect"
label = "Sharp bridges give eventual minimum-cost words"
headline = true

[[theorems]]
name = "RealRooted.FiniteMemory.SharpResidueMinimizers.exists_upper_degree_word"
module = "RealRooted.FiniteMemory.Defect"
label = "Sharp bridges give scaled upper-degree words"

[[theorems]]
name = "RealRooted.FiniteMemory.SharpResidueMinimizers.exists_lower_degree_word"
module = "RealRooted.FiniteMemory.Defect"
label = "Sharp bridges give scaled lower-degree words"

[[theorems]]
name = "RealRooted.FiniteMemory.exists_fractional_upper_degree_word"
module = "RealRooted.FiniteMemory.Defect"
label = "The fractional (2, 3) upper-degree bridge"
-->

<!-- realrooted-catalog-content -->
# Finite-memory degree-defect bridges

For a finite-memory symbol whose active lags have gcd one, every index beyond an explicit
threshold has a lag word of minimum residue cost, and this gives exact degree identities for
the fundamental rows.

## Results

**Proposition (no cancellation).** Let $p,q\in\mathbb R[x]$ be nonzero with nonnegative
coefficients. Then $\deg(p+q)=\max(\deg p,\deg q)$, and the trailing degree of $p+q$ is the
minimum of the trailing degrees of $p$ and $q$.

**Proposition (fundamental rows).** Let $p_1,\dots,p_r\in\mathbb R[x]$ be the symbol, with
lag series $\Lambda(t)=\sum_{i=1}^r p_i\,t^i$. The symbol series is $S(t)=(1-\Lambda(t))^{-1}$
over $\mathbb R[x]$, and its coefficients $S_n$ are the fundamental rows, so that $S_0=1$ and
$$
S_n=\sum_{i+j=n}S_i\,[t^j]\Lambda \qquad(n\ge1).
$$
If all $p_i$ have nonnegative coefficients, then so does every $S_n$.

**Definition (lag words and bridges).** For a set $\mathcal L$ of active lags and a cost function
$\delta$, a lag word is a list of lags $l\in\mathcal L$ with $1\le l\le r$. Its lag is the sum
of its entries and its cost is the sum of their costs. A *sharp bridge* for $(r,p,q,\mathcal
L,\delta,K)$
consists of a zero-cost lag $p\in\mathcal L$ with $p\le r$, a divisor $q$ of $p$ and, for each
residue modulo
$p$, a lag word in that residue class whose cost is $K(\text{lag}\bmod q)$, whose lag $\ell$
satisfies $\ell+1\le(r-1)(r-2)+p$, and such that every lag word has cost at least
$K(\text{lag}\bmod q)$.

**Theorem (sharp bridges from coprime lags).** Let $\mathcal L\subseteq[1,r]$ have gcd one and let
$p\in\mathcal L$ with
$p\le r$ and $\delta(p)=0$. Let $q$ be the gcd of the zero-cost active lags and let $K(a)$ be the
least cost of a lag word whose lag is congruent to $a$ modulo $q$. Then these data form a sharp
bridge.

**Theorem (exact words).** Let a sharp bridge be given and let $n\ge(r-1)(r-2)$. Then there is
a lag word of lag $n$ and cost $K(n\bmod q)$, and no lag word of lag $n$ has smaller cost. If
$\delta(l)+B\,d(l)=A\,l$ for all $l\in\mathcal L$, then some lag word $w$ of lag $n$ satisfies
$B\sum_{l\in w}d(l)+K(n\bmod q)=A\,n$. If $e(l)+C\,l=D\,t(l)$ for all $l\in\mathcal L$, then some
lag
word $w$ of lag $n$ satisfies $D\sum_{l\in w}t(l)=C\,n+K(n\bmod q)$.

**Example (lags $2$ and $3$).** Let $\mathcal L=\{2,3\}$, $r=3$, $\delta(2)=1$ and $\delta(3)=0$,
and
let $K_0,K_1,K_2=0,2,1$. For $n\ge2$ there is a lag word $w$ of lag $n$ with
$$
3\sum_{l\in w}d(l)+K_{n\bmod3}=2n,\qquad d(2)=1,\ d(3)=2 .
$$

## References

See [@BogvadHagg2017; @NyandwiHaggKurujyibwamiUwimbabazi2026x].
<!-- /realrooted-catalog-content -->
-/
