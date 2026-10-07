import RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya

/-!
# Eneström–Kakeya challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "enestrom-kakeya"
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

**Theorem.** If $0 < a_0 \leq a_1 \leq \dotsb \leq a_n$, then every complex
zero $z$ of $a_0 + a_1 z + \dotsb + a_n z^n$ satisfies $|z| \leq 1$.

More generally, if every coefficient is positive and
$m \leq a_i / a_{i+1} \leq M$ for all $i$, then every zero lies in the
annulus $m \leq |z| \leq M$.

## Proof idea

Multiply by $z - 1$. The product is
$a_n z^{n+1} - \sum_k (a_k - a_{k-1}) z^k - a_0$, whose middle coefficients
are nonnegative and sum, together with $a_0$, to $a_n$. For $|z| > 1$ the
triangle inequality bounds the lower terms by $a_n |z|^n < a_n |z|^{n+1}$.
The annulus form follows by rescaling $z \mapsto Mz$ and by reversing the
coefficients.

## References

G. Eneström, *Härledning af en allmän formel för antalet pensionärer …*,
Öfversigt af Kongl. Vetenskaps-Akademiens Förhandlingar 50 (1893);
S. Kakeya, *On the limits of the roots of an algebraic equation with positive
coefficients*, Tôhoku Math. J. 2 (1912), 140–142.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya`.
-/
