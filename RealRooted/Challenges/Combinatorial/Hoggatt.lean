module

public import RealRooted.CombinatorialExamples.Hoggatt
public import RealRooted.Applications.OEIS.A056939

/-!
# Hoggatt polynomials and Baxter permutations

<!-- realrooted-catalog
version = 1
section = "families"
slug = "hoggatt"
formalized = "2026-11-13"
authors = ["Fang", "Zhang", "Zhao", "Dilks"]
years = [2015, 2025]

[[definitions]]
name = "RealRooted.Hoggatt.polynomial"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The binomial-product polynomial F(n,m)"

[[definitions]]
name = "RealRooted.Hoggatt.normalized"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "Normalized Hoggatt polynomials H_n^[m]"

[[theorems]]
name = "RealRooted.Hoggatt.normalized_interlaces_and_isCoprime"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "For every m ≥ 2, consecutive Hoggatt rows strictly interlace"
headline = true

[[theorems]]
name = "RealRooted.Hoggatt.polynomial_pred_interlaces"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "F(n−1,m) strictly interlaces F(n,m) for n ≥ m ≥ 2"

[[theorems]]
name = "RealRooted.Hoggatt.derivative_auxiliary"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The Hadamard derivative identity G'(n+1,m+1) = (n+1) F(n,m+1)"

[[theorems]]
name = "RealRooted.Hoggatt.derivative_hadamard_one"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The derivative identity at m = 2"

[[theorems]]
name = "RealRooted.Hoggatt.normalized_splits"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "Every Hoggatt polynomial is real-rooted, for all m ≥ 1"

[[theorems]]
name = "RealRooted.Hoggatt.normalized_one"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The m = 1 family consists of powers of X + 1"

[[theorems]]
name = "RealRooted.Hoggatt.hasSimpleRoots_polynomial"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The binomial-product polynomials have simple roots for m ≥ 2"

[[theorems]]
name = "RealRooted.Hoggatt.baxter_interlaces"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "Baxter polynomials are a strict Sturm sequence"

[[theorems]]
name = "RealRooted.Hoggatt.normalized_three_eq_baxter"
label = "The m = 3 specialization equals the existing Baxter recurrence model"

[[theorems]]
name = "RealRooted.Applications.OEIS.A056939.polynomial_isCoprime_succ"
label = "Consecutive rows of the existing A056939 model are coprime"
-->

<!-- realrooted-catalog-content -->
# Hoggatt polynomials form a Sturm sequence

For positive integers $m$ we set
\[
F_{n,m}(t)=\sum_{k=0}^{n-m+1}
  \left(\prod_{i=0}^{m-1}\binom{n}{k+i}\right)t^k,
\]
and normalize by its positive constant coefficient to obtain
$H_n^{[m]}(t)=F_{n+m-2,m}(t)/F_{n+m-2,m}(0)$ for $n\ge1$.
MacMahon's formula identifies the coefficient of $t^k$ with plane partitions
in a $k\times(n-1-k)\times m$ box. The checked statements concern the explicit
binomial-product polynomials; the combinatorial identification is documentation.

**Theorem (Fang–Zhang–Zhao).** For every $m\ge2$, consecutive Hoggatt
polynomials strictly interlace. All roots are simple and negative. We record
strictness as the conjunction of the library's degree-gap-one `Interlaces`
predicate and `IsCoprime`; `StrictInterl` alone permits shared roots.
For $m=1$ we obtain $(1+t)^{n-1}$ and a generalized Sturm sequence.
Real-rootedness for all $m\ge1$ recovers Dilks's theorem.

We use the existing Garloff–Wagner Hadamard theorem and derivative-interlacing
theory. For $G_{n+1,m+1}=F_{n+1,1}*F_{n,m}$, coefficient comparison gives
$G'_{n+1,m+1}=(n+1)F_{n,m+1}$. Induction gives the weak root ordering.
The additional strict corollary needed here rules out common roots for
Hadamard products with consecutive binomial powers. Its proof combines
Hadamard simplicity with the adjacent-binomial differential identity.
Global Wronskian positivity supplies Markov's strict derivative step.

At $m=3$ the normalized polynomials are Baxter descent polynomials. The
checked equality identifies $H_{n+1}^{[3]}$ with row $n$ of the existing
A056939 recurrence and Schur model. Thus that model inherits coprimality
of consecutive rows as well as its existing interlacing theorem.

## References

- H. Fang, C. X. T. Zhang, J. J. Y. Zhao,
  [*Analytic properties arising from the Baxter numbers*](https://arxiv.org/abs/2505.05873),
  2025, Theorems 1–2 and §2.
- K. Dilks, *Involutions on Baxter Objects, and q-Gamma Nonnegativity*,
  Ph.D. thesis, University of Minnesota, 2015, Theorem 3.8.
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Hoggatt

/-- The normalized `m = 3` Hoggatt polynomial agrees with the existing
A056939 model, whose row `n` is indexed by Baxter permutations on `n+1` letters. -/
theorem normalized_three_eq_baxter (n : ℕ) :
    normalized (n + 1) 3 = Applications.OEIS.A056939.polynomial n := by
  rw [normalized_three_eq_binomial_sum, Applications.OEIS.A056939.polynomial_eq_binomial_sum]

end RealRooted.Hoggatt

namespace RealRooted.Applications.OEIS.A056939

/-- Strictness for the existing Baxter model: consecutive rows have no shared root. -/
theorem polynomial_isCoprime_succ (n : ℕ) :
    IsCoprime (polynomial n) (polynomial (n + 1)) := by
  have h := Hoggatt.baxter_interlaces (Nat.succ_ne_zero n)
  simpa only [Hoggatt.normalized_three_eq_baxter] using h.2

end RealRooted.Applications.OEIS.A056939
