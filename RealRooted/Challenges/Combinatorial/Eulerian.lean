module

public import RealRooted.CombinatorialExamples.Eulerian
public import RealRooted.CombinatorialExamples.EulerianStatistic
public import RealRooted.CombinatorialExamples.TypeBEulerian
public import RealRooted.GeneralizedEulerian.GeneratingFunction
public import RealRooted.MaWang.DerivativeStep

public section

open Polynomial

/-!
# Eulerian polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "eulerian"
formalized = "2026-07-10"
references = [
  "Brenti1994",
]
authors = ["Frobenius", "Brenti"]
years = [1910, 1994]

[[definitions]]
name = "RealRooted.eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Eulerian polynomials"

[[definitions]]
name = "RealRooted.typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Type B Eulerian polynomials"

[[definitions]]
name = "RealRooted.generalizedEulerian"
module = "RealRooted.GeneralizedEulerian"
label = "Generalized Eulerian polynomials"

[[theorems]]
name = "RealRooted.isRealRooted_eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.interlaces_eulerianTilde_succ"
module = "RealRooted.CombinatorialExamples.Eulerian"
label = "Consecutive Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.isRealRooted_typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Type B Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.interlaces_typeBEulerian_succ"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "Consecutive type B Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.generalizedEulerian_splits"
module = "RealRooted.GeneralizedEulerian"
label = "Generalized Eulerian polynomials are real-rooted for c > 0"
headline = true

[[theorems]]
name = "RealRooted.interlaces_generalizedEulerian_succ"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "Consecutive generalized Eulerian polynomials interlace for c > 0"

[[theorems]]
name = "RealRooted.eulerianTilde_eq_X_mul_generalizedEulerian_one"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "The Eulerian polynomials are x times the case c = 1"

[[theorems]]
name = "RealRooted.typeBEulerian_eq_generalizedEulerian_two"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"
label = "The type B Eulerian polynomials are the case c = 2"

[[theorems]]
name = "RealRooted.GeneralizedEulerian.coeff_generalizedEulerian_one_eq_sum"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "Alternating-sum formula for the Eulerian coefficients"

[[theorems]]
name = "RealRooted.genPoly_univ_descentCount"
module = "RealRooted.CombinatorialExamples.EulerianStatistic"
label = "The descent generating polynomial of permutations is the Eulerian polynomial"

[[theorems]]
name = "RealRooted.isRealRooted_genPoly_univ_descentCount"
module = "RealRooted.CombinatorialExamples.EulerianStatistic"
label = "Permutations counted by descents give a real-rooted polynomial"
-->

<!-- realrooted-catalog-content -->
# Eulerian polynomials

The library defines the shifted Eulerian polynomials `eulerianTilde n` by the recurrence
$P_0 = t$ and $P_{n+1} = t\bigl((n+2) P_n + (1-t) P_n'\bigr)$. Classically, $P_n = t A_{n+1}(t)$,
where $A_n(t) = \sum_{\sigma \in \mathfrak{S}_n} t^{\operatorname{des}(\sigma)}$ counts
permutations by descents. This identification is formalized: the descent generating
polynomial of $\mathfrak S_{n+1}$ equals $E_n^{(1)}$ (`genPoly_univ_descentCount`) and is
real-rooted. The type $B$ Eulerian polynomials are likewise defined by the recurrence
$B_0 = 1$ and
$B_{n+1} = \bigl(1 + (2n+1)t\bigr) B_n + 2t(1-t) B_n'$.

Both families are real-rooted, and consecutive polynomials interlace.

For a real parameter $c$, the generalized Eulerian polynomials
`generalizedEulerian c n` are defined by $E_0^{(c)} = 1$ and
$$
E_{n+1}^{(c)} = \bigl(1 + (cn + 1)t\bigr) E_n^{(c)} + c\,t(1-t) \bigl(E_n^{(c)}\bigr)'.
$$
For $c > 0$ every $E_n^{(c)}$ is real-rooted, and consecutive members
interlace. Both families above are special cases:
$$
P_n = t\,E_n^{(1)}, \qquad B_n = E_n^{(2)}.
$$
The coefficients of $E_k^{(1)}$ are given by the alternating sum
$$
[t^j]\, E_k^{(1)} = \sum_{i=0}^{j+1} (-1)^{j+1-i} \binom{k+2}{j+1-i}\, i^{k+1}.
$$
This is the classical formula for the Eulerian numbers; by
`genPoly_univ_descentCount`, $[t^j]E_k^{(1)}$ is the number of permutations of
$k+1$ letters with $j$ descents.

## References

The ordinary Eulerian recurrence and its real-rootedness go back to F. G. Frobenius,
“Über die Bernoullischen Zahlen und die Eulerschen Polynome,” *Sitzungsberichte der
Königlich Preussischen Akademie der Wissenschaften* (1910), 809–847. For type $B$,
see [@Brenti1994]. See also the
[Eulerian polynomials on symmetricfunctions.com](sf:eulerianPolynomial).
<!-- /realrooted-catalog-content -->

Human statements:

* Eulerian polynomials:
  sf:eulerianPolynomial
* Eulerian Sturm sequence example:
  sf:ex:eulerianSturm
* Type `B` Eulerian polynomials:
  sf:typeBEulerianPolynomial

Classical origin: F. G. Frobenius, "Über die Bernoullischen Zahlen und die
Eulerschen Polynome", Sitzungsberichte der Königlich Preussischen Akademie der
Wissenschaften (1910), 809--847.

This module exposes the checked ordinary and type `B` Eulerian real-rootedness
and interlacing statements, together with the corresponding Sturm-prefix API.
-/

namespace RealRooted
namespace Challenges
namespace Eulerian

/-- Ordinary Eulerian tilde polynomials are real-rooted. -/
theorem realRooted (n : ℕ) : eulerianTilde n ≠ 0 ∧ (eulerianTilde n).Splits :=
  RealRooted.isRealRooted_eulerianTilde n

/-- Consecutive ordinary Eulerian tilde polynomials interlace. -/
theorem interlaces_succ (n : ℕ) : Interlaces (eulerianTilde n) (eulerianTilde (n + 1)) :=
  RealRooted.interlaces_eulerianTilde_succ n

/-- Descending ordinary Eulerian prefixes form Sturm sequences. -/
theorem sturmPrefix (n : ℕ) : IsSturmSeq (eulerianTildePrefix n) :=
  RealRooted.isSturmSeq_eulerianTildePrefix n

/-- Type `B` Eulerian polynomials are real-rooted. -/
theorem typeB_realRooted (n : ℕ) : typeBEulerian n ≠ 0 ∧ (typeBEulerian n).Splits :=
  RealRooted.isRealRooted_typeBEulerian n

/-- Consecutive type `B` Eulerian polynomials interlace. -/
theorem typeB_interlaces_succ (n : ℕ) :
    Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) :=
  RealRooted.interlaces_typeBEulerian_succ n

/-- Descending type `B` Eulerian prefixes form Sturm sequences. -/
theorem typeB_sturmPrefix (n : ℕ) : IsSturmSeq (typeBEulerianPrefix n) :=
  RealRooted.isSturmSeq_typeBEulerianPrefix n

end Eulerian
end Challenges
end RealRooted
