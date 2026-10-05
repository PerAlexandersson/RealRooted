import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.CombinatorialExamples.TypeBEulerian

open Polynomial

/-!
# Eulerian polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "eulerian"
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

[[theorems]]
name = "RealRooted.Challenges.Eulerian.realRooted"
label = "Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Eulerian.interlaces_succ"
label = "Consecutive Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.typeB_realRooted"
label = "Type B Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Eulerian.typeB_interlaces_succ"
label = "Consecutive type B Eulerian polynomials interlace"
-->

<!-- realrooted-catalog-content -->
# Eulerian polynomials

Let $A_n(t) = \sum_{\sigma \in \mathfrak{S}_n} t^{\operatorname{des}(\sigma)}$ be the Eulerian
polynomial. The library uses the shifted version `eulerianTilde n` $= t A_{n+1}(t)$, which satisfies
$P_0 = t$ and $P_{n+1} = t\bigl((n+2) P_n + (1-t) P_n'\bigr)$. The type $B$ Eulerian polynomials
satisfy $B_0 = 1$ and $B_{n+1} = \bigl(1 + (2n+1)t\bigr) B_n + 2t(1-t) B_n'$.

Both families are real-rooted, and consecutive polynomials interlace.

## References

The ordinary Eulerian recurrence and its real-rootedness go back to
F. G. Frobenius, “Über die Bernoullischen Zahlen und die Eulerschen Polynome,”
Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften
(1910), 809–847.  For type $B$, see F. Brenti, [“q-Eulerian polynomials arising
from Coxeter groups,”](https://doi.org/10.1006/eujc.1994.1046) *European Journal
of Combinatorics* 15 (1994), 417–441.  See also the
[Eulerian polynomials on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedWords.htm#eulerianPolynomial).
<!-- /realrooted-catalog-content -->

Human statements:

* Eulerian polynomials:
  https://www.symmetricfunctions.com/realRootedWords.htm#eulerianPolynomial
* Eulerian Sturm sequence example:
  https://www.symmetricfunctions.com/realRootedWords.htm#ex:eulerianSturm
* Type `B` Eulerian polynomials:
  https://www.symmetricfunctions.com/realRootedWords.htm#typeBEulerianPolynomial

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
