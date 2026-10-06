import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.CombinatorialExamples.TypeBEulerian
import RealRooted.GeneralizedEulerian.GeneratingFunction
import RealRooted.MaWang.DerivativeStep

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

[[definitions]]
name = "RealRooted.generalizedEulerian"
module = "RealRooted.GeneralizedEulerian"
label = "Generalized Eulerian polynomials"

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

[[theorems]]
name = "RealRooted.generalizedEulerian_splits"
module = "RealRooted.GeneralizedEulerian"
label = "Generalized Eulerian polynomials are real-rooted for c > 0"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Eulerian.interlaces_generalizedEulerian_succ"
label = "Consecutive generalized Eulerian polynomials interlace for c > 0"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.eulerianTilde_eq_X_mul_generalizedEulerian_one"
label = "The Eulerian polynomials are x times the case c = 1"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.typeBEulerian_eq_generalizedEulerian_two"
label = "The type B Eulerian polynomials are the case c = 2"

[[theorems]]
name = "RealRooted.GeneralizedEulerian.coeff_generalizedEulerian_one_eq_sum"
module = "RealRooted.GeneralizedEulerian.GeneratingFunction"
label = "Alternating-sum formula for the Eulerian coefficients"
-->

<!-- realrooted-catalog-content -->
# Eulerian polynomials

The library defines the shifted Eulerian polynomials `eulerianTilde n` by the recurrence
$P_0 = t$ and $P_{n+1} = t\bigl((n+2) P_n + (1-t) P_n'\bigr)$. Classically, $P_n = t A_{n+1}(t)$,
where $A_n(t) = \sum_{\sigma \in \mathfrak{S}_n} t^{\operatorname{des}(\sigma)}$ counts
permutations by descents; this identification is cited, not formalized. The type $B$
Eulerian polynomials are likewise defined by the recurrence $B_0 = 1$ and
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
This is the classical formula for the Eulerian numbers; the descent count
itself is still not formalized.

## References

The ordinary Eulerian recurrence and its real-rootedness go back to
F. G. Frobenius, “Über die Bernoullischen Zahlen und die Eulerschen Polynome,”
Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften
(1910), 809–847.  For type $B$, see F. Brenti, [“q-Eulerian polynomials arising
from Coxeter groups,”](https://doi.org/10.1006/eujc.1994.1046) *European Journal
of Combinatorics* 15 (1994), 417–441.  See also the
[Eulerian polynomials on symmetricfunctions.com](https://www.symmetricfunctions.com/eulerian.htm#eulerianPolynomial).
<!-- /realrooted-catalog-content -->

Human statements:

* Eulerian polynomials:
  https://www.symmetricfunctions.com/eulerian.htm#eulerianPolynomial
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

/-- The ordinary Eulerian polynomials are `X` times the generalized Eulerian polynomials at
`c = 1`. -/
theorem eulerianTilde_eq_X_mul_generalizedEulerian_one (n : ℕ) :
    eulerianTilde n = X * generalizedEulerian 1 n := by
  induction n with
  | zero => simp [generalizedEulerian]
  | succ n ih =>
    rw [eulerianTilde_recurrence, generalizedEulerian_succ, ih, derivative_mul, derivative_X]
    simp only [one_mul, map_add, map_natCast, map_one, map_ofNat]
    ring

/-- The type `B` Eulerian polynomials are the generalized Eulerian polynomials at `c = 2`. -/
theorem typeBEulerian_eq_generalizedEulerian_two (n : ℕ) :
    typeBEulerian n = generalizedEulerian 2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typeBEulerian_succ, generalizedEulerian_succ, ih, typeBEulerianCoeffA,
      typeBEulerianCoeffB]

/-- For `c > 0`, consecutive generalized Eulerian polynomials interlace. -/
theorem interlaces_generalizedEulerian_succ {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Interlaces (generalizedEulerian c n) (generalizedEulerian c (n + 1)) := by
  obtain ⟨hdeg, hnonneg, hsplit⟩ := generalizedEulerian_invariants hc n
  have hpos : ∀ k, HasPosLeadingCoeff (generalizedEulerian c k) := fun k ↦ by
    simp [HasPosLeadingCoeff, (generalizedEulerian_monic c k).leadingCoeff]
  have hdeg' := generalizedEulerian_natDegree c (n + 1)
  have hstep : StrictInterl (generalizedEulerian c n) (generalizedEulerian c (n + 1)) := by
    have hpos' := hpos (n + 1)
    have hdeg'' := hdeg'
    rw [generalizedEulerian_succ] at hpos' hdeg'' ⊢
    refine MaWang.strictInterl_derivative_of_nonpos_of_splits hsplit (by lia) (by lia) hpos'
      (hpos n) fun r hr ↦ ?_
    have hr0 : r ≤ 0 :=
      roots_nonpos_of_hasNonnegCoeffs hnonneg r ((mem_roots (hpos n).ne_zero).mpr hr)
    simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc.le hr0)
      (by linarith)
  exact hstep.toInterlaces (by rw [hdeg, hdeg'])

end Eulerian
end Challenges
end RealRooted
