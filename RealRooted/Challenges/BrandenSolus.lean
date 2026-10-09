import RealRooted.SymmetricDecomposition
import RealRooted.CombinatorialExamples.DerangementStatistic
import RealRooted.SymmetricDecomposition.DerangementTransform

open Polynomial

/-!
# Branden--Solus challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-solus"
authors = ["Brändén", "Solus"]
years = [2019]

[[definitions]]
name = "RealRooted.IsIdDecomposition"
module = "RealRooted.SymmetricDecomposition.Definitions"
label = "Symmetric I_d-decomposition"

[[theorems]]
name = "RealRooted.Challenges.BrandenSolus.interlacing_equivalences"
label = "Interlacing equivalences for the I_d-decomposition"

[[definitions]]
name = "RealRooted.DerangementTransform.transform"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "Derangement transform x^j ↦ d_j"

[[theorems]]
name = "RealRooted.DerangementTransform.transform_magicExpansion_isPF"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "Nonnegative magic-basis coordinates give a real-rooted derangement image"

[[theorems]]
name = "RealRooted.DerangementTransform.transform_magicExpansion_strictInterl"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "The derangement image lies between A_d and d_d"

[[theorems]]
name = "RealRooted.DerangementStatistic.derangementExcGenPoly_eq_polynomial"
module = "RealRooted.CombinatorialExamples.DerangementStatistic"
label = "Derangements counted by excedances give the derangement polynomials d_n"

[[theorems]]
name = "RealRooted.DerangementStatistic.derangementExcGenPoly_isRealRooted"
module = "RealRooted.CombinatorialExamples.DerangementStatistic"
label = "The excedance polynomial of derangements is real-rooted"
-->

<!-- realrooted-catalog-content -->
# Brändén–Solus symmetric decomposition

The $I_d$-decomposition writes a polynomial $p$ of degree at most $d$ as
$p = a + Xb$ with reciprocal symmetry conditions on $a$ and $b$. If $a$ and $b$
are nonzero with nonnegative coefficients, then $b \ll a$, $a \ll p$ and
$b \ll p$ are equivalent. They are also equivalent to $I_d(p) \ll p$, and to
$R_d(f) \ll f$ for the associated polynomial $f$ (`fPolynomial d p`).

The derangement transform $D : x^j \mapsto d_j(x)$ sends every polynomial with nonnegative
coordinates in the basis $x^k(1+x)^{d-k}$ to a real-rooted polynomial lying between the
Eulerian polynomial $A_d$ and the derangement polynomial $d_d$ (Brändén–Solus, Corollary 3.7).
Here it is derived from the Brändén–Vecchi Chow-resolution theorem for the Pascal matrix,
whose resolving rows are exactly $x^k(1+x)^{d-k}$.

The derangement polynomials are defined by a recurrence. Their combinatorial meaning is
formalized: $d_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over the
derangements of $n$ letters, where $\operatorname{exc}$ counts excedances $i < \sigma(i)$.
The proof establishes the excedance recurrence by removing the letter $0$ from a derangement.

## References

P. Brändén and L. Solus, “Symmetric decompositions and real-rootedness,”
*International Mathematics Research Notices* 2021 (2021), 7764–7798.  See the
[symmetric-decomposition overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#symmetricIDecomposition).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#symmetricIDecomposition

Original publication: P. Branden and L. Solus, "Symmetric decompositions and
real-rootedness", International Mathematics Research Notices 2021 (2019),
7764--7798.

This module exposes the completed nondegenerate `StrictInterl` form of the
Branden--Solus symmetric-decomposition theorem.  The decomposition API and
boundary-case proof remain in `RealRooted.SymmetricDecomposition`.
-/

namespace RealRooted
namespace Challenges
namespace BrandenSolus

/-- Interlacing equivalences for the symmetric `I_d`-decomposition `p = a + X b`. -/
theorem interlacing_equivalences {d : ℕ} {p a b : ℝ[X]} (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b) (ha : HasNonnegCoeffs a) (hb : HasNonnegCoeffs b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (StrictInterl b a ↔ StrictInterl a p) ∧
      (StrictInterl a p ↔ StrictInterl b p) ∧
      (StrictInterl b p ↔ StrictInterl (idTransform d p) p) ∧
      (StrictInterl (idTransform d p) p ↔
        StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p)) :=
  RealRooted.BrandenSolus.strictInterl_iff_of_isIdDecomposition hd hid ha hb ha0 hb0

end BrandenSolus
end Challenges
end RealRooted
