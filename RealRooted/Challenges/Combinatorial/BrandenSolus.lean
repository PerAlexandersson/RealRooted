module

public import RealRooted.SymmetricDecomposition
public import RealRooted.CombinatorialExamples.DerangementStatistic
public import RealRooted.SymmetricDecomposition.DerangementTransform
import RealRooted.SymmetricDecomposition.Theorem26
public import RealRooted.SymmetricDecomposition.FPolynomial
public import RealRooted.SymmetricDecomposition.Definitions

public section

open Polynomial

/-!
# Branden--Solus challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-solus"
formalized = "2026-10-02"
references = [
  "BrandenSolus2019",
]
authors = ["Brändén", "Solus"]
years = [2019]

[[definitions]]
name = "RealRooted.IsIdDecomposition"
module = "RealRooted.SymmetricDecomposition.Definitions"
label = "Symmetric I_d-decomposition"

[[theorems]]
name = "RealRooted.Challenges.BrandenSolus.interlacing_equivalences"
label = "Interlacing equivalences for the I_d-decomposition"
headline = true

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
label = "The excedance polynomial of derangements is real-rooted for n ≥ 2"
headline = true
-->

<!-- realrooted-catalog-content -->
# Brändén–Solus symmetric decomposition

The $I_d$-decomposition writes a polynomial $p$ of degree at most $d$ as
$p = a + Xb$ with reciprocal symmetry conditions on $a$ and $b$. If $a$ and $b$
are nonzero with nonnegative coefficients, then $b \ll a$, $a \ll p$ and
$b \ll p$ are equivalent. They are also equivalent to $I_d(p) \ll p$, and to
$R_d(f) \ll f$ for the associated polynomial $f$ (`fPolynomial d p`).
Here $u\ll v$ means that $u$ interlaces $v$, with the largest zero in $v$ and
shared zeros allowed. We use
$I_d(p)=x^d p(1/x)$, $R_d(p)(x)=(-1)^d p(-1-x)$, and
$f=\sum_k p_kx^k(1+x)^{d-k}$.

The derangement transform $D : x^j \mapsto d_j(x)$ sends every polynomial with nonnegative
coordinates in the basis $x^k(1+x)^{d-k}$ to a polynomial that is zero or
real-rooted with nonpositive zeros. For $d\ge2$ and some positive coordinate,
it is nonzero and lies between the Eulerian polynomial $A_d$ and the
derangement polynomial $d_d$ in the interlacing order
[@BrandenSolus2019, Cor. 3.7].
Here it is derived from the Brändén–Vecchi Chow-resolution theorem for the Pascal matrix,
whose resolving rows are exactly $x^k(1+x)^{d-k}$.

The derangement polynomials are defined by a recurrence. Their combinatorial meaning is
formalized: $d_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over the
derangements of $n$ letters, where $\operatorname{exc}$ counts excedances $i < \sigma(i)$.
The proof establishes the excedance recurrence by removing the letter $0$ from a derangement.
Moreover, $d_n$ is real-rooted for $n\ge2$.

## References

See [@BrandenSolus2019] and the
[symmetric-decomposition overview on symmetricfunctions.com](sf:symmetricIDecomposition).
<!-- /realrooted-catalog-content -->

Human statement:
sf:symmetricIDecomposition

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
