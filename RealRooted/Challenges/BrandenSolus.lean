import RealRooted.SymmetricDecomposition

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
-->

<!-- realrooted-catalog-content -->
# Brändén–Solus symmetric decomposition

The $I_d$-decomposition writes a polynomial $p$ of degree at most $d$ as
$p = a + Xb$ with reciprocal symmetry conditions on $a$ and $b$. If $a$ and $b$
are nonzero with nonnegative coefficients, then $b \ll a$, $a \ll p$ and
$b \ll p$ are equivalent. They are also equivalent to $I_d(p) \ll p$, and to
$R_d(f) \ll f$ for the associated polynomial $f$ (`fPolynomial d p`).

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
