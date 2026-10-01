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
name = "RealRooted.Challenges.BrandenSolus.theorem26"
label = "Brändén–Solus, Theorem 2.6"
-->

<!-- realrooted-catalog-content -->
# Brändén–Solus symmetric decomposition

The $I_d$-decomposition writes a polynomial as $a + Xb$ with reciprocal
symmetry conditions on $a$ and $b$. Under the hypotheses of Brändén–Solus
Theorem 2.6, these two pieces interlace.

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

/-- Branden--Solus symmetric-decomposition theorem. -/
theorem theorem26 :
    ∀ {d : ℕ} {p a b : ℝ[X]},
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (StrictInterl b a ↔ StrictInterl a p) ∧
      (StrictInterl a p ↔ StrictInterl b p) ∧
      (StrictInterl b p ↔ StrictInterl (IdTransform d p) p) ∧
      (StrictInterl (IdTransform d p) p ↔
        StrictInterl (RdTransform d (fPolynomial d p)) (fPolynomial d p)) :=
  RealRooted.brandenSolusTheorem26

end BrandenSolus
end Challenges
end RealRooted
