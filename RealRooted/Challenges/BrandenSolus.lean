import RealRooted.SymmetricDecomposition

/-!
# Branden--Solus challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#symmetricIDecomposition

Original publication: P. Branden and L. Solus, "Symmetric decompositions and
real-rootedness", International Mathematics Research Notices 2021 (2019),
7764--7798.

This module exposes the completed nondegenerate `Prec` form of the
Branden--Solus symmetric-decomposition theorem.  The decomposition API and
boundary-case proof remain in `RealRooted.SymmetricDecomposition`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace BrandenSolus

/-- Branden--Solus symmetric-decomposition theorem, challenge-facing alias. -/
theorem theorem26
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : RealRooted.IsIdDecomposition d p a b)
    (ha_nonneg : RealRooted.HasNonnegCoeffs a)
    (hb_nonneg : RealRooted.HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (RealRooted.Prec b a ↔ RealRooted.Prec a p) ∧
    (RealRooted.Prec a p ↔ RealRooted.Prec b p) ∧
    (RealRooted.Prec b p ↔ RealRooted.Prec (RealRooted.IdTransform d p) p) ∧
    (RealRooted.Prec (RealRooted.IdTransform d p) p ↔
      RealRooted.Prec (RealRooted.RdTransform d (RealRooted.fPolynomial d p))
        (RealRooted.fPolynomial d p)) :=
  RealRooted.brandenSolusTheorem26 hd hid ha_nonneg hb_nonneg ha0 hb0

end BrandenSolus
end Challenges
end RealRooted
