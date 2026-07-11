import RealRooted.SymmetricDecomposition

open Polynomial

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

/-- Challenge-facing name for the symmetric `I_d`-decomposition. -/
abbrev IDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  IsIdDecomposition d p a b

/-- Challenge-facing name for the Brändén--Solus Theorem 2.6 target. -/
def Theorem26Target : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IDecomposition d p a b →
    RealRooted.HasNonnegCoeffs a →
    RealRooted.HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    (RealRooted.Prec b a ↔ RealRooted.Prec a p) ∧
    (RealRooted.Prec a p ↔ RealRooted.Prec b p) ∧
    (RealRooted.Prec b p ↔ RealRooted.Prec (RealRooted.IdTransform d p) p) ∧
    (RealRooted.Prec (RealRooted.IdTransform d p) p ↔
      RealRooted.Prec (RealRooted.RdTransform d (RealRooted.fPolynomial d p))
        (RealRooted.fPolynomial d p))

/-- Branden--Solus symmetric-decomposition theorem, challenge-facing alias. -/
theorem theorem26 :
    Theorem26Target :=
  RealRooted.brandenSolusTheorem26

end BrandenSolus
end Challenges
end RealRooted
