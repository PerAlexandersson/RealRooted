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

namespace RealRooted
namespace Challenges
namespace BrandenSolus

/-- Challenge-facing name for the symmetric `I_d`-decomposition. -/
abbrev IDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  IsIdDecomposition d p a b

/-- Challenge-facing name for the Brändén--Solus Theorem 2.6 target. -/
abbrev Theorem26Target : Prop :=
  RealRooted.brandenSolusTheorem26Statement

/-- Branden--Solus symmetric-decomposition theorem, challenge-facing alias. -/
theorem theorem26 :
    Theorem26Target :=
  RealRooted.brandenSolusTheorem26

end BrandenSolus
end Challenges
end RealRooted
