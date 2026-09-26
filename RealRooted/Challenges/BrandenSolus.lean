import RealRooted.SymmetricDecomposition

open Polynomial

/-!
# Branden--Solus challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-solus"

[[definitions]]
name = "RealRooted.Challenges.BrandenSolus.IDecomposition"

[[theorems]]
name = "RealRooted.Challenges.BrandenSolus.theorem26"
-->

<!-- realrooted-catalog-content -->
# Brändén–Solus symmetric decomposition

The `I_d`-decomposition writes a polynomial as `a + X b` with the prescribed
reciprocal symmetries in ambient degree `d`.  The selected theorem is the
checked form of Brändén–Solus Theorem 2.6: under its nondegeneracy,
coefficient, degree, and reciprocal-root hypotheses, the two symmetric pieces
are in proper position.  The boundary cases are included in the underlying
proof rather than assumed as an external input.

## References

P. Brändén and L. Solus, “Symmetric decompositions and real-rootedness,”
*International Mathematics Research Notices* 2021 (2019), 7764–7798.  See the
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
