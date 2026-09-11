import RealRooted.TotallyNonnegInterlacing

/-!
# Totally nonnegative principal interlacing challenge entry point

Human statement: the characteristic polynomial of either the leading or the
trailing codimension-one principal section of a finite totally nonnegative
matrix weakly interlaces the characteristic polynomial of the full matrix.
The checked theorem includes singular and reducible matrices (issue #552).

The reusable endpoints are
`Matrix.IsTotallyNonneg.leading_charpoly_interlaces` and
`Matrix.IsTotallyNonneg.trailing_charpoly_interlaces` in
`RealRooted.TotallyNonnegInterlacing`.  This file only gives compact
challenge-facing names; it is not independent comparator coverage.
-/

namespace RealRooted
namespace Challenges
namespace TotallyNonnegative

/-- Weak trailing-principal characteristic-polynomial interlacing for every
finite totally nonnegative real matrix, including singular matrices. -/
theorem trailingPrincipal_charpoly_interlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) :
    RealRooted.Interlaces
      (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly := by
  exact hA.trailing_charpoly_interlaces

/-- Weak leading-principal characteristic-polynomial interlacing for every
finite totally nonnegative real matrix, including singular matrices. -/
theorem leadingPrincipal_charpoly_interlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) :
    RealRooted.Interlaces
      (A.submatrix Fin.castSucc Fin.castSucc).charpoly A.charpoly := by
  exact hA.leading_charpoly_interlaces

end TotallyNonnegative
end Challenges
end RealRooted
