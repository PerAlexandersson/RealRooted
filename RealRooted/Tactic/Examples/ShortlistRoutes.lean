import RealRooted.Applications.OEIS.A151775
import RealRooted.Applications.OEIS.A330798
import RealRooted.Applications.OEIS.ReflectedEulerRows
import RealRooted.Interlacing.ReversalCommonFactor
import RealRooted.Tactic.RowInterlacing

/-!
# Shortlist row-model routes

Regression examples for the A151775 transfer, the reflected Euler-bidiagonal families, and
the normalized A330798 sequence identification.
-/

open Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.Examples.ShortlistRoutes

private def row151775 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (4 * X + 4 * X ^ 3 + 8 * X ^ 2) * (row151775 n).derivative.derivative +
        (2 + 10 * X ^ 2 + 12 * X) * (row151775 n).derivative +
          (1 + 2 * X) * row151775 n

example (n : ℕ) : Interlaces (row151775 n) (row151775 (n + 1)) := by
  rr_row_interlaces

private def row008957 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 1 * X ^ 3 * (row008957 n).derivative.derivative +
        C (-1 + -2 * (n : ℝ)) * X ^ 2 * (row008957 n).derivative +
          (C 1 + C (-3 + (2 + (n : ℝ)) ^ 2 + -2 * (n : ℝ)) * X) * row008957 n

example (n : ℕ) : Interlaces (row008957 n) (row008957 (n + 1)) := by
  rr_row_interlaces

private def row191935 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 1 * X ^ 3 * (row191935 n).derivative.derivative +
        C (-2 + -2 * (n : ℝ)) * X ^ 2 * (row191935 n).derivative +
          (C 1 + C (-2 + (2 + (n : ℝ)) ^ 2 + -(n : ℝ)) * X) * row191935 n

example (n : ℕ) : Interlaces (row191935 n) (row191935 (n + 1)) := by
  rr_row_interlaces

private def row330798 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | n + 2 => RowParityDegree.A330798Next n (row330798 (n + 1)) (row330798 n)

example (n : ℕ) : row330798 n = RowParityDegree.A330798 n := by
  apply RowParityDegree.sequence_eq_A330798_of_recurrence
  · rfl
  · rfl
  · intro m
    rw [row330798]

example (n : ℕ) : (row330798 n).natDegree = n := by
  rw [RowParityDegree.sequence_eq_A330798_of_recurrence
    (P := row330798) (by rfl) (by rfl) (fun m => by rw [row330798])]
  exact RowParityDegree.A330798_natDegree n

example {g f : ℝ[X]} (h : Interlaces g f)
    (hf : ∀ t ∈ f.roots, t < 0) (hg : ∀ t ∈ g.roots, t < 0) :
    Interlaces (X ^ 2 * g.reverse) (X ^ 2 * f.reverse) := by
  exact interlaces_X_pow_mul_reverse_of_roots_neg h hf hg 2

end RealRooted.Tactic.Examples.ShortlistRoutes
