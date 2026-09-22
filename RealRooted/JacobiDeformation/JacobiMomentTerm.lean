import RealRooted.JacobiDeformation.WeightNormalization

/-!
# Scalar cancellation in normalized Jacobi moments
-/

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The scalar cancellation which converts a mixed normalized beta moment to
the finite Chu--Vandermonde summand. -/
theorem risingFactorial_mixed_moment_cancel
    {c d a : ℝ} (hc : 0 < c) (hd : 0 < d) (i k : ℕ) :
    (risingFactorial a i / risingFactorial c i) *
        (risingFactorial c i * risingFactorial d k /
          risingFactorial (c + d) (i + k)) =
      (risingFactorial d k / risingFactorial (c + d) k) *
        (risingFactorial a i / risingFactorial (c + d + k) i) := by
  have hs : 0 < c + d := by linarith
  have hci : 0 < risingFactorial c i := risingFactorial_pos i hc
  have hsk : 0 < risingFactorial (c + d) k := risingFactorial_pos k hs
  have hski : 0 < risingFactorial (c + d + k) i := by
    apply risingFactorial_pos
    positivity
  have hsplit := risingFactorial_mul_shift (c + d) k i
  rw [show (c + d : ℝ) + k = c + d + k by ring,
    Nat.add_comm] at hsplit
  field_simp [hci.ne', hsk.ne', hski.ne']
  rw [← hsplit]
  ring

end RealRooted.JacobiDeformation
