module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Expanded formal symbols and derivative strides
-/

public section

open Polynomial Finset

namespace RealRooted.HermitePoulain

/-- Expanding a formal symbol by `X^p` restricts its polynomial action to
derivatives of orders divisible by the positive stride. -/
theorem formalDifferentialOperator_expand_eq_sum
    (φ : PowerSeries ℝ) {p : ℕ} (hp : 0 < p) (P : ℝ[X]) :
    formalDifferentialOperator (PowerSeries.expand p hp.ne' φ) P =
      ∑ k ∈ range (P.natDegree / p + 1),
        C (PowerSeries.coeff k φ) * (derivative^[p * k]) P := by
  rw [formalDifferentialOperator_eq_sum]
  simp_rw [PowerSeries.coeff_expand, apply_ite, map_zero, ite_mul, zero_mul]
  rw [← sum_filter]
  symm
  apply sum_bij (fun k _ ↦ p * k)
  · intro k hk
    simp only [mem_filter, mem_range]
    refine ⟨?_, dvd_mul_right p k⟩
    have hk' : k ≤ P.natDegree / p := Nat.le_of_lt_succ (mem_range.mp hk)
    exact Nat.lt_succ_of_le ((Nat.mul_le_mul_left p hk').trans
      (Nat.mul_div_le P.natDegree p))
  · intro k hk j hj hkj
    exact Nat.eq_of_mul_eq_mul_left hp hkj
  · intro j hj
    obtain ⟨hjr, hjd⟩ := mem_filter.mp hj
    refine ⟨j / p, mem_range.mpr ?_, Nat.mul_div_cancel' hjd⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ (mem_range.mp hjr)))
  · intro k _
    rw [Nat.mul_div_cancel_left k hp]

end RealRooted.HermitePoulain
