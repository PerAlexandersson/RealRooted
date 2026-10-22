import RealRooted.FerrersTiling.TwoColumn
import RealRooted.DegreeDropReversal

/-!
# Fault-line polynomials for two-column Ferrers tiles

This file formalizes the algebraic statement in Ahlberg--Alexandersson,
*Polynomials from tilings of rectangles*, Section 6: the fault-line family is
the coefficient reversal of the two-column family.
-/

open Polynomial

namespace RealRooted
namespace FerrersTiling

noncomputable section

/-- The two-column polynomial has degree at most its board-width index. -/
theorem twoColumnPolynomial_natDegree_le (d n : ℕ) :
    (twoColumnPolynomial d n).natDegree ≤ n := by
  have hbase := pathPowerCliquePolynomial_subsequence_natDegree_le
    2 1 0 n (by norm_num) (by norm_num) (by norm_num)
  have hbase' : (pathPowerCliquePolynomial 2 n).natDegree ≤ n := by
    simpa [pathPowerCliquePolynomial] using hbase
  refine Polynomial.natDegree_comp_le.trans ?_
  have hinner : (C (d : ℝ) * X).natDegree ≤ 1 := by compute_degree
  nlinarith [Nat.mul_le_mul hbase' hinner]

/-- The fault-line polynomial `R_n = X^n P_n(X⁻¹)`. -/
def faultLinePolynomial (d n : ℕ) : ℝ[X] :=
  (twoColumnPolynomial d n).reflect n

@[simp]
theorem faultLinePolynomial_zero (d : ℕ) : faultLinePolynomial d 0 = 1 := by
  simp [faultLinePolynomial, twoColumnPolynomial_zero]

@[simp]
theorem faultLinePolynomial_one (d : ℕ) : faultLinePolynomial d 1 = X := by
  simp [faultLinePolynomial, twoColumnPolynomial_one]

private theorem reflect_succ_of_natDegree_le {p : ℝ[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) :
    p.reflect (n + 1) = X * p.reflect n := by
  have h := reflect_mul (1 : ℝ[X]) p (F := 1) (G := n) (by simp) hp
  rw [one_mul, reflect_one, pow_one, add_comm] at h
  exact h

/-- The recurrence `R_(n+2) = X R_(n+1) + d X R_n`. -/
theorem faultLinePolynomial_add_two (d n : ℕ) :
    faultLinePolynomial d (n + 2) =
      X * faultLinePolynomial d (n + 1) +
        C (d : ℝ) * X * faultLinePolynomial d n := by
  rw [faultLinePolynomial, twoColumnPolynomial_add_two]
  rw [Polynomial.reflect_add]
  rw [reflect_succ_of_natDegree_le (twoColumnPolynomial_natDegree_le d (n + 1))]
  have hprod :
      (C (d : ℝ) * X * twoColumnPolynomial d n).natDegree ≤ n + 1 := by
    refine natDegree_mul_le.trans ?_
    have hleft : (C (d : ℝ) * X).natDegree ≤ 1 := by compute_degree
    exact (add_le_add hleft (twoColumnPolynomial_natDegree_le d n)).trans_eq (by lia)
  have hreflect :
      (C (d : ℝ) * X * twoColumnPolynomial d n).reflect (n + 2) =
        X * (C (d : ℝ) * X * twoColumnPolynomial d n).reflect (n + 1) := by
    simpa only [show n + 2 = n + 1 + 1 by lia] using
      reflect_succ_of_natDegree_le hprod
  rw [hreflect]
  have hmul := reflect_mul (C (d : ℝ) * X) (twoColumnPolynomial d n)
    (F := 1) (G := n) (by compute_degree) (twoColumnPolynomial_natDegree_le d n)
  have hmul' :
      (C (d : ℝ) * X * twoColumnPolynomial d n).reflect (n + 1) =
        (C (d : ℝ) * X).reflect 1 * (twoColumnPolynomial d n).reflect n := by
    simpa only [Nat.add_comm] using hmul
  rw [hmul']
  rw [show (C (d : ℝ) * X : ℝ[X]) = C (d : ℝ) * X ^ 1 by simp,
    Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le (by lia)]
  simp only [Nat.sub_self, pow_zero, mul_one, faultLinePolynomial]
  ring

/-- Every fault-line polynomial is real-rooted. -/
theorem faultLinePolynomial_splits (d n : ℕ) :
    (faultLinePolynomial d n).Splits :=
  Polynomial.Splits.reflect (twoColumnPolynomial_splits d n)
    (twoColumnPolynomial_natDegree_le d n)

end

end FerrersTiling
end RealRooted
