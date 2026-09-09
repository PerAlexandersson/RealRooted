import RealRooted.AissenSchoenbergWhitneyBase

/-!
# Euler numerators of polynomial-value sequences

This file defines the canonical finite Euler numerator obtained from the
Gregory--Newton coefficients of a polynomial-value sequence. The ambient
degree is always the polynomial's actual `natDegree`; using a larger degree
would introduce artificial factors of `1 - X`.
-/

open Polynomial

namespace RealRooted

/-- The degree-`d` Euler numerator with Newton coefficients `a`. -/
noncomputable def finiteEulerNumerator (d : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (a k) * X ^ k * (1 - X) ^ (d - k)

/-- The canonical Euler numerator of a polynomial-value sequence. -/
noncomputable def polynomialValueEulerNumerator (p : ℝ[X]) : ℝ[X] :=
  finiteEulerNumerator p.natDegree fun k =>
    ((fwdDiff (1 : ℕ))^[k] (polynomialValueSeq p)) 0

/-- Evaluation at `1` selects the top Newton coefficient. -/
theorem finiteEulerNumerator_eval_one (d : ℕ) (a : ℕ → ℝ) :
    (finiteEulerNumerator d a).eval 1 = a d := by
  classical
  simp only [finiteEulerNumerator, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, eval_sub, eval_one, one_pow, sub_self]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    have hkd' : k < d := by
      have hkle : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact lt_of_le_of_ne hkle hkd
    have hsub : d - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hkd')
    simp [hsub]
  · simp

/-- The canonical Euler numerator evaluates at `1` to the leading coefficient
times the degree factorial. -/
theorem polynomialValueEulerNumerator_eval_one (p : ℝ[X]) :
    (polynomialValueEulerNumerator p).eval 1 =
      p.leadingCoeff * p.natDegree.factorial := by
  rw [polynomialValueEulerNumerator, finiteEulerNumerator_eval_one]
  exact congr_fun (fwdDiff_iter_polynomialValueSeq_natDegree_eq_factorial p) 0

/-- A nonzero polynomial has a nonzero canonical Euler numerator. -/
theorem polynomialValueEulerNumerator_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    polynomialValueEulerNumerator p ≠ 0 := by
  intro hzero
  have hprod : p.leadingCoeff * (p.natDegree.factorial : ℝ) ≠ 0 := by
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (by positivity)
  apply hprod
  simpa [hzero] using (polynomialValueEulerNumerator_eval_one p).symm

end RealRooted
