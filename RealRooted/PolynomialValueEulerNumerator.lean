import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Mathlib.RingTheory.PowerSeries.CausalFwdDiff
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Euler numerators of polynomial-value sequences

This file defines the canonical finite Euler numerator obtained from the
Gregory--Newton coefficients of a polynomial-value sequence. The ambient
degree is always the polynomial's actual `natDegree`; using a larger degree
would introduce artificial factors of `1 - X`.
-/

open Polynomial

namespace RealRooted

private theorem coeff_X_pow_mul_invOneSubPow (k n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.X ^ k * (PowerSeries.invOneSubPow ℝ (k + 1)).val) =
      (n.choose k : ℝ) := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hkn
  · rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.coeff_mk, Nat.add_sub_of_le hkn]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn)]

private theorem eulerBasis_mul_invOneSubPow (d k : ℕ) (hk : k ≤ d) :
    PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (d - k) *
        (PowerSeries.invOneSubPow ℝ (d + 1)).val =
      PowerSeries.X ^ k * (PowerSeries.invOneSubPow ℝ (k + 1)).val := by
  rw [mul_assoc]
  have hadd : k + 1 + (d - k) = d + 1 := by lia
  rw [← hadd,
    PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]

/-- The degree-`d` Euler numerator with Newton coefficients `a`. -/
noncomputable def finiteEulerNumerator (d : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (a k) * X ^ k * (1 - X) ^ (d - k)

/-- The degree-`d` Euler numerator has degree at most `d`, including when top
Newton coefficients cancel. -/
theorem natDegree_finiteEulerNumerator_le (d : ℕ) (a : ℕ → ℝ) :
    (finiteEulerNumerator d a).natDegree ≤ d := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    (C (a k) * X ^ k * (1 - X) ^ (d - k)).natDegree ≤
        (C (a k) * X ^ k).natDegree +
          ((1 - X : ℝ[X]) ^ (d - k)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ k + (d - k) := by
      apply Nat.add_le_add
      · exact (Polynomial.natDegree_C_mul_le (a k) (X ^ k)).trans_eq
          (Polynomial.natDegree_X_pow k)
      · calc
          ((1 - X) ^ (d - k) : ℝ[X]).natDegree ≤
              (d - k) * (1 - X : ℝ[X]).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ (d - k) * 1 := Nat.mul_le_mul_left _ (by
            simpa using Polynomial.natDegree_sub_le (1 : ℝ[X]) X)
          _ = d - k := by simp
    _ = d := Nat.add_sub_of_le hkd

private theorem finiteEulerNumerator_mul_invOneSubPow (d : ℕ) (a : ℕ → ℝ) :
    (finiteEulerNumerator d a : PowerSeries ℝ) *
        (PowerSeries.invOneSubPow ℝ (d + 1)).val =
      ∑ k ∈ Finset.range (d + 1),
        PowerSeries.C (a k) *
          (PowerSeries.X ^ k * (PowerSeries.invOneSubPow ℝ (k + 1)).val) := by
  classical
  rw [finiteEulerNumerator]
  change Polynomial.coeToPowerSeries.ringHom
      (∑ k ∈ Finset.range (d + 1),
        C (a k) * X ^ k * (1 - X) ^ (d - k)) * _ = _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X, map_sub, map_one]
  rw [mul_assoc (PowerSeries.C (a k)), mul_assoc (PowerSeries.C (a k))]
  congr 1
  exact eulerBasis_mul_invOneSubPow d k hkd

/-- The canonical Euler numerator of a polynomial-value sequence. -/
noncomputable def polynomialValueEulerNumerator (p : ℝ[X]) : ℝ[X] :=
  finiteEulerNumerator p.natDegree fun k =>
    ((fwdDiff (1 : ℕ))^[k] (polynomialValueSeq p)) 0

/-- The canonical numerator uses the source polynomial's actual degree as its
degree cap. -/
theorem natDegree_polynomialValueEulerNumerator_le (p : ℝ[X]) :
    (polynomialValueEulerNumerator p).natDegree ≤ p.natDegree := by
  exact natDegree_finiteEulerNumerator_le p.natDegree _

/-- The generating series of a polynomial-value sequence is its canonical
Euler numerator divided by `(1 - X)^(natDegree + 1)`. -/
theorem polynomialValueSeries_eq_eulerNumerator_mul_invOneSubPow (p : ℝ[X]) :
    PowerSeries.mk (polynomialValueSeq p) =
      (polynomialValueEulerNumerator p : PowerSeries ℝ) *
        (PowerSeries.invOneSubPow ℝ (p.natDegree + 1)).val := by
  ext n
  rw [PowerSeries.coeff_mk,
    polynomialValueSeq_eq_sum_choose_fwdDiff_upto_natDegree]
  rw [polynomialValueEulerNumerator,
    finiteEulerNumerator_mul_invOneSubPow]
  simp only [map_sum, PowerSeries.coeff_C_mul,
    coeff_X_pow_mul_invOneSubPow, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Iterating causal forward differences through the actual degree of a
polynomial-value sequence gives the coefficients of its canonical Euler
numerator. -/
theorem causalFwdDiff_iter_polynomialValueSeq_eq_eulerNumerator_coeff (p : ℝ[X]) :
    (Function.causalFwdDiff^[p.natDegree + 1]) (polynomialValueSeq p) =
      fun n => (polynomialValueEulerNumerator p).coeff n := by
  have hseries :
      PowerSeries.mk ((Function.causalFwdDiff^[p.natDegree + 1])
        (polynomialValueSeq p)) = (polynomialValueEulerNumerator p : PowerSeries ℝ) := by
    rw [PowerSeries.mk_causalFwdDiff_iter,
      polynomialValueSeries_eq_eulerNumerator_mul_invOneSubPow,
      ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    calc
      (PowerSeries.invOneSubPow ℝ (p.natDegree + 1)).inv *
          ((polynomialValueEulerNumerator p : PowerSeries ℝ) *
            (PowerSeries.invOneSubPow ℝ (p.natDegree + 1)).val) =
          (polynomialValueEulerNumerator p : PowerSeries ℝ) *
            ((PowerSeries.invOneSubPow ℝ (p.natDegree + 1)).inv *
              (PowerSeries.invOneSubPow ℝ (p.natDegree + 1)).val) := by
        ring
      _ = (polynomialValueEulerNumerator p : PowerSeries ℝ) := by
        rw [Units.inv_val, mul_one]
  funext n
  simpa using congrArg (PowerSeries.coeff n) hseries

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

@[simp]
theorem polynomialValueEulerNumerator_zero :
    polynomialValueEulerNumerator (0 : ℝ[X]) = 0 := by
  simp [polynomialValueEulerNumerator, finiteEulerNumerator, polynomialValueSeq]

@[simp]
theorem polynomialValueEulerNumerator_one :
    polynomialValueEulerNumerator (1 : ℝ[X]) = 1 := by
  simp [polynomialValueEulerNumerator, finiteEulerNumerator, polynomialValueSeq]

@[simp]
theorem polynomialValueEulerNumerator_X :
    polynomialValueEulerNumerator (X : ℝ[X]) = X := by
  rw [polynomialValueEulerNumerator, natDegree_X]
  norm_num [finiteEulerNumerator, Finset.sum_range_succ,
    polynomialValueSeq, fwdDiff, Function.iterate_succ_apply']

@[simp]
theorem polynomialValueEulerNumerator_X_add_one :
    polynomialValueEulerNumerator (X + 1 : ℝ[X]) = 1 := by
  rw [polynomialValueEulerNumerator,
    show (X + 1 : ℝ[X]).natDegree = 1 by
      simp [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp]]
  norm_num [finiteEulerNumerator, Finset.sum_range_succ,
    polynomialValueSeq, fwdDiff, Function.iterate_succ_apply']

end RealRooted
