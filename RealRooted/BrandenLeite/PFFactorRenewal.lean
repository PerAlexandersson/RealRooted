module

public import RealRooted.BrandenLeite.PFFactorNumerators
public import RealRooted.CombinatorialExamples.WeightedRenewal
import RealRooted.BrandenLeite.ZeroConstant
import RealRooted.MultiplierSequence.JensenHypergeometric

/-!
# PF-factor numerators and delayed renewal polynomials

This module proves the delayed-renewal specialization of the PF-factor
numerator theorem.  In each residue class modulo the delay, a renewal row is
the degree-padded reciprocal of a PF-factor numerator.  The identity gives
Pólya-frequency rows and consecutive interlacing within each residue class.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted
namespace BrandenLeite

private theorem mk_polynomial_coeff (p : ℝ[X]) :
    PowerSeries.mk p.coeff = (p : PowerSeries ℝ) := by
  ext n
  simp

private theorem positivePartSeries_mul_pow_X_mul_pow
    (R : ℝ[X]) {m r : ℕ} (hrm : r ≤ m) :
    positivePartSeries
        (fun k ↦ PowerSeries.coeff k
          (PowerSeries.mk (R ^ r).coeff *
            PowerSeries.mk (X * R ^ (m - r)).coeff)) =
      ((X * R ^ m : ℝ[X]) : PowerSeries ℝ) := by
  rw [positivePartSeries_eq_mk_of_zero]
  · rw [mk_coeff_eq, mk_polynomial_coeff, mk_polynomial_coeff,
      ← Polynomial.coe_mul]
    congr 1
    calc
      R ^ r * (X * R ^ (m - r)) = X * (R ^ r * R ^ (m - r)) := by ring
      _ = X * R ^ (r + (m - r)) := by rw [pow_add]
      _ = X * R ^ m := by rw [Nat.add_sub_of_le hrm]
  · rw [mk_polynomial_coeff, mk_polynomial_coeff]
    simp

/-- Coefficients of the PF-factor numerator used for a delayed renewal row.
The first factor is `R ^ r`, while the second is `X * R ^ (m - r)`. -/
theorem coeff_pfFactorNumerator_renewal (R : ℝ[X])
    {m r : ℕ} (hrm : r ≤ m) (q k : ℕ) :
    (pfFactorNumerator (R ^ r).coeff
        (X * R ^ (m - r)).coeff q).coeff k =
      if k ≤ q then (R ^ (r + m * k)).coeff (q - k) else 0 := by
  rw [coeff_pfFactorNumerator,
    positivePartSeries_mul_pow_X_mul_pow R hrm,
    mk_polynomial_coeff]
  have hseries :
      ((R ^ r : ℝ[X]) : PowerSeries ℝ) *
          (((X * R ^ m : ℝ[X]) : PowerSeries ℝ) ^ k) =
        ((X ^ k * R ^ (r + m * k) : ℝ[X]) : PowerSeries ℝ) := by
    rw [← Polynomial.coe_pow, ← Polynomial.coe_mul]
    congr 1
    rw [mul_pow]
    simp only [pow_mul, pow_add]
    ring
  rw [hseries, Polynomial.coeff_coe, Polynomial.coeff_X_pow_mul']

/-- With positive constant coefficient, the PF-factor numerator for the
renewal row at quotient `q` has degree exactly `q`. -/
theorem natDegree_pfFactorNumerator_renewal
    {R : ℝ[X]} (hR0 : 0 < R.coeff 0)
    {m r : ℕ} (hrm : r ≤ m) (q : ℕ) :
    (pfFactorNumerator (R ^ r).coeff
      (X * R ^ (m - r)).coeff q).natDegree = q := by
  apply le_antisymm (natDegree_pfFactorNumerator_le _ _ q)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_pfFactorNumerator_renewal R hrm q q,
    ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero,
    eval_pow, ← coeff_zero_eq_eval_zero]
  exact (pow_pos hR0 (r + m * q)).ne'

/-- The leading coefficient of the PF-factor numerator is the expected
positive power of the constant coefficient of the renewal driver. -/
theorem leadingCoeff_pfFactorNumerator_renewal
    {R : ℝ[X]} (hR0 : 0 < R.coeff 0)
    {m r : ℕ} (hrm : r ≤ m) (q : ℕ) :
    (pfFactorNumerator (R ^ r).coeff
      (X * R ^ (m - r)).coeff q).leadingCoeff =
        (R.coeff 0) ^ (r + m * q) := by
  rw [leadingCoeff, natDegree_pfFactorNumerator_renewal hR0 hrm q,
    coeff_pfFactorNumerator_renewal R hrm q q,
    ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero,
    eval_pow, ← coeff_zero_eq_eval_zero]

/-- The row at index `m * q + r` of the delayed renewal family is the
degree-`q` reciprocal of its PF-factor numerator, for `r < m`. -/
theorem renewalPolynomial_eq_reciprocalShift_pfFactorNumerator
    (R : ℝ[X]) {m r : ℕ} (hrm : r < m) (q : ℕ) :
    renewalPolynomial R m (m * q + r) =
      reciprocalShift q
        (pfFactorNumerator (R ^ r).coeff
          (X * R ^ (m - r)).coeff q) := by
  ext j
  rw [coeff_renewalPolynomial R m (m * q + r) j (by lia),
    coeff_reciprocalShift]
  by_cases hj : j ≤ q
  · rw [Polynomial.revAt_le hj,
      coeff_pfFactorNumerator_renewal R hrm.le]
    simp only [Nat.sub_le, ↓reduceIte]
    congr 1
    · rw [Nat.add_comm (m * q) r,
        Nat.add_sub_assoc (Nat.mul_le_mul_left m hj),
        ← Nat.mul_sub_left_distrib]
    · lia
  · have hqj : q < j := Nat.lt_of_not_ge hj
    rw [Polynomial.revAt_eq_self_of_lt hqj,
      coeff_pfFactorNumerator_renewal R hrm.le,
      ite_eq_right (by lia)]
    have hsub : m * q + r - m * j = 0 := by
      apply Nat.sub_eq_zero_of_le
      exact (calc
          m * q + r < m * q + m := Nat.add_lt_add_left hrm _
          _ ≤ m * j := by
            rw [← Nat.mul_succ]
            exact Nat.mul_le_mul_left m (Nat.succ_le_iff.mpr hqj)).le
    rw [hsub, pow_zero, coeff_one]
    simp [show j ≠ 0 by lia]

end BrandenLeite

/-- The constant coefficient of a delayed renewal row is the corresponding
power of the constant coefficient of its driver. -/
theorem coeff_zero_renewalPolynomial (R : ℝ[X])
    {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (renewalPolynomial R m n).coeff 0 = (R.coeff 0) ^ n := by
  rw [coeff_renewalPolynomial R m n 0 hm]
  simp only [Nat.mul_zero, Nat.sub_zero]
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]

/-- A delayed renewal row is nonzero when its driver has positive constant
coefficient. -/
theorem renewalPolynomial_ne_zero_of_coeff_zero_pos
    {R : ℝ[X]} {m : ℕ} (hm : m ≠ 0) (hR0 : 0 < R.coeff 0) (n : ℕ) :
    renewalPolynomial R m n ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
  rw [coeff_zero_renewalPolynomial R hm n] at hcoeff
  simp only [coeff_zero] at hcoeff
  exact (pow_pos hR0 n).ne' hcoeff

/-- Zero-aware interlacing is preserved by reciprocal shifts at consecutive
degree bounds for PF polynomials. -/
theorem interl_reciprocalShift_succ
    {n : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpd : p.natDegree ≤ n) (hqd : q.natDegree ≤ n + 1)
    (hpq : Interl p q) :
    Interl (reciprocalShift n p) (reciprocalShift (n + 1) q) := by
  by_cases hp0 : p = 0
  · rw [hp0]
    exact interl_zero_left _
  by_cases hq0 : q = 0
  · rw [hq0]
    exact interl_zero_right _
  exact (strictInterl_reciprocalShift_succ hp hq hpd hqd
    (hpq.toStrictInterl_of_ne hp0 hq0)).toInterl

/-- If the delayed-renewal driver is PF, every row in every residue class is
a PF polynomial. -/
theorem renewalPolynomial_isPF_of_isPFPolynomial
    {R : ℝ[X]} (hR : IsPFPolynomial R)
    {m r : ℕ} (hrm : r < m) (q : ℕ) :
    IsPFPolynomial (renewalPolynomial R m (m * q + r)) := by
  rw [BrandenLeite.renewalPolynomial_eq_reciprocalShift_pfFactorNumerator
    R hrm q]
  apply reciprocalShift_preserves_pf
  · exact BrandenLeite.pfFactorNumerator_isPFPolynomial
      (hR.pow r).to_sequence ((hR.pow (m - r)).X_mul).to_sequence q
  · exact BrandenLeite.natDegree_pfFactorNumerator_le _ _ q

/-- Consecutive delayed-renewal rows within one residue class interlace in
the zero-aware relation.  This does not compare different residue classes. -/
theorem interl_renewalPolynomial_residue_succ
    {R : ℝ[X]} (hR : IsPFPolynomial R)
    {m r : ℕ} (hrm : r < m) (q : ℕ) :
    Interl (renewalPolynomial R m (m * q + r))
      (renewalPolynomial R m (m * (q + 1) + r)) := by
  rw [BrandenLeite.renewalPolynomial_eq_reciprocalShift_pfFactorNumerator
      R hrm q,
    BrandenLeite.renewalPolynomial_eq_reciprocalShift_pfFactorNumerator
      R hrm (q + 1)]
  apply interl_reciprocalShift_succ
  · exact BrandenLeite.pfFactorNumerator_isPFPolynomial
      (hR.pow r).to_sequence ((hR.pow (m - r)).X_mul).to_sequence q
  · exact BrandenLeite.pfFactorNumerator_isPFPolynomial
      (hR.pow r).to_sequence ((hR.pow (m - r)).X_mul).to_sequence (q + 1)
  · exact BrandenLeite.natDegree_pfFactorNumerator_le _ _ q
  · exact BrandenLeite.natDegree_pfFactorNumerator_le _ _ (q + 1)
  · exact BrandenLeite.interl_pfFactorNumerator_succ
      (hR.pow r).to_sequence ((hR.pow (m - r)).X_mul).to_sequence q

/-- With positive constant coefficient, consecutive delayed-renewal rows
within a residue class strictly interlace. -/
theorem strictInterl_renewalPolynomial_residue_succ
    {R : ℝ[X]} (hR : IsPFPolynomial R) (hR0 : 0 < R.coeff 0)
    {m r : ℕ} (hrm : r < m) (q : ℕ) :
    StrictInterl (renewalPolynomial R m (m * q + r))
      (renewalPolynomial R m (m * (q + 1) + r)) := by
  apply (interl_renewalPolynomial_residue_succ hR hrm q).toStrictInterl_of_ne
  · exact renewalPolynomial_ne_zero_of_coeff_zero_pos (by lia) hR0 _
  · exact renewalPolynomial_ne_zero_of_coeff_zero_pos (by lia) hR0 _

end RealRooted
