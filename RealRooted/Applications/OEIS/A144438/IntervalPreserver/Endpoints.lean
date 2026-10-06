import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Basic
import RealRooted.BasisTransform

/-!
# Endpoint estimates for the A144438 diagonal family

This file proves the coefficient positivity, endpoint recurrences, and scalar
ratio bounds used by the residue-energy induction.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The A144438 basis transform preserves coefficientwise nonnegativity. -/
theorem HasNonnegCoeffs.a144438Transform {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) : HasNonnegCoeffs (a144438Transform p) :=
  hp.basisTransform decoEulerian_hasNonnegCoeffs

/-- The A144438 lag transform preserves coefficientwise nonnegativity. -/
theorem HasNonnegCoeffs.a144438LagTransform {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) : HasNonnegCoeffs (a144438LagTransform p) := by
  apply hp.basisTransform
  intro n
  cases n with
  | zero => simpa [a144438LagBasis] using hasNonnegCoeffs_zero
  | succ n => exact decoEulerian_hasNonnegCoeffs n

/-- Evaluation at zero after the A144438 transform is input evaluation at
one. -/
theorem a144438Transform_eval_zero (p : ℝ[X]) :
    (a144438Transform p).eval 0 = p.eval 1 := by
  rw [← coeff_zero_eq_eval_zero, a144438Transform,
    Polynomial.coeff_basisTransform, Polynomial.eval_eq_sum]
  simp

/-- The diagonal family has nonnegative coefficients for nonnegative
parameters. -/
theorem a144438Diagonal_hasNonnegCoeffs {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (a144438Diagonal n a) := by
  apply HasNonnegCoeffs.a144438Transform
  exact (hasNonnegCoeffs_X.add (hasNonnegCoeffs_C ha)).pow n

/-- The diagonal lag family has nonnegative coefficients for nonnegative
parameters. -/
theorem a144438DiagonalLag_hasNonnegCoeffs {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (a144438DiagonalLag n a) := by
  apply HasNonnegCoeffs.a144438LagTransform
  exact (hasNonnegCoeffs_X.add (hasNonnegCoeffs_C ha)).pow n

/-- The value at zero of the diagonal polynomial. -/
@[simp]
theorem a144438Diagonal_eval_zero (n : ℕ) (a : ℝ) :
    (a144438Diagonal n a).eval 0 = (1 + a) ^ n := by
  rw [a144438Diagonal, a144438Transform_eval_zero]
  simp

/-- Every diagonal polynomial is nonzero when `a > -1`. -/
theorem a144438Diagonal_ne_zero {n : ℕ} {a : ℝ} (ha : -1 < a) :
    a144438Diagonal n a ≠ 0 := by
  intro hzero
  have := congrArg (fun p : ℝ[X] => p.eval 0) hzero
  simp only [a144438Diagonal_eval_zero, eval_zero] at this
  have hbase : 0 < 1 + a := by linarith
  have : 0 < (1 + a) ^ n := pow_pos hbase n
  linarith

/-- The diagonal value at one is positive for nonnegative parameters. -/
theorem a144438Diagonal_eval_one_pos {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    0 < (a144438Diagonal n a).eval 1 :=
  eval_pos_of_hasNonnegCoeffs (a144438Diagonal_hasNonnegCoeffs ha)
    (a144438Diagonal_ne_zero (by linarith)) (by norm_num)

/-- The diagonal lag value at one is nonnegative for nonnegative parameters.
-/
theorem a144438DiagonalLag_eval_one_nonneg {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (a144438DiagonalLag n a).eval 1 := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (a144438DiagonalLag_hasNonnegCoeffs ha k) (by positivity)

/-- The diagonal endpoint value `p_n(1)`. -/
def a144438DiagonalAtOne (n : ℕ) (a : ℝ) : ℝ :=
  (a144438Diagonal n a).eval 1

/-- The lag endpoint value `k_n(1)`. -/
def a144438DiagonalLagAtOne (n : ℕ) (a : ℝ) : ℝ :=
  (a144438DiagonalLag n a).eval 1

/-- The endpoint quotient `p_n(1) / p_{n-1}(1)`. The intended uses have
positive rank. -/
def a144438Gamma (n : ℕ) (a : ℝ) : ℝ :=
  a144438DiagonalAtOne n a / a144438DiagonalAtOne (n - 1) a

/-- The normalized lag endpoint `k_n(1) / p_n(1)`. -/
def a144438Kappa (n : ℕ) (a : ℝ) : ℝ :=
  a144438DiagonalLagAtOne n a / a144438DiagonalAtOne n a

/-- The normalized diagonal correction `n a / γ_n`. -/
def a144438Eta (n : ℕ) (a : ℝ) : ℝ :=
  (n : ℝ) * a / a144438Gamma n a

@[simp]
theorem a144438DiagonalAtOne_zero (a : ℝ) :
    a144438DiagonalAtOne 0 a = 1 := by
  simp [a144438DiagonalAtOne]

@[simp]
theorem a144438DiagonalAtOne_one (a : ℝ) :
    a144438DiagonalAtOne 1 a = 2 + a := by
  simp [a144438DiagonalAtOne]
  ring

@[simp]
theorem a144438DiagonalLagAtOne_one (a : ℝ) :
    a144438DiagonalLagAtOne 1 a = 1 := by
  simp [a144438DiagonalLagAtOne]

@[simp]
theorem a144438Gamma_one (a : ℝ) : a144438Gamma 1 a = 2 + a := by
  simp [a144438Gamma]

@[simp]
theorem a144438Kappa_one (a : ℝ) : a144438Kappa 1 a = 1 / (2 + a) := by
  simp [a144438Kappa]

/-- Evaluation at one of the diagonal lag recurrence. -/
theorem a144438DiagonalLagAtOne_succ (n : ℕ) (a : ℝ) :
    a144438DiagonalLagAtOne (n + 1) a =
      a144438DiagonalAtOne n a + a * a144438DiagonalLagAtOne n a := by
  change (a144438DiagonalLag (n + 1) a).eval 1 =
    (a144438Diagonal n a).eval 1 +
      a * (a144438DiagonalLag n a).eval 1
  rw [a144438DiagonalLag_succ]
  simp only [eval_add, eval_mul, eval_C]

/-- Evaluation at one of the positive-rank diagonal recurrence. -/
theorem a144438DiagonalAtOne_succ_succ (n : ℕ) (a : ℝ) :
    a144438DiagonalAtOne (n + 2) a =
      ((n : ℝ) + 3 + a) * a144438DiagonalAtOne (n + 1) a -
        ((n : ℝ) + 1) * a * a144438DiagonalAtOne n a +
          a144438DiagonalLagAtOne (n + 1) a := by
  rw [a144438DiagonalAtOne, a144438Diagonal_succ,
    a144438DiagonalCompanion_succ_eq]
  simp only [eval_add, eval_sub, eval_mul, eval_one, eval_X, eval_C, one_mul,
    a144438DiagonalAtOne, a144438DiagonalLagAtOne]
  ring

/-- The exact endpoint quotient recurrence. -/
theorem a144438Gamma_succ_succ (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    a144438Gamma (n + 2) a =
      (n : ℝ) + 3 + a - ((n : ℝ) + 1) * a /
        a144438Gamma (n + 1) a + a144438Kappa (n + 1) a := by
  have hp0 := a144438Diagonal_eval_one_pos (n := n) ha
  have hp1 := a144438Diagonal_eval_one_pos (n := n + 1) ha
  rw [a144438Gamma, a144438Gamma, a144438Kappa]
  rw [show n + 2 - 1 = n + 1 by lia, show n + 1 - 1 = n by lia]
  rw [a144438DiagonalAtOne_succ_succ]
  have hp0' : a144438DiagonalAtOne n a ≠ 0 := ne_of_gt hp0
  have hp1' : a144438DiagonalAtOne (n + 1) a ≠ 0 := ne_of_gt hp1
  field_simp [hp0', hp1']

/-- The exact normalized lag recurrence. -/
theorem a144438Kappa_succ (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    a144438Kappa (n + 1) a =
      (1 + a * a144438Kappa n a) / a144438Gamma (n + 1) a := by
  have hp := a144438Diagonal_eval_one_pos (n := n) ha
  have hpSucc := a144438Diagonal_eval_one_pos (n := n + 1) ha
  rw [a144438Kappa, a144438Gamma, a144438Kappa,
    a144438DiagonalLagAtOne_succ]
  simp only [Nat.add_sub_cancel]
  have hp' : a144438DiagonalAtOne n a ≠ 0 := ne_of_gt hp
  have hpSucc' : a144438DiagonalAtOne (n + 1) a ≠ 0 := ne_of_gt hpSucc
  field_simp [hp', hpSucc']

/-- Simultaneous endpoint bounds for every positive rank. -/
theorem a144438_endpoint_bounds {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * a + 1 < a144438Gamma n a ∧
        2 + a ≤ a144438Gamma n a ∧
          0 ≤ a144438Kappa n a ∧ a144438Kappa n a ≤ 1 / 2 := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero =>
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
        add_zero, one_mul, Nat.reduceAdd]
      change a + 1 < a144438Gamma 1 a ∧
        2 + a ≤ a144438Gamma 1 a ∧
          0 ≤ a144438Kappa 1 a ∧ a144438Kappa 1 a ≤ 1 / 2
      rw [a144438Gamma_one, a144438Kappa_one]
      constructor
      · linarith
      constructor
      · rfl
      constructor
      · positivity
      · have : 0 < 2 + a := by linarith
        rw [div_le_iff₀ this]
        linarith
  | succ m ih =>
      have ih' :
          (m + 1 : ℝ) * a + 1 < a144438Gamma (m + 1) a ∧
            2 + a ≤ a144438Gamma (m + 1) a ∧
              0 ≤ a144438Kappa (m + 1) a ∧
                a144438Kappa (m + 1) a ≤ 1 / 2 := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.add_comm, add_comm] using ih
      have hgammaRec := a144438Gamma_succ_succ m ha0
      have hkappaRec := a144438Kappa_succ (m + 1) ha0
      have hgammaPos : 0 < a144438Gamma (m + 1) a := by
        have : 0 ≤ (m + 1 : ℝ) * a := by positivity
        linarith [ih'.1]
      have heta : (m + 1 : ℝ) * a / a144438Gamma (m + 1) a < 1 := by
        rw [div_lt_one hgammaPos]
        linarith [ih'.1]
      have hgammaStrong :
          (m + 2 : ℝ) + a < a144438Gamma (m + 2) a := by
        rw [hgammaRec]
        linarith [heta, ih'.2.2.1]
      have hgammaLinear :
          (m + 2 : ℝ) * a + 1 < a144438Gamma (m + 2) a := by
        have : (m + 2 : ℝ) * a + 1 ≤ (m + 2 : ℝ) + a := by
          nlinarith
        linarith
      have hgammaFloor : 2 + a ≤ a144438Gamma (m + 2) a := by
        linarith
      have hkappaNonneg : 0 ≤ a144438Kappa (m + 2) a := by
        rw [hkappaRec]
        have hnum : 0 ≤ 1 + a * a144438Kappa (m + 1) a := by
          exact add_nonneg zero_le_one (mul_nonneg ha0 ih'.2.2.1)
        exact div_nonneg hnum
          (le_trans (by linarith : 0 ≤ 2 + a) hgammaFloor)
      have hkappaHalf : a144438Kappa (m + 2) a ≤ 1 / 2 := by
        rw [hkappaRec, div_le_iff₀ (lt_of_lt_of_le (by linarith) hgammaFloor)]
        have hmul := mul_le_mul_of_nonneg_left ih'.2.2.2 ha0
        nlinarith [hmul]
      have hind := And.intro hgammaLinear
        (And.intro hgammaFloor (And.intro hkappaNonneg hkappaHalf))
      convert hind using 1 <;> norm_num <;> ring_nf

/-- The endpoint correction satisfies `η_n < 1`. -/
theorem a144438Eta_lt_one {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : a144438Eta n a < 1 := by
  have hgamma := (a144438_endpoint_bounds ha0 ha1 n hn).1
  have hna : 0 ≤ (n : ℝ) * a := mul_nonneg (by positivity) ha0
  have hgammaPos : 0 < a144438Gamma n a := by linarith
  rw [a144438Eta, div_lt_one hgammaPos]
  linarith

end RealRooted.Applications.OEIS
