module

public import RealRooted.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.LinearPowerFamily
import RealRooted.Hadamard
import RealRooted.NarayanaTransformation
import RealRooted.Tactic.RowInterlacing

/-!
# Original certificate-context regressions for #2366

The A181543 recurrence, supporting cube-binomial certificate, and endpoint goals are copied
from `sqrt-of-2/real-rooted-oeis-proofs`, revision `97fb3191`, `ProofsOeis/A181543.lean`.
Only supporting proofs are split into coefficient ranges; the original endpoint calls remain.
The tactic must reuse the earlier strict certificate and degree equation before reading the
unsupported derivative-lag recurrence. No target conclusion is assumed.
-/

@[expose] public section

open RealRooted Polynomial

namespace RealRooted.Tactic.Examples.RowRegressions2366Certificates

noncomputable section

/-- The original downstream recurrence for A181543. -/
def A181543 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (12 + (9 * (n : ℝ)))))
      * X + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-12 + (-9 * (n : ℝ))))) *
      X ^ 2)) * (A181543 (n + 1)).derivative + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n
      : ℝ))))) * (11 + (-1 * ((3 + (n : ℝ))) ^ (2)) + (6 * (n : ℝ))))) + C (((1 / ((-5 + ((3 + (n
      : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-58 + (-27 * (n : ℝ)) + (8 * ((3 + (n : ℝ))) ^ (2))))) *
      X)) * A181543 (n + 1) + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-16 +
      (-8 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) +
      (-2 * (n : ℝ))))) * (-32 + (-16 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2))))) * X + C (((1 /
      ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 * ((3 + (n :
      ℝ))) ^ (2))))) * X ^ 2)) * A181543 n


/-- Schur–Szegő composition with binomial-cube coefficients. -/
private def cubePoly (n : ℕ) : ℝ[X] :=
  schurSzegoComp n (narayanaPolynomial 0 n) (narayanaPolynomial 0 n)

private lemma coeff_cubePoly_of_le {n k : ℕ} (hk : k ≤ n) :
    (cubePoly n).coeff k = (Nat.choose n k : ℝ) ^ 3 := by
  rw [cubePoly, coeff_schurSzegoComp_of_le hk]
  rw [coeff_narayanaPolynomial_of_le hk]
  simp only [narayanaTransformCoeff, add_zero, zero_add, Nat.choose_self, Nat.cast_one,
    div_one]
  grind

private lemma coeff_cubePoly_of_lt {n k : ℕ} (hk : n < k) :
    (cubePoly n).coeff k = 0 :=
  coeff_schurSzegoComp_eq_zero_of_lt hk _ _

private lemma coeff_X_mul_all (p : ℝ[X]) (k : ℕ) :
    (X * p).coeff k = if 1 ≤ k then p.coeff (k - 1) else 0 := by
  rw [show X = X ^ 1 by simp, coeff_X_pow_mul']

private lemma choose_ratio (x y : ℕ) (h : y ≤ x) :
    (x.choose y : ℝ) =
      x.factorial / (y.factorial * (x - y).factorial) := by
  have hne : (y.factorial : ℝ) * (x - y).factorial ≠ 0 := by positivity
  rw [eq_div_iff hne]
  have hfac : (x.choose y : ℝ) * (y.factorial * (x - y).factorial) =
      x.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial h]
    grind
  assumption

/-- The normalized derivative-lag operator in the original cube-binomial model. -/
private def cubeNext (n : ℕ) : ℝ[X] :=
      (C ((9 * (n : ℝ) + 12) / (n + 2) ^ 2) * X -
          C ((9 * (n : ℝ) + 12) / (n + 2) ^ 2) * X ^ 2) *
          (cubePoly (n + 1)).derivative +
      (C ((2 - (n : ℝ) ^ 2) / (n + 2) ^ 2) +
          C ((8 * (n : ℝ) ^ 2 + 21 * n + 14) / (n + 2) ^ 2) * X) *
          cubePoly (n + 1) +
      (C (2 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) +
          C (4 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) * X +
          C (2 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) * X ^ 2) *
          cubePoly n

/-- The constant and linear coefficients satisfy the model recurrence. -/
private lemma cubePoly_coeff_rec_small (n k : ℕ) (hk : k < 2) :
    (cubePoly (n + 2)).coeff k = (cubeNext n).coeff k := by
  unfold cubeNext
  ring_nf
  simp only [mul_assoc]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_mul_all, coeff_derivative]
  by_cases hk0 : k = 0
  · subst k
    simp_rw [coeff_cubePoly_of_le (Nat.zero_le _)]
    norm_num
    field_simp
    ring
  have hk1 : k = 1 := by lia
  subst k
  simp_rw [coeff_cubePoly_of_le (Nat.zero_le _)]
  by_cases hn : n = 0
  · subst n
    rw [coeff_cubePoly_of_le (n := 2) (by lia),
      coeff_cubePoly_of_le (n := 1) (by lia)]
    rw [coeff_cubePoly_of_lt (n := 0) (k := 1) (by norm_num)]
    norm_num
  simp_rw [coeff_cubePoly_of_le (n := 2 + n) (k := 1) (by lia)]
  simp_rw [coeff_cubePoly_of_le (n := 1 + n) (k := 1) (by lia)]
  simp_rw [coeff_cubePoly_of_le (n := n) (k := 1) (by lia)]
  norm_num
  grind

/-- Interior coefficients satisfy the model recurrence by factorial ratios. -/
private lemma cubePoly_coeff_rec_interior (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    (cubePoly (n + 2)).coeff k = (cubeNext n).coeff k := by
  unfold cubeNext
  ring_nf
  simp only [mul_assoc]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_mul_all, coeff_derivative]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk2
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hkn
  simp only [show 1 ≤ j + 2 by lia, show 2 ≤ j + 2 by assumption, ite_true]
  rw [coeff_cubePoly_of_le (by lia), coeff_cubePoly_of_le (by lia),
    coeff_cubePoly_of_le (by lia), coeff_cubePoly_of_le (by lia),
    coeff_cubePoly_of_le (by lia), coeff_cubePoly_of_le (by lia)]
  simp only [Nat.add_sub_cancel_right]
  rw [coeff_cubePoly_of_le (by lia), coeff_cubePoly_of_le (by assumption)]
  have hs1 : j + 2 - 1 = j + 1 := by lia
  have hs2 : a + (j + 2) - (j + 2) = a := by lia
  have hs3 : 1 + (a + (j + 2)) - (j + 2) = a + 1 := by lia
  have hs4 : 1 + (a + (j + 2)) - (j + 1) = a + 2 := by lia
  have hs5 : a + (j + 2) - (j + 1) = a + 1 := by lia
  have hs6 : 2 + (a + (j + 2)) - (j + 2) = a + 2 := by lia
  have hs7 : a + (j + 2) - j = a + 2 := by lia
  simp only [hs1]
  rw [choose_ratio (2 + (a + (j + 2))) (j + 2) (by lia),
    choose_ratio (1 + (a + (j + 2))) (j + 2) (by lia),
    choose_ratio (1 + (a + (j + 2))) (j + 1) (by lia),
    choose_ratio (a + (j + 2)) (j + 2) (by assumption),
    choose_ratio (a + (j + 2)) (j + 1) (by lia),
    choose_ratio (a + (j + 2)) j (by lia)]
  simp only [hs2, hs3, hs4, hs5, hs6, hs7]
  simp only [Nat.factorial_succ]
  rw [show (2 + (a + (j + 2))).factorial =
      (2 + (a + (j + 2))) * (1 + (a + (j + 2))).factorial by
        rw [show 2 + (a + (j + 2)) = (1 + (a + (j + 2))) + 1 by lia,
          Nat.factorial_succ],
    show (1 + (a + (j + 2))).factorial =
      (1 + (a + (j + 2))) * (a + (j + 2)).factorial by
        rw [show 1 + (a + (j + 2)) = (a + (j + 2)) + 1 by lia,
          Nat.factorial_succ]]
  push_cast
  field_simp
  ring

/-- The penultimate coefficient satisfies the model recurrence. -/
private lemma cubePoly_coeff_rec_succ (n k : ℕ) (hk : k = n + 1) (hn1 : 1 ≤ n) :
    (cubePoly (n + 2)).coeff k = (cubeNext n).coeff k := by
  unfold cubeNext
  ring_nf
  simp only [mul_assoc]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_mul_all, coeff_derivative]
  subst k
  simp only [show 1 ≤ n + 1 by lia, ite_true]
  by_cases htwo : 2 ≤ n + 1
  · simp only [htwo, ite_true]
    have hs1 : n + 1 - 1 = n := by lia
    have hs2 : n + 1 - 2 = n - 1 := by lia
    have hs4 : n - 1 + 1 = n := by lia
    simp only [hs1, hs2, hs4]
    simp_rw [coeff_cubePoly_of_le (n := 2 + n) (k := n + 1) (by lia)]
    simp_rw [coeff_cubePoly_of_le (n := 1 + n) (k := n + 1) (by lia)]
    simp_rw [coeff_cubePoly_of_le (n := 1 + n) (k := n) (by lia)]
    simp_rw [coeff_cubePoly_of_le (n := n) (k := n) (by lia)]
    simp_rw [coeff_cubePoly_of_le (n := n) (k := n - 1) (by lia)]
    simp_rw [coeff_cubePoly_of_lt (n := n) (k := n + 1) (by lia)]
    have hcomm : n + 1 = 1 + n := by lia
    simp only [hcomm, Nat.choose_self, Nat.cast_one, one_pow]
    rw [choose_ratio (2 + n) (1 + n) (by lia),
      choose_ratio (1 + n) n (by lia),
      choose_ratio n (n - 1) (by lia)]
    have hd1 : 1 + n - n = 1 := by lia
    have hd2 : n - (n - 1) = 1 := by lia
    have hd3 : 2 + n - (1 + n) = 1 := by lia
    simp only [hd1, hd2, hd3, Nat.factorial_one, Nat.cast_one]
    rw [show (2 + n).factorial = (2 + n) * (1 + n).factorial by
          rw [show 2 + n = (1 + n) + 1 by lia, Nat.factorial_succ],
      show (1 + n).factorial = (1 + n) * n.factorial by
          rw [show 1 + n = n + 1 by lia, Nat.factorial_succ],
      show n.factorial = n * (n - 1).factorial by
          calc
            n.factorial = ((n - 1) + 1).factorial := by simp_all
            _ = ((n - 1) + 1) * (n - 1).factorial := Nat.factorial_succ _
            _ = n * (n - 1).factorial := by simp_all]
    push_cast
    have : ((n - 1 : ℕ) : ℝ) + 1 = n := by simp_all
    have hncast' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by linarith
    field_simp
    grind
  · lia

/-- The leading coefficient satisfies the model recurrence. -/
private lemma cubePoly_coeff_rec_succ_succ (n k : ℕ) (hk : k = n + 2) :
    (cubePoly (n + 2)).coeff k = (cubeNext n).coeff k := by
  unfold cubeNext
  ring_nf
  simp only [mul_assoc]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_mul_all, coeff_derivative]
  subst k
  simp only [show 1 ≤ n + 2 by lia, show 2 ≤ n + 2 by lia, ite_true]
  have hs1 : n + 2 - 1 = n + 1 := by lia
  have hs2 : n + 2 - 2 = n := by lia
  simp only [hs1, hs2]
  simp_rw [coeff_cubePoly_of_le (n := 2 + n) (k := n + 2) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := 1 + n) (k := n + 2) (by lia)]
  simp_rw [coeff_cubePoly_of_le (n := 1 + n) (k := n + 1) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := n) (k := n + 1) (by lia)]
  simp_rw [coeff_cubePoly_of_le (n := n) (k := n) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := n) (k := n + 2) (by lia)]
  have hcomm2 : 2 + n = n + 2 := by lia
  have hcomm1 : 1 + n = n + 1 := by lia
  simp only [hcomm2, hcomm1, Nat.choose_self, Nat.cast_one, one_pow]
  field_simp
  ring

/-- Coefficients beyond the degree vanish on both sides of the model recurrence. -/
private lemma cubePoly_coeff_rec_above (n k : ℕ) (hkbig : n + 2 < k) :
    (cubePoly (n + 2)).coeff k = (cubeNext n).coeff k := by
  unfold cubeNext
  ring_nf
  simp only [mul_assoc]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_mul_all, coeff_derivative]
  simp only [show 1 ≤ k by lia, show 2 ≤ k by lia, ite_true]
  simp_rw [coeff_cubePoly_of_lt (n := 2 + n) (k := k) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := 1 + n) (k := k) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := 1 + n) (k := k - 1 + 1) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := 1 + n) (k := k - 1) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := n) (k := k) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := n) (k := k - 1) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := n) (k := k - 2) (by lia)]
  simp_rw [coeff_cubePoly_of_lt (n := 1 + n) (k := k - 2 + 1) (by lia)]
  ring

/-- The original model recurrence, assembled from its coefficient ranges. -/
private lemma cubePoly_rec (n : ℕ) :
    cubePoly (n + 2) =
      (C ((9 * (n : ℝ) + 12) / (n + 2) ^ 2) * X -
          C ((9 * (n : ℝ) + 12) / (n + 2) ^ 2) * X ^ 2) *
          (cubePoly (n + 1)).derivative +
      (C ((2 - (n : ℝ) ^ 2) / (n + 2) ^ 2) +
          C ((8 * (n : ℝ) ^ 2 + 21 * n + 14) / (n + 2) ^ 2) * X) *
          cubePoly (n + 1) +
      (C (2 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) +
          C (4 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) * X +
          C (2 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) * X ^ 2) *
          cubePoly n := by
  change cubePoly (n + 2) = cubeNext n
  ext k
  rcases lt_or_ge k 2 with hk | hk
  · exact cubePoly_coeff_rec_small n k hk
  rcases le_or_gt k n with hkn | hkn
  · exact cubePoly_coeff_rec_interior n k hk hkn
  by_cases hk1 : k = n + 1
  · exact cubePoly_coeff_rec_succ n k hk1 (by lia)
  by_cases hk2 : k = n + 2
  · exact cubePoly_coeff_rec_succ_succ n k hk2
  exact cubePoly_coeff_rec_above n k (by lia)

private lemma A181543_eq_cubePoly (n : ℕ) : A181543 n = cubePoly n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      ext k
      cases k with
      | zero =>
          rw [coeff_cubePoly_of_le (by lia)]
          norm_num [A181543]
      | succ k =>
          rw [coeff_cubePoly_of_lt (by lia)]
          simp [A181543, coeff_one]
  | one =>
      ext k
      rcases k with (_ | _ | k)
      · rw [coeff_cubePoly_of_le (by lia)]
        norm_num [A181543]
      · rw [coeff_cubePoly_of_le (by lia)]
        norm_num [A181543, coeff_one, coeff_X]
      · rw [coeff_cubePoly_of_lt (by lia)]
        simp [A181543, coeff_one, coeff_X]
  | more n ih0 ih1 =>
      rw [A181543, ih0, ih1, cubePoly_rec]
      ring_nf
      grind

private theorem A181543_coeff_of_le {n k : ℕ} (hk : k ≤ n) :
    (A181543 n).coeff k = (Nat.choose n k : ℝ) ^ 3 := by
  rw [A181543_eq_cubePoly]
  exact coeff_cubePoly_of_le hk

private theorem A181543_coeff_of_lt {n k : ℕ} (hk : n < k) :
    (A181543 n).coeff k = 0 := by
  rw [A181543_eq_cubePoly]
  exact coeff_cubePoly_of_lt hk
private theorem A181543_natDegree (n : ℕ) : (A181543 n).natDegree = n := by rr_row_natDegree

private lemma A181543_eq_hadamard (n : ℕ) :
    A181543 n =
      hadamardProduct ((X + 1 : ℝ[X]) ^ n) (narayanaPolynomial 0 n) := by
  ext k
  rw [coeff_hadamardProduct, Polynomial.coeff_X_add_one_pow]
  by_cases hk : k ≤ n
  · rw [A181543_coeff_of_le hk, coeff_narayanaPolynomial_of_le hk]
    simp only [narayanaTransformCoeff, add_zero, zero_add, Nat.choose_self, Nat.cast_one,
      div_one]
    ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [A181543_coeff_of_lt hnk, coeff_narayanaPolynomial_of_lt hnk,
      Nat.choose_eq_zero_of_lt hnk]
    simp

private lemma prec_narayana_zero_succ (n : ℕ) :
    StrictInterl (narayanaPolynomial 0 n) (narayanaPolynomial 0 (n + 1)) := by
  cases n with
  | zero =>
      rw [narayanaPolynomial_zero_right, narayanaPolynomial_one]
      simpa using strictInterl_X_add_C_pow_succ 1 0
  | succ n =>
      simpa [Nat.succ_eq_add_one] using strictInterl_narayanaPolynomial_succ 0 n

private lemma A181543_ne_zero_aux (n : ℕ) : A181543 n ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  rw [A181543_coeff_of_le (Nat.zero_le n)] at hcoeff
  norm_num at hcoeff

private lemma A181543_prec_aux (n : ℕ) :
    StrictInterl (A181543 n) (A181543 (n + 1)) := by
  have hprec0 :=
    RealRooted.StrictInterl.interl_hadamardProduct
      (f := (X + 1 : ℝ[X]) ^ n)
      (g := (X + 1 : ℝ[X]) ^ (n + 1))
      (p := narayanaPolynomial 0 n)
      (q := narayanaPolynomial 0 (n + 1))
      (by simpa [add_comm] using
        (hasNonnegCoeffs_linear_pow (a := 1) (b := 1)
          (by norm_num) (by norm_num) n))
      (by simpa [add_comm] using
        (hasNonnegCoeffs_linear_pow (a := 1) (b := 1)
          (by norm_num) (by norm_num) (n + 1)))
      (hasNonnegCoeffs_narayanaPolynomial 0 n)
      (hasNonnegCoeffs_narayanaPolynomial 0 (n + 1))
      (by simpa using strictInterl_X_add_C_pow_succ 1 n)
      (prec_narayana_zero_succ n)
  rw [← A181543_eq_hadamard n,
    ← A181543_eq_hadamard (n + 1)] at hprec0
  exact (RealRooted.Interl.toStrictInterl_of_ne (hprec0))
    (A181543_ne_zero_aux n) (A181543_ne_zero_aux (n + 1))

/-- The original interlacing call from #2366. -/
theorem A181543_interlaces (n : ℕ) : RealRooted.Interlaces (A181543 n) (A181543 (n + 1)) := by
  rr_row_interlaces


/-- The original splitting call from #2366. -/
theorem A181543_splits (n : ℕ) : (A181543 n).Splits := by rr_row_splits

end
end RealRooted.Tactic.Examples.RowRegressions2366Certificates
