import RealRooted.Recurrence.Uniqueness
import RealRooted.LinearPowerFamily
import RealRooted.Hadamard.GarloffWagner
import RealRooted.Hadamard
import RealRooted.NarayanaTransformation

open RealRooted
open Polynomial

/-!
# Binomial-cube rows

The row polynomial has coefficients `C(n, k)^3`.  Its Schur--Szegő model
proves splitting, and its Hadamard--Narayana model proves consecutive
interlacing.  The final two theorems transfer these facts to any sequence
with the same lag-two recurrence and initial rows.
-/

noncomputable section

namespace RealRooted.Applications.OEIS.A181543

/-- The polynomial with coefficient of `X ^ k` equal to `C(n, k)^3`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (12 + (9 * (n :
    ℝ))))) * X + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-12 + (-9 * (n :
    ℝ))))) * X ^ 2)) * (polynomial (n + 1)).derivative + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2)
    +
    (-2 * (n : ℝ))))) * (11 + (-1 * ((3 + (n : ℝ))) ^ (2)) +
    (6 * (n : ℝ))))) + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) +
    (-2 * (n : ℝ))))) * (-58 + (-27 * (n : ℝ)) + (8 * ((3 + (n : ℝ))) ^
    (2))))) * X)) * polynomial (n + 1) + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n :
    ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) +
    C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
    (-32 + (-16 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2))))) * X
    + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 *
    ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * polynomial n

private def schurModel (n : ℕ) : ℝ[X] :=
  schurSzegoComp n (narayanaPolynomial 0 n) (narayanaPolynomial 0 n)

private lemma coeff_schurModel_of_le {n k : ℕ} (hk : k ≤ n) :
    (schurModel n).coeff k = (Nat.choose n k : ℝ) ^ 3 := by
  rw [schurModel, coeff_schurSzegoComp_of_le hk]
  rw [coeff_narayanaPolynomial_of_le hk]
  simp [narayanaTransformCoeff]
  grind

private lemma coeff_schurModel_of_lt {n k : ℕ} (hk : n < k) :
    (schurModel n).coeff k = 0 :=
  coeff_schurSzegoComp_eq_zero_of_lt hk _ _

private lemma schurModel_splits (n : ℕ) : (schurModel n).Splits := by
  apply splits_schurSzegoComp_of_isPF n
  · exact narayanaPolynomialRootLocation 0 n
  · intro h
    have := congrArg (fun p : ℝ[X] => p.coeff 0) h
    rw [coeff_narayanaPolynomial_of_le (Nat.zero_le n)] at this
    simp [narayanaTransformCoeff] at this
  · exact natDegree_narayanaPolynomial_le 0 n
  · intro h
    have := congrArg (fun p : ℝ[X] => p.coeff 0) h
    rw [coeff_narayanaPolynomial_of_le (Nat.zero_le n)] at this
    simp [narayanaTransformCoeff] at this
  · exact natDegree_narayanaPolynomial_le 0 n
  · exact splits_narayanaPolynomial 0 n

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

private lemma schurModel_rec (n : ℕ) :
    schurModel (n + 2) =
      (C ((9 * (n : ℝ) + 12) / (n + 2) ^ 2) * X -
          C ((9 * (n : ℝ) + 12) / (n + 2) ^ 2) * X ^ 2) *
          (schurModel (n + 1)).derivative +
      (C ((2 - (n : ℝ) ^ 2) / (n + 2) ^ 2) +
          C ((8 * (n : ℝ) ^ 2 + 21 * n + 14) / (n + 2) ^ 2) * X) *
          schurModel (n + 1) +
      (C (2 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) +
          C (4 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) * X +
          C (2 * (n + 1 : ℝ) ^ 2 / (n + 2) ^ 2) * X ^ 2) *
          schurModel n := by
  ext k
  ring_nf
  simp only [mul_assoc]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_mul_all, coeff_derivative]
  by_cases hk0 : k = 0
  · subst k
    simp_rw [coeff_schurModel_of_le (Nat.zero_le _)]
    norm_num
    field_simp
    ring
  by_cases hk1 : k = 1
  · subst k
    simp_rw [coeff_schurModel_of_le (Nat.zero_le _)]
    by_cases hn : n = 0
    · subst n
      rw [coeff_schurModel_of_le (n := 2) (by lia),
        coeff_schurModel_of_le (n := 1) (by lia)]
      rw [coeff_schurModel_of_lt (n := 0) (k := 1) (by norm_num)]
      norm_num
    simp_rw [coeff_schurModel_of_le (n := 2 + n) (k := 1) (by lia)]
    simp_rw [coeff_schurModel_of_le (n := 1 + n) (k := 1) (by lia)]
    simp_rw [coeff_schurModel_of_le (n := n) (k := 1) (by lia)]
    norm_num
    grind
  by_cases hkn : k ≤ n
  · have hk2 : 2 ≤ k := by lia
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk2
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hkn
    simp only [show 1 ≤ j + 2 by lia, show 2 ≤ j + 2 by assumption, ite_true]
    rw [coeff_schurModel_of_le (by lia), coeff_schurModel_of_le (by lia),
      coeff_schurModel_of_le (by lia), coeff_schurModel_of_le (by lia),
      coeff_schurModel_of_le (by lia), coeff_schurModel_of_le (by lia)]
    simp only [Nat.add_sub_cancel_right]
    rw [coeff_schurModel_of_le (by lia), coeff_schurModel_of_le (by assumption)]
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
  by_cases hkN1 : k = n + 1
  · subst k
    have hn1 : 1 ≤ n := by lia
    simp only [show 1 ≤ n + 1 by lia, ite_true]
    by_cases htwo : 2 ≤ n + 1
    · simp only [htwo, ite_true]
      have hs1 : n + 1 - 1 = n := by lia
      have hs2 : n + 1 - 2 = n - 1 := by lia
      have hs4 : n - 1 + 1 = n := by lia
      simp only [hs1, hs2, hs4]
      simp_rw [coeff_schurModel_of_le (n := 2 + n) (k := n + 1) (by lia)]
      simp_rw [coeff_schurModel_of_le (n := 1 + n) (k := n + 1) (by lia)]
      simp_rw [coeff_schurModel_of_le (n := 1 + n) (k := n) (by lia)]
      simp_rw [coeff_schurModel_of_le (n := n) (k := n) (by lia)]
      simp_rw [coeff_schurModel_of_le (n := n) (k := n - 1) (by lia)]
      simp_rw [coeff_schurModel_of_lt (n := n) (k := n + 1) (by lia)]
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
  by_cases hkN2 : k = n + 2
  · subst k
    simp only [show 1 ≤ n + 2 by lia, show 2 ≤ n + 2 by lia, ite_true]
    have hs1 : n + 2 - 1 = n + 1 := by lia
    have hs2 : n + 2 - 2 = n := by lia
    simp only [hs1, hs2]
    simp_rw [coeff_schurModel_of_le (n := 2 + n) (k := n + 2) (by lia)]
    simp_rw [coeff_schurModel_of_lt (n := 1 + n) (k := n + 2) (by lia)]
    simp_rw [coeff_schurModel_of_le (n := 1 + n) (k := n + 1) (by lia)]
    simp_rw [coeff_schurModel_of_lt (n := n) (k := n + 1) (by lia)]
    simp_rw [coeff_schurModel_of_le (n := n) (k := n) (by lia)]
    simp_rw [coeff_schurModel_of_lt (n := n) (k := n + 2) (by lia)]
    have hcomm2 : 2 + n = n + 2 := by lia
    have hcomm1 : 1 + n = n + 1 := by lia
    simp only [hcomm2, hcomm1, Nat.choose_self, Nat.cast_one, one_pow]
    field_simp
    ring
  have hkbig : n + 2 < k := by lia
  simp only [show 1 ≤ k by lia, show 2 ≤ k by lia, ite_true]
  simp_rw [coeff_schurModel_of_lt (n := 2 + n) (k := k) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := 1 + n) (k := k) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := 1 + n) (k := k - 1 + 1) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := 1 + n) (k := k - 1) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := n) (k := k) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := n) (k := k - 1) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := n) (k := k - 2) (by lia)]
  simp_rw [coeff_schurModel_of_lt (n := 1 + n) (k := k - 2 + 1) (by lia)]
  ring

private lemma polynomial_eq_schurModel (n : ℕ) : polynomial n = schurModel n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      ext k
      cases k with
      | zero =>
          rw [coeff_schurModel_of_le (by lia)]
          norm_num [polynomial]
      | succ k =>
          rw [coeff_schurModel_of_lt (by lia)]
          simp [polynomial, coeff_one]
  | one =>
      ext k
      rcases k with (_ | _ | k)
      · rw [coeff_schurModel_of_le (by lia)]
        norm_num [polynomial]
      · rw [coeff_schurModel_of_le (by lia)]
        norm_num [polynomial, coeff_one, coeff_X]
      · rw [coeff_schurModel_of_lt (by lia)]
        simp [polynomial, coeff_one, coeff_X]
  | more n ih0 ih1 =>
      rw [polynomial, ih0, ih1, schurModel_rec]
      ring_nf
      grind

private theorem polynomial_coeff_of_le {n k : ℕ} (hk : k ≤ n) :
    (polynomial n).coeff k = (Nat.choose n k : ℝ) ^ 3 := by
  rw [polynomial_eq_schurModel]
  exact coeff_schurModel_of_le hk

private theorem polynomial_coeff_of_lt {n k : ℕ} (hk : n < k) :
    (polynomial n).coeff k = 0 := by
  rw [polynomial_eq_schurModel]
  exact coeff_schurModel_of_lt hk

private theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun k hk =>
      polynomial_coeff_of_lt (n := n) (k := k) hk))
  rw [polynomial_coeff_of_le (n := n) (k := n) (by lia)]
  norm_num

private lemma polynomial_eq_hadamard (n : ℕ) :
    polynomial n =
      hadamardProduct ((X + 1 : ℝ[X]) ^ n) (narayanaPolynomial 0 n) := by
  ext k
  rw [coeff_hadamardProduct, Polynomial.coeff_X_add_one_pow]
  by_cases hk : k ≤ n
  · rw [polynomial_coeff_of_le hk, coeff_narayanaPolynomial_of_le hk]
    simp [narayanaTransformCoeff]
    ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [polynomial_coeff_of_lt hnk, coeff_narayanaPolynomial_of_lt hnk,
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

private lemma polynomial_ne_zero_aux (n : ℕ) : polynomial n ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  rw [polynomial_coeff_of_le (Nat.zero_le n)] at hcoeff
  norm_num at hcoeff

private lemma polynomial_prec_aux (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  have hprec0 :=
    StrictInterl.interl_hadamardProduct
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
  rw [← polynomial_eq_hadamard n,
    ← polynomial_eq_hadamard (n + 1)] at hprec0
  exact (RealRooted.Interl.toStrictInterl_of_ne (hprec0))
    (polynomial_ne_zero_aux n) (polynomial_ne_zero_aux (n + 1))

/-- Consecutive binomial-cube rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    RealRooted.Interlaces (polynomial n) (polynomial (n + 1)) := by
  exact (RealRooted.StrictInterl.toInterlaces ((polynomial_prec_aux n))) (by
    rw [polynomial_natDegree, polynomial_natDegree])

/-- Every binomial-cube row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  rw [polynomial_eq_schurModel]
  exact schurModel_splits n

/-- The lag-two recurrence operator whose binomial-cube model is `polynomial`. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (12 + (9 * (n : ℝ))))) * X + C
    (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
    (-12 + (-9 * (n : ℝ))))) * X ^ 2))
    * p.derivative + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (11 + (-1 *
    ((3 + (n : ℝ))) ^ (2)) + (6 * (n : ℝ))))) +
    C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n
    : ℝ))))) * (-58 + (-27 * (n : ℝ)) + (8 * ((3 + (n : ℝ))) ^ (2))))) * X)) * p + ((C (((1 /
    ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 * ((3 + (n :
    ℝ))) ^ (2))))) + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-32 + (-16 *
    (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2))))) * X +
    C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2
    * (n : ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * q

/-- The binomial-cube model satisfies `recurrence`. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 2) =
      nextRow n (polynomial (n + 1)) (polynomial n) := by
  rfl

/-- A sequence with the binomial-cube initial rows and update has split rows. -/
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl))
    (hone.trans (show (1 + X : ℝ[X]) = polynomial 1 by rfl))
    hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows of a sequence with the binomial-cube update interlace. -/
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    RealRooted.Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl))
    (hone.trans (show (1 + X : ℝ[X]) = polynomial 1 by rfl))
    hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n


end RealRooted.Applications.OEIS.A181543
