import RealRooted.Derivative.Interlacing
import RealRooted.DerivativeRecurrence.SecondOrderDegree
import RealRooted.GeneralizedLiuWang
import RealRooted.WagnerRightSum

/-!
# Interlacing for affine-lagged second-order derivative recurrences

Coefficient positivity, strict root negativity, and proper position for the
second-order recurrence shared by several OEIS polynomial families.
-/

open Polynomial

noncomputable section

namespace RealRooted

variable {P : ℕ → ℝ[X]} {a : ℝ}

/-- Every polynomial in the recurrence has constant coefficient one. -/
theorem coeff_zero_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) :
    ∀ n : ℕ, coeff (P n) 0 = 1
  | 0 => by rw [h0]; simp
  | 1 => by rw [h1]; simp
  | n + 2 => by
      have ih := coeff_zero_affine_lag_second_order_derivative h0 h1 hrec (n + 1)
      rw [hrec n]
      rw [show (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative =
          C a * (X * (P (n + 1)).derivative) +
            C (-a) * (X ^ 2 * (P (n + 1)).derivative) by ring]
      rw [show (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) =
          P (n + 1) + C ((a + 1) + a * (n : ℝ)) * (X * P (n + 1)) by
            rw [map_one]
            ring]
      rw [show (C a * X) * P n = C a * (X * P n) by ring]
      simp only [coeff_add, coeff_C_mul]
      norm_num
      exact ih

private theorem nonneg_coeffs_affine_lag_second_order_derivative_aux
    (ha : 0 < a) (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n)
    (habove : ∀ n k, n < k → coeff (P n) k = 0) :
    ∀ n k, 0 ≤ coeff (P n) k
  | 0, k => by
      rw [h0, coeff_one]
      split_ifs <;> norm_num
  | 1, k => by
      rw [h1, coeff_add, coeff_one, coeff_X]
      split_ifs <;> norm_num
  | n + 2, k => by
      have hnn1 := nonneg_coeffs_affine_lag_second_order_derivative_aux
        ha h0 h1 hrec habove (n + 1)
      have hnn0 := nonneg_coeffs_affine_lag_second_order_derivative_aux
        ha h0 h1 hrec habove n
      have hcoeff : ∀ j : ℕ, coeff (P (n + 2)) (j + 1) =
          (a * ((j : ℝ) + 1) + 1) * coeff (P (n + 1)) (j + 1) +
            (((a + 1) + a * (n : ℝ)) - a * (j : ℝ)) * coeff (P (n + 1)) j +
              a * coeff (P n) j := fun j =>
        second_order_derivative_coeff_succ_succ P a a
          (fun m => (a + 1) + a * (m : ℝ)) hrec n j
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [coeff_zero_affine_lag_second_order_derivative h0 h1 hrec (n + 2)]
        norm_num
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
        rw [hcoeff j]
        have hfirst :
            0 ≤ (a * ((j : ℝ) + 1) + 1) * coeff (P (n + 1)) (j + 1) := by
          exact mul_nonneg (by positivity) (hnn1 (j + 1))
        have hlast : 0 ≤ a * coeff (P n) j := mul_nonneg ha.le (hnn0 j)
        have hmiddle :
            0 ≤ (((a + 1) + a * (n : ℝ)) - a * (j : ℝ)) *
              coeff (P (n + 1)) j := by
          by_cases hj : n + 1 < j
          · rw [habove (n + 1) j hj]
            simp
          · have hjle : (j : ℝ) ≤ (n : ℝ) + 1 := by
              exact_mod_cast (by lia : j ≤ n + 1)
            exact mul_nonneg (by nlinarith) (hnn1 j)
        linarith

private theorem top_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) (n : ℕ) :
    0 < coeff (P n) n ∧ ∀ m > n, coeff (P n) m = 0 := by
  exact second_order_derivative_top_and_above P a a
    (fun m => (a + 1) + a * (m : ℝ)) h0 h1 hrec (by intro m; ring) n

/-- Every polynomial in the recurrence has nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_affine_lag_second_order_derivative
    (P : ℕ → ℝ[X]) (a : ℝ) (ha : 0 < a)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) :
    ∀ n, HasNonnegCoeffs (P n) := fun n =>
  nonneg_coeffs_affine_lag_second_order_derivative_aux ha h0 h1 hrec
    (fun m k hmk => (top_affine_lag_second_order_derivative h0 h1 hrec m).2 k hmk) n

private theorem natDegree_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) (n : ℕ) :
    (P n).natDegree = n := by
  exact natDegree_of_second_order_derivative P a a
    (fun m => (a + 1) + a * (m : ℝ)) h0 h1 hrec (by intro m; ring) n

private theorem pos_leading_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_affine_lag_second_order_derivative h0 h1 hrec n]
  exact (top_affine_lag_second_order_derivative h0 h1 hrec n).1

private theorem root_neg_affine_lag_second_order_derivative
    (ha : 0 < a) (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) (n : ℕ) {r : ℝ} (hr : (P n).IsRoot r) :
    r < 0 := by
  have hpos := pos_leading_affine_lag_second_order_derivative h0 h1 hrec n
  have hnonneg : HasNonnegCoeffs (P n) :=
    hasNonnegCoeffs_of_affine_lag_second_order_derivative P a ha h0 h1 hrec n
  have hmem : r ∈ (P n).roots := by
    rw [mem_roots hpos.ne_zero]
    exact hr
  have hle : r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hnonneg r hmem
  rcases lt_or_eq_of_le hle with hlt | rfl
  · exact hlt
  · exfalso
    have heval : eval 0 (P n) = 1 := by
      rw [← coeff_zero_eq_eval_zero,
        coeff_zero_affine_lag_second_order_derivative h0 h1 hrec]
    rw [Polynomial.IsRoot.def, heval] at hr
    norm_num at hr

private theorem derivative_interlaces_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) (n : ℕ) (hs : (P (n + 1)).Splits) :
    Interlaces ((P (n + 1)).derivative) (P (n + 1)) := by
  have hpos := pos_leading_affine_lag_second_order_derivative h0 h1 hrec (n + 1)
  exact interlaces_derivative_of_pos_natDegree hpos.ne_zero hs hpos (by
    rw [natDegree_affine_lag_second_order_derivative h0 h1 hrec]
    lia)

private theorem derivative_pos_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) (n : ℕ) :
    HasPosLeadingCoeff ((P (n + 1)).derivative) :=
  (pos_leading_affine_lag_second_order_derivative h0 h1 hrec (n + 1)).derivative (by
    rw [natDegree_affine_lag_second_order_derivative h0 h1 hrec]
    lia)

/-- Adjacent members of an affine-lagged second-order derivative recurrence
are in proper position and have no common real root. -/
theorem prec_and_noCommonRoot_of_affine_lag_second_order_derivative
    (P : ℕ → ℝ[X]) (a : ℝ) (ha : 0 < a)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C a * X) * P n) :
    ∀ n, Prec (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  intro n
  induction n with
  | zero =>
      constructor
      · rw [h0]
        exact (interlaces_one_linear (by
          rw [natDegree_affine_lag_second_order_derivative h0 h1 hrec])).toPrec
      · intro r _ hr0
        rw [Polynomial.IsRoot.def, h0] at hr0
        simp at hr0
  | succ n ih =>
      obtain ⟨ihprec, ihno⟩ := ih
      have hinter : Interlaces (P n) (P (n + 1)) :=
        ihprec.toInterlaces (by
          rw [natDegree_affine_lag_second_order_derivative h0 h1 hrec,
            natDegree_affine_lag_second_order_derivative h0 h1 hrec])
      have hderiv_inter : Interlaces ((P (n + 1)).derivative) (P (n + 1)) :=
        derivative_interlaces_affine_lag_second_order_derivative h0 h1 hrec n ihprec.2.1.2
      have hderiv_pos : HasPosLeadingCoeff ((P (n + 1)).derivative) :=
        derivative_pos_affine_lag_second_order_derivative h0 h1 hrec n
      have hV : ∀ r : ℝ, (P (n + 1)).IsRoot r →
          eval r (C a * X + C (-a) * X ^ 2) ≤ 0 := by
        intro r hr
        have hneg := root_neg_affine_lag_second_order_derivative ha h0 h1 hrec (n + 1) hr
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
        nlinarith [sq_nonneg r]
      have hW : ∀ r : ℝ, (P (n + 1)).IsRoot r → eval r (C a * X) ≤ 0 := by
        intro r hr
        have hneg := root_neg_affine_lag_second_order_derivative ha h0 h1 hrec (n + 1) hr
        simp only [eval_mul, eval_C, eval_X]
        nlinarith
      have hsum : P (n + 2) =
          (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
            polynomialWeightedSum
              ((C a * X, P n) ::
                [(C a * X + C (-a) * X ^ 2, (P (n + 1)).derivative)]) := by
        rw [hrec n]
        simp only [polynomialWeightedSum]
        ring
      have hprec : Prec (P (n + 1)) (P (n + 2)) := by
        rw [hsum]
        refine prec_generalizedLiuWang_of_no_common
          hinter (pos_leading_affine_lag_second_order_derivative h0 h1 hrec n)
            ?_ ?_ ?_ ?_ ?_ ?_ ihno hW
        · intro bg hmem
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hderiv_inter
        · intro bg hmem
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hderiv_pos
        · intro bg hmem r hr
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hV r hr
        · rw [← hsum]
          exact pos_leading_affine_lag_second_order_derivative h0 h1 hrec (n + 2)
        · rw [← hsum,
            natDegree_affine_lag_second_order_derivative h0 h1 hrec,
            natDegree_affine_lag_second_order_derivative h0 h1 hrec]
          lia
        · rw [← hsum,
            natDegree_affine_lag_second_order_derivative h0 h1 hrec,
            natDegree_affine_lag_second_order_derivative h0 h1 hrec]
      refine ⟨hprec, ?_⟩
      intro r hr2 hr1
      have hrneg : r < 0 :=
        root_neg_affine_lag_second_order_derivative ha h0 h1 hrec (n + 1) hr1
      have hkey : (1 - r) * eval r ((P (n + 1)).derivative) + eval r (P n) = 0 := by
        have h := hr2
        rw [Polynomial.IsRoot.def, hrec n] at h
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at h
        rw [Polynomial.IsRoot.def] at hr1
        rw [hr1] at h
        have hr0 : r ≠ 0 := ne_of_lt hrneg
        have hfactor :
            2 * a * r * ((1 - r) * eval r ((P (n + 1)).derivative) +
              eval r (P n)) = 0 := by
          nlinarith [h]
        rcases mul_eq_zero.mp hfactor with hzero | hzero
        · exfalso
          rcases mul_eq_zero.mp hzero with htwo | hzero
          · exact ha.ne' (by nlinarith [htwo])
          · exact hr0 hzero
        · exact hzero
      have hne : eval r (P n) ≠ 0 := fun hroot => ihno r hr1 hroot
      have hsign : 0 ≤ eval r (P n) * eval r ((P (n + 1)).derivative) :=
        eval_mul_eval_nonneg_of_prec_right ihprec hderiv_inter.toPrec
          (pos_leading_affine_lag_second_order_derivative h0 h1 hrec n) hderiv_pos hr1
      have hsquare : 0 < (eval r (P n)) ^ 2 := by positivity
      have hmul :
          0 ≤ (1 - r) * (eval r (P n) * eval r ((P (n + 1)).derivative)) :=
        mul_nonneg (by linarith) hsign
      have hreassoc :
          (1 - r) * (eval r (P n) * eval r ((P (n + 1)).derivative)) =
            eval r (P n) * ((1 - r) * eval r ((P (n + 1)).derivative)) := by
        ring
      have hderiv_value :
          (1 - r) * eval r ((P (n + 1)).derivative) = -eval r (P n) := by
        linarith
      rw [hreassoc, hderiv_value] at hmul
      nlinarith

end RealRooted
