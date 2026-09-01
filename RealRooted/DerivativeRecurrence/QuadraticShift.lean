import RealRooted.DerivativeRecurrence.QuadraticDegree
import RealRooted.MaWang

/-!
# Shifted quadratic-coefficient derivative recurrences

Nonnegative-coefficient and proper-position results for the normalized shifted recurrence.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma quadratic_derivative_shift_coeff_zero_succ
    (P : ℕ → ℝ[X]) (s : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (n : ℕ) :
    Polynomial.coeff (P (n + 1)) 0 = Polynomial.coeff (P n) 0 := by simp_all

lemma hasNonnegCoeffs_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) :
    ∀ n : ℕ, HasNonnegCoeffs (P n)
  | 0 => by
      intro m
      rw [h0]
      rcases m with _ | m <;> simp [coeff_one]
  | n + 1 => by
      rintro (_ | m)
      · rw [quadratic_derivative_shift_coeff_zero_succ P s hrec]
        exact hasNonnegCoeffs_of_quadratic_derivative_shift P s h0 hrec hs n 0
      · rw [quadratic_derivative_shift_coeff_succ P s hrec]
        refine add_nonneg (mul_nonneg (by positivity)
          (hasNonnegCoeffs_of_quadratic_derivative_shift P s h0 hrec hs n (m + 1))) ?_
        rcases quadratic_derivative_shift_top_and_above P s h0 hrec hs n with ⟨_, habove⟩
        by_cases hmn : m ≤ n
        · exact mul_nonneg (by nlinarith [hs, Nat.cast_nonneg (α := ℝ) n,
            (Nat.cast_le (α := ℝ)).mpr hmn])
            (hasNonnegCoeffs_of_quadratic_derivative_shift P s h0 hrec hs n m)
        · simp_all

lemma hasPosLeadingCoeff_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
  exact (quadratic_derivative_shift_top_and_above P s h0 hrec hs n).1

lemma quadratic_derivative_shift_v_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (C (1) * X + C (-1) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hv : (C (1) * X + C (-1) * X ^ 2 : ℝ[X]).eval r = r - r ^ 2 := by
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  rw [hv]
  nlinarith [sq_nonneg r]

lemma prec_step_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) (m : ℕ) (hm : 2 ≤ m) (hsp : (P m).Splits) :
    Prec (P m) (P (m + 1)) := by
  have hne : P m ≠ 0 := ne_zero_of_quadratic_derivative_shift P s h0 hrec hs m
  have hroots_nonpos : ∀ r, (P m).IsRoot r → r ≤ 0 := fun r hr =>
    roots_nonpos_of_hasNonnegCoeffs (hasNonnegCoeffs_of_quadratic_derivative_shift P s h0 hrec hs m)
      r ((mem_roots hne).mpr hr)
  have hInter : Interlaces (P m).derivative (P m) :=
    derivative_interlaces hsp (by
      rw [natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
      assumption)
  have hg_pos : HasPosLeadingCoeff (P m).derivative :=
    (hasPosLeadingCoeff_of_quadratic_derivative_shift P s h0 hrec hs m).derivative (by
      rw [natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
      lia)
  have hF_eq : (C 1 + C (s + (m : ℝ)) * X) * P m
      + (C (1) * X + C (-1) * X ^ 2) * (P m).derivative = P (m + 1) := by grind
  have hF_pos :
      HasPosLeadingCoeff ((C 1 + C (s + (m : ℝ)) * X) * P m
        + (C (1) * X + C (-1) * X ^ 2) * (P m).derivative) := by
    rw [hF_eq]
    exact hasPosLeadingCoeff_of_quadratic_derivative_shift P s h0 hrec hs (m + 1)
  have hdeg_lo :
      (P m).natDegree ≤ ((C 1 + C (s + (m : ℝ)) * X) * P m
        + (C (1) * X + C (-1) * X ^ 2) * (P m).derivative).natDegree := by
    rw [hF_eq, natDegree_of_quadratic_derivative_shift P s h0 hrec hs,
      natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
    lia
  have hdeg_hi :
      ((C 1 + C (s + (m : ℝ)) * X) * P m
        + (C (1) * X + C (-1) * X ^ 2) * (P m).derivative).natDegree ≤
        (P m).natDegree + 1 := by
    rw [hF_eq, natDegree_of_quadratic_derivative_shift P s h0 hrec hs,
      natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
  have hb_nonpos : ∀ r, (P m).IsRoot r →
      (C (1) * X + C (-1) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    exact quadratic_derivative_shift_v_nonpos_of_nonpos (hroots_nonpos r hr)
  have := prec_of_interlaces_evalCoeff_nonpos
    (f := P m) (g := (P m).derivative)
    (a := C 1 + C (s + (m : ℝ)) * X) (b := C (1) * X + C (-1) * X ^ 2)
    hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simp_all


theorem prec_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) :
    ∀ n : ℕ, Prec (P n) (P (n + 1))
  | 0 => by
      have : Interlaces (P 0) (P 1) := by
        rw [h0]
        exact interlaces_one_linear (p := P 1)
          (by rw [natDegree_of_quadratic_derivative_shift P s h0 hrec hs])
      exact this.toPrec
  | 1 => by
      have hp1 : P 1 = 1 + C s * X := by
        simp_all
      have hder : (P 1).derivative = C s := by simp_all
      have hInter : Interlaces (P 1).derivative (P 1) := by
        rw [hder]
        exact interlaces_C_linear (c := s) hs.ne'
          (p := P 1) (by rw [natDegree_of_quadratic_derivative_shift P s h0 hrec hs])
      have hg_pos : HasPosLeadingCoeff (P 1).derivative := by
        rw [hder]
        simpa [HasPosLeadingCoeff, leadingCoeff] using hs
      have hF_eq : (C 1 + C (s + ((1 : ℕ) : ℝ)) * X) * P 1
          + (C (1) * X + C (-1) * X ^ 2) * (P 1).derivative = P 2 := by grind
      have hF_pos :
          HasPosLeadingCoeff ((C 1 + C (s + ((1 : ℕ) : ℝ)) * X) * P 1
            + (C (1) * X + C (-1) * X ^ 2) * (P 1).derivative) := by
        rw [hF_eq]
        exact hasPosLeadingCoeff_of_quadratic_derivative_shift P s h0 hrec hs 2
      have hdeg_lo :
          (P 1).natDegree ≤
            ((C 1 + C (s + ((1 : ℕ) : ℝ)) * X) * P 1
              + (C (1) * X + C (-1) * X ^ 2) * (P 1).derivative).natDegree := by
        rw [hF_eq, natDegree_of_quadratic_derivative_shift P s h0 hrec hs,
          natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
        lia
      have hdeg_hi :
          ((C 1 + C (s + ((1 : ℕ) : ℝ)) * X) * P 1
            + (C (1) * X + C (-1) * X ^ 2) * (P 1).derivative).natDegree ≤
            (P 1).natDegree + 1 := by
        rw [hF_eq, natDegree_of_quadratic_derivative_shift P s h0 hrec hs,
          natDegree_of_quadratic_derivative_shift P s h0 hrec hs]
      have hne : P 1 ≠ 0 := ne_zero_of_quadratic_derivative_shift P s h0 hrec hs 1
      have hb_nonpos : ∀ r, (P 1).IsRoot r →
          (C (1) * X + C (-1) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
        intro r hr
        have := roots_nonpos_of_hasNonnegCoeffs
          (hasNonnegCoeffs_of_quadratic_derivative_shift P s h0 hrec hs 1)
          r ((mem_roots hne).mpr hr)
        exact quadratic_derivative_shift_v_nonpos_of_nonpos this
      have := prec_of_interlaces_evalCoeff_nonpos
        (f := P 1) (g := (P 1).derivative)
        (a := C 1 + C (s + ((1 : ℕ) : ℝ)) * X) (b := C (1) * X + C (-1) * X ^ 2)
        hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
      simp_all
  | n + 2 =>
      prec_step_of_quadratic_derivative_shift P s h0 hrec hs (n + 2) (by lia)
        (prec_of_quadratic_derivative_shift P s h0 hrec hs (n + 1)).2.1.2


end RealRooted
