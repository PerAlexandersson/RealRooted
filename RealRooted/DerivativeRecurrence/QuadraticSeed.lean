import RealRooted.DerivativeRecurrence.QuadraticInterlacing

/-!
# Quadratic-seed derivative recurrences

Degree and proper-position adapters for recurrences beginning with a quadratic seed.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma prec_one_add_X_quadratic_of_two_le (u : ℝ) (hu : 2 ≤ u) :
    Prec (1 + X : ℝ[X]) (1 + X * C u + X ^ 2) := by
  have hInter : Interlaces (1 : ℝ[X]) (1 + X) :=
    interlaces_one_linear (p := 1 + X) (by compute_degree!)
  have hg_pos : HasPosLeadingCoeff (1 : ℝ[X]) := by
    norm_num [HasPosLeadingCoeff, leadingCoeff]
  have hF_eq :
      (1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X]) =
        1 + X * C u + X ^ 2 := by
    apply Polynomial.funext
    intro r
    simp only [eval_add, eval_mul, eval_one, eval_X, eval_C, eval_pow]
    ring
  have hF_pos :
      HasPosLeadingCoeff ((1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X])) := by
    rw [hF_eq]
    rw [HasPosLeadingCoeff, leadingCoeff,
      show (1 + X * C u + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
    norm_num [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_one]
  have hdeg_lo :
      (1 + X : ℝ[X]).natDegree ≤
        ((1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X])).natDegree := by
    rw [hF_eq]
    norm_num [show (1 + X : ℝ[X]).natDegree = 1 by compute_degree!,
      show (1 + C u * X + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
  have hdeg_hi :
      ((1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X])).natDegree ≤
        (1 + X : ℝ[X]).natDegree + 1 := by
    rw [hF_eq]
    norm_num [show (1 + X : ℝ[X]).natDegree = 1 by compute_degree!,
      show (1 + C u * X + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
  have hb_nonpos : ∀ r, (1 + X : ℝ[X]).IsRoot r →
      (C (u - 2) * X : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    have hr' : r = -1 := by
      change (1 + X : ℝ[X]).eval r = 0 at hr
      simp only [eval_add, eval_one, eval_X] at hr
      grind
    simp_all
  have := prec_of_interlaces_evalCoeff_nonpos
    (f := (1 + X : ℝ[X])) (g := (1 : ℝ[X]))
    (a := 1 + X) (b := C (u - 2) * X)
    hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simp_all

theorem natDegree_of_quadratic_derivative_linear_quadratic_seed
    (P : ℕ → ℝ[X]) (u a b c s t : ℝ)
    (h0 : P 0 = 1)
    (h1 : P 1 = 1 + X)
    (h2 : P 2 = 1 + X * C u + X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      (C a * X + C (-b) * X ^ 2) * (P (n + 2)).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P (n + 2))
    (hsd : 0 < s - b * (2 : ℝ)) (hbt : b ≤ t) :
    ∀ n : ℕ, (P n).natDegree = n
  | 0 => by
      simp_all
  | 1 => by
      rw [h1]
      compute_degree!
  | n + 2 => by
      have hbase_top : 0 < Polynomial.coeff ((fun m => P (m + 2)) 0) 2 := by
        change 0 < Polynomial.coeff (P 2) 2
        rw [h2]
        norm_num [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_one]
      have hbase_above : ∀ m > 2, Polynomial.coeff ((fun m => P (m + 2)) 0) m = 0 := by
        intro m hm
        change Polynomial.coeff (P 2) m = 0
        rw [h2]
        apply coeff_eq_zero_of_natDegree_lt
        rw [show (1 + X * C u + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
        assumption
      have hrecQ : ∀ n, (fun m ↦ P (m + 2)) (n + 1) =
          (C a * X + C (-b) * X ^ 2) * ((fun m ↦ P (m + 2)) n).derivative +
            (C c + C (s + t * (n : ℝ)) * X) * (fun m ↦ P (m + 2)) n := by assumption
      exact natDegree_of_quadratic_derivative_linear_offset
        (fun m ↦ P (m + 2)) a b c s t 2
        hbase_top hbase_above hrecQ hsd hbt n

theorem prec_of_quadratic_derivative_linear_quadratic_seed
    (P : ℕ → ℝ[X]) (u a b c s t : ℝ)
    (h0 : P 0 = 1)
    (h1 : P 1 = 1 + X)
    (h2 : P 2 = 1 + X * C u + X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      (C a * X + C (-b) * X ^ 2) * (P (n + 2)).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P (n + 2))
    (hu : 2 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsd : 0 < s - b * (2 : ℝ)) (hbt : b ≤ t) :
    ∀ n : ℕ, Prec (P n) (P (n + 1))
  | 0 => by
      have hInter : Interlaces (P 0) (P 1) := by
        rw [h0, h1]
        exact interlaces_one_linear (p := 1 + X) (by compute_degree!)
      exact hInter.toPrec
  | 1 => by
      rw [h1, h2]
      exact prec_one_add_X_quadratic_of_two_le u hu
  | n + 2 => by
      have hbase_nonneg : HasNonnegCoeffs ((fun m => P (m + 2)) 0) := by
        change HasNonnegCoeffs (P 2)
        rw [h2]
        rw [show (1 + X * C u + X ^ 2 : ℝ[X]) = 1 + C u * X + X ^ 2 by
          simp]
        exact (hasNonnegCoeffs_one.add
          ((hasNonnegCoeffs_C (by nlinarith : 0 ≤ u)).mul hasNonnegCoeffs_X)).add
          (hasNonnegCoeffs_X.pow 2)
      have hbase_top : 0 < Polynomial.coeff ((fun m => P (m + 2)) 0) 2 := by
        change 0 < Polynomial.coeff (P 2) 2
        rw [h2]
        norm_num [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_one]
      have hbase_above : ∀ m > 2, Polynomial.coeff ((fun m => P (m + 2)) 0) m = 0 := by
        intro m hm
        change Polynomial.coeff (P 2) m = 0
        rw [h2]
        apply coeff_eq_zero_of_natDegree_lt
        rw [show (1 + X * C u + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
        assumption
      have hbase_splits : (((fun m ↦ P (m + 2)) 0)).Splits := by
        change (P 2).Splits
        rw [h2]
        exact (prec_one_add_X_quadratic_of_two_le u hu).2.1.2
      have hrecQ : ∀ n, (fun m ↦ P (m + 2)) (n + 1) =
          (C a * X + C (-b) * X ^ 2) * ((fun m ↦ P (m + 2)) n).derivative +
            (C c + C (s + t * (n : ℝ)) * X) * (fun m ↦ P (m + 2)) n := by assumption
      exact prec_of_quadratic_derivative_linear_offset
        (fun m ↦ P (m + 2)) a b c s t 2
        hbase_nonneg hbase_top hbase_above hbase_splits hrecQ
        ha hb hc hsd hbt (by norm_num) n


end RealRooted
