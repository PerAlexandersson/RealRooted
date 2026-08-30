import RealRooted.DerivativeRecurrence.QuadraticDegree
import RealRooted.MaWang

/-!
# Interlacing for quadratic-coefficient derivative recurrences

Nonnegative-coefficient and proper-position results for the general
linear-multiplier recurrence, including degree offsets.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma quadratic_derivative_linear_coeff_zero_succ
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (n : ℕ) :
    Polynomial.coeff (P (n + 1)) 0 = c * Polynomial.coeff (P n) 0 := by simp_all

lemma hasNonnegCoeffs_of_quadratic_derivative_linear
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < s) (hbt : b ≤ t) :
    ∀ n : ℕ, HasNonnegCoeffs (P n)
  | 0 => by
      intro m
      rw [h0]
      rcases m with _ | m <;> simp [coeff_one]
  | n + 1 => by
      rintro (_ | m)
      · rw [quadratic_derivative_linear_coeff_zero_succ P a b c s t hrec]
        exact mul_nonneg hc
          (hasNonnegCoeffs_of_quadratic_derivative_linear P a b c s t h0 hrec
            ha hb hc hs hbt n 0)
      · rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        refine add_nonneg
          (mul_nonneg (by nlinarith [ha, hc, Nat.cast_nonneg (α := ℝ) m])
            (hasNonnegCoeffs_of_quadratic_derivative_linear P a b c s t h0 hrec
              ha hb hc hs hbt n (m + 1))) ?_
        rcases quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n with
          ⟨_, habove⟩
        by_cases hmn : m ≤ n
        · exact mul_nonneg (by
            have hn : 0 ≤ (n : ℝ) := by simp
            have hmn' : (m : ℝ) ≤ (n : ℝ) := by simp_all
            nlinarith [hs, hb, hbt, hn, hmn'])
            (hasNonnegCoeffs_of_quadratic_derivative_linear P a b c s t h0 hrec
              ha hb hc hs hbt n m)
        · simp_all

lemma hasPosLeadingCoeff_of_quadratic_derivative_linear
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  rw [HasPosLeadingCoeff, leadingCoeff,
    natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
  exact (quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n).1

lemma quadratic_derivative_linear_v_nonpos_of_nonpos
    {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r ≤ 0) :
    (C a * X + C (-b) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hv : (C a * X + C (-b) * X ^ 2 : ℝ[X]).eval r = a * r - b * r ^ 2 := by
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  rw [hv]
  nlinarith [mul_nonneg ha (neg_nonneg.mpr hr), mul_nonneg hb (sq_nonneg r)]

lemma prec_step_of_quadratic_derivative_linear
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < s) (hbt : b ≤ t)
    (m : ℕ) (hm : 2 ≤ m) (hsp : (P m).Splits) :
    Prec (P m) (P (m + 1)) := by
  have hne : P m ≠ 0 := ne_zero_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt m
  have hroots_nonpos : ∀ r, (P m).IsRoot r → r ≤ 0 := fun r hr =>
    roots_nonpos_of_hasNonnegCoeffs
      (hasNonnegCoeffs_of_quadratic_derivative_linear P a b c s t h0 hrec
        ha hb hc hs hbt m) r ((mem_roots hne).mpr hr)
  have hInter : Interlaces (P m).derivative (P m) :=
    derivative_interlaces hsp (by
      rw [natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
      assumption)
  have hg_pos : HasPosLeadingCoeff (P m).derivative :=
    (hasPosLeadingCoeff_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt m).derivative (by
      rw [natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
      lia)
  have hF_eq : (C c + C (s + t * (m : ℝ)) * X) * P m
      + (C a * X + C (-b) * X ^ 2) * (P m).derivative = P (m + 1) := by grind
  have hF_pos :
      HasPosLeadingCoeff ((C c + C (s + t * (m : ℝ)) * X) * P m
        + (C a * X + C (-b) * X ^ 2) * (P m).derivative) := by
    rw [hF_eq]
    exact hasPosLeadingCoeff_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt (m + 1)
  have hdeg_lo :
      (P m).natDegree ≤ ((C c + C (s + t * (m : ℝ)) * X) * P m
        + (C a * X + C (-b) * X ^ 2) * (P m).derivative).natDegree := by
    rw [hF_eq, natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt,
      natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
    lia
  have hdeg_hi :
      ((C c + C (s + t * (m : ℝ)) * X) * P m
        + (C a * X + C (-b) * X ^ 2) * (P m).derivative).natDegree ≤
        (P m).natDegree + 1 := by
    rw [hF_eq, natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt,
      natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
  have hb_nonpos : ∀ r, (P m).IsRoot r →
      (C a * X + C (-b) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    exact quadratic_derivative_linear_v_nonpos_of_nonpos ha hb (hroots_nonpos r hr)
  have := prec_of_interlaces_evalCoeff_nonpos
    (f := P m) (g := (P m).derivative)
    (a := C c + C (s + t * (m : ℝ)) * X) (b := C a * X + C (-b) * X ^ 2)
    hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simp_all

theorem prec_of_quadratic_derivative_linear
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < s) (hbt : b ≤ t) :
    ∀ n : ℕ, Prec (P n) (P (n + 1))
  | 0 => by
      have : Interlaces (P 0) (P 1) := by
        rw [h0]
        exact interlaces_one_linear (p := P 1)
          (by rw [natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt])
      exact this.toPrec
  | 1 => by
      have hp1 : P 1 = C c + C s * X := by
        simp_all
      have hder : (P 1).derivative = C s := by simp_all
      have hInter : Interlaces (P 1).derivative (P 1) := by
        rw [hder]
        exact interlaces_C_linear (c := s) hs.ne'
          (p := P 1) (by rw [natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt])
      have hg_pos : HasPosLeadingCoeff (P 1).derivative := by
        rw [hder]
        simpa [HasPosLeadingCoeff, leadingCoeff] using hs
      have hF_eq : (C c + C (s + t * ((1 : ℕ) : ℝ)) * X) * P 1
          + (C a * X + C (-b) * X ^ 2) * (P 1).derivative = P 2 := by grind
      have hF_pos :
          HasPosLeadingCoeff ((C c + C (s + t * ((1 : ℕ) : ℝ)) * X) * P 1
            + (C a * X + C (-b) * X ^ 2) * (P 1).derivative) := by
        rw [hF_eq]
        exact hasPosLeadingCoeff_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt 2
      have hdeg_lo :
          (P 1).natDegree ≤
            ((C c + C (s + t * ((1 : ℕ) : ℝ)) * X) * P 1
              + (C a * X + C (-b) * X ^ 2) * (P 1).derivative).natDegree := by
        rw [hF_eq, natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt,
          natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
        lia
      have hdeg_hi :
          ((C c + C (s + t * ((1 : ℕ) : ℝ)) * X) * P 1
            + (C a * X + C (-b) * X ^ 2) * (P 1).derivative).natDegree ≤
            (P 1).natDegree + 1 := by
        rw [hF_eq, natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt,
          natDegree_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt]
      have hne : P 1 ≠ 0 := ne_zero_of_quadratic_derivative_linear P a b c s t h0 hrec hs hbt 1
      have hb_nonpos : ∀ r, (P 1).IsRoot r →
          (C a * X + C (-b) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
        intro r hr
        have := roots_nonpos_of_hasNonnegCoeffs
          (hasNonnegCoeffs_of_quadratic_derivative_linear P a b c s t h0 hrec
            ha hb hc hs hbt 1) r ((mem_roots hne).mpr hr)
        exact quadratic_derivative_linear_v_nonpos_of_nonpos ha hb this
      have := prec_of_interlaces_evalCoeff_nonpos
        (f := P 1) (g := (P 1).derivative)
        (a := C c + C (s + t * ((1 : ℕ) : ℝ)) * X) (b := C a * X + C (-b) * X ^ 2)
        hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
      simp_all
  | n + 2 =>
      prec_step_of_quadratic_derivative_linear P a b c s t h0 hrec
        ha hb hc hs hbt (n + 2) (by lia)
        (prec_of_quadratic_derivative_linear P a b c s t h0 hrec
          ha hb hc hs hbt (n + 1)).2.1.2

lemma hasNonnegCoeffs_of_quadratic_derivative_linear_offset
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_nonneg : HasNonnegCoeffs (P 0))
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsd : 0 < s - b * (d : ℝ))
    (hbt : b ≤ t) :
    ∀ n : ℕ, HasNonnegCoeffs (P n)
  | 0 => hbase_nonneg
  | n + 1 => by
      rintro (_ | m)
      · rw [quadratic_derivative_linear_coeff_zero_succ P a b c s t hrec]
        exact mul_nonneg hc
          (hasNonnegCoeffs_of_quadratic_derivative_linear_offset P a b c s t d
            hbase_nonneg hbase_top hbase_above hrec ha hb hc hsd hbt n 0)
      · rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        refine add_nonneg
          (mul_nonneg (by nlinarith [ha, hc, Nat.cast_nonneg (α := ℝ) m])
            (hasNonnegCoeffs_of_quadratic_derivative_linear_offset P a b c s t d
              hbase_nonneg hbase_top hbase_above hrec ha hb hc hsd hbt n (m + 1))) ?_
        rcases quadratic_derivative_linear_offset_top_and_above P a b c s t d
          hbase_top hbase_above hrec hsd hbt n with ⟨_, habove⟩
        by_cases hmn : m ≤ n + d
        · exact mul_nonneg (by
            have hn : 0 ≤ (n : ℝ) := by simp
            have hmn' : (m : ℝ) ≤ (n : ℝ) + (d : ℝ) := by
              have hcast : ((n + d : ℕ) : ℝ) = (n : ℝ) + (d : ℝ) := by norm_num
              rw [← hcast]
              exact_mod_cast hmn
            nlinarith [hsd, hb, hbt, hn, hmn'])
            (hasNonnegCoeffs_of_quadratic_derivative_linear_offset P a b c s t d
              hbase_nonneg hbase_top hbase_above hrec ha hb hc hsd hbt n m)
        · simp_all

lemma hasPosLeadingCoeff_of_quadratic_derivative_linear_offset
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hsd : 0 < s - b * (d : ℝ)) (hbt : b ≤ t) (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  rw [HasPosLeadingCoeff, leadingCoeff,
    natDegree_of_quadratic_derivative_linear_offset P a b c s t d
      hbase_top hbase_above hrec hsd hbt]
  exact (quadratic_derivative_linear_offset_top_and_above P a b c s t d
    hbase_top hbase_above hrec hsd hbt n).1

lemma prec_step_of_quadratic_derivative_linear_offset
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_nonneg : HasNonnegCoeffs (P 0))
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsd : 0 < s - b * (d : ℝ))
    (hbt : b ≤ t) (hd : 2 ≤ d) (m : ℕ) (hsp : (P m).Splits) :
    Prec (P m) (P (m + 1)) := by
  have hne : P m ≠ 0 := ne_zero_of_quadratic_derivative_linear_offset P a b c s t d
    hbase_top hbase_above hrec hsd hbt m
  have hroots_nonpos : ∀ r, (P m).IsRoot r → r ≤ 0 := fun r hr =>
    roots_nonpos_of_hasNonnegCoeffs
      (hasNonnegCoeffs_of_quadratic_derivative_linear_offset P a b c s t d
        hbase_nonneg hbase_top hbase_above hrec ha hb hc hsd hbt m)
      r ((mem_roots hne).mpr hr)
  have hInter : Interlaces (P m).derivative (P m) :=
    derivative_interlaces hsp (by
      rw [natDegree_of_quadratic_derivative_linear_offset P a b c s t d
        hbase_top hbase_above hrec hsd hbt]
      lia)
  have hg_pos : HasPosLeadingCoeff (P m).derivative :=
    (hasPosLeadingCoeff_of_quadratic_derivative_linear_offset P a b c s t d
      hbase_top hbase_above hrec hsd hbt m).derivative (by
        rw [natDegree_of_quadratic_derivative_linear_offset P a b c s t d
          hbase_top hbase_above hrec hsd hbt]
        lia)
  have hF_eq : (C c + C (s + t * (m : ℝ)) * X) * P m
      + (C a * X + C (-b) * X ^ 2) * (P m).derivative = P (m + 1) := by grind
  have hF_pos :
      HasPosLeadingCoeff ((C c + C (s + t * (m : ℝ)) * X) * P m
        + (C a * X + C (-b) * X ^ 2) * (P m).derivative) := by
    rw [hF_eq]
    exact hasPosLeadingCoeff_of_quadratic_derivative_linear_offset P a b c s t d
      hbase_top hbase_above hrec hsd hbt (m + 1)
  have hdeg_lo :
      (P m).natDegree ≤ ((C c + C (s + t * (m : ℝ)) * X) * P m
        + (C a * X + C (-b) * X ^ 2) * (P m).derivative).natDegree := by
    rw [hF_eq, natDegree_of_quadratic_derivative_linear_offset P a b c s t d
      hbase_top hbase_above hrec hsd hbt,
      natDegree_of_quadratic_derivative_linear_offset P a b c s t d
        hbase_top hbase_above hrec hsd hbt]
    lia
  have hdeg_hi :
      ((C c + C (s + t * (m : ℝ)) * X) * P m
        + (C a * X + C (-b) * X ^ 2) * (P m).derivative).natDegree ≤
        (P m).natDegree + 1 := by
    rw [hF_eq, natDegree_of_quadratic_derivative_linear_offset P a b c s t d
      hbase_top hbase_above hrec hsd hbt,
      natDegree_of_quadratic_derivative_linear_offset P a b c s t d
        hbase_top hbase_above hrec hsd hbt]
    lia
  have hb_nonpos : ∀ r, (P m).IsRoot r →
      (C a * X + C (-b) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    exact quadratic_derivative_linear_v_nonpos_of_nonpos ha hb (hroots_nonpos r hr)
  have := prec_of_interlaces_evalCoeff_nonpos
    (f := P m) (g := (P m).derivative)
    (a := C c + C (s + t * (m : ℝ)) * X) (b := C a * X + C (-b) * X ^ 2)
    hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simp_all

theorem prec_of_quadratic_derivative_linear_offset
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_nonneg : HasNonnegCoeffs (P 0))
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hbase_splits : (P 0).Splits)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsd : 0 < s - b * (d : ℝ))
    (hbt : b ≤ t) (hd : 2 ≤ d) :
    ∀ n : ℕ, Prec (P n) (P (n + 1))
  | 0 =>
      prec_step_of_quadratic_derivative_linear_offset P a b c s t d
        hbase_nonneg hbase_top hbase_above hrec ha hb hc hsd hbt hd 0 hbase_splits
  | n + 1 =>
      prec_step_of_quadratic_derivative_linear_offset P a b c s t d
        hbase_nonneg hbase_top hbase_above hrec ha hb hc hsd hbt hd (n + 1)
        (prec_of_quadratic_derivative_linear_offset P a b c s t d
          hbase_nonneg hbase_top hbase_above hbase_splits hrec
          ha hb hc hsd hbt hd n).2.1.2


end RealRooted
