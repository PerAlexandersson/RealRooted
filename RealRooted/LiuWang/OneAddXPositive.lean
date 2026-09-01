import Mathlib.Tactic.ComputeDegree
import RealRooted.LiuWang.SequenceProducts

/-!
# Positive one-plus-X recurrence sequences

Degree growth and consecutive interlacing for polynomial sequences satisfying
a positive three-term recurrence with current coefficient one plus X.

This sequence-independent theorem family was first used in the OEIS proof
project in ProofsOeis.OneAddXPositive.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem natDegree_of_one_add_X_positive_coeff
    (P : ℕ → ℝ[X]) (c : ℕ → ℝ) (a : ℝ)
    (h0 : P 0 = 1)
    (h1 : P 1 = 1 + C a * X)
    (hrec : ∀ n, P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n)
    (ha : a ≠ 0)
    (n : ℕ) :
    (P n).natDegree = n := by
  have hcoeff_succ (n k : ℕ) :
      Polynomial.coeff (P (n + 2)) (k + 1) =
        Polynomial.coeff (P (n + 1)) (k + 1)
          + Polynomial.coeff (P (n + 1)) k + c n * Polynomial.coeff (P n) k := by
    rw [hrec n]
    have hsplit :
        (1 + X) * P (n + 1) + (C (c n) * X) * P n =
          P (n + 1) + X * P (n + 1) + C (c n) * (X * P n) := by
      ring
    simp_all
  have habove : ∀ n N : ℕ, n < N → Polynomial.coeff (P n) N = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N hN
        match n with
        | 0 =>
            rw [h0, coeff_one]
            grind
        | 1 =>
            rcases N with _ | k
            · simp at hN
            · rcases k with _ | k
              · simp at hN
              · simp_all
        | k + 2 =>
            rcases N with _ | j
            · lia
            · rw [hcoeff_succ]
              grind
  have htop : ∀ n : ℕ, Polynomial.coeff (P n) n ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 =>
            simp_all
        | 1 =>
            rw [h1]
            change Polynomial.coeff (1 + C a * X) 1 ≠ 0
            rw [coeff_add, coeff_one, coeff_C_mul, coeff_X]
            grind
        | k + 2 =>
            simp_all
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun N hN ↦ habove n N hN))
    (htop n)

theorem interlaces_of_one_add_X_positive_coeff_with_base
    (P : ℕ → ℝ[X]) (c : ℕ → ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg : ∀ n, (P n).natDegree = n)
    (hc_pos : ∀ n, 0 < c n)
    (hbase : Prec (P 0) (P 1))
    (hbase_eval0 : (P 1).eval 0 = 1)
    (hbase_nn : HasNonnegCoeffs (P 1))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hnn_oneX : HasNonnegCoeffs (1 + X : ℝ[X]) :=
    hasNonnegCoeffs_one.add hasNonnegCoeffs_X
  have hinv : ∀ n, (P n).eval 0 = 1 ∧ HasNonnegCoeffs (P n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 =>
            rw [h0]
            exact ⟨by simp, hasNonnegCoeffs_one⟩
        | 1 =>
            simp_all
        | k + 2 =>
            obtain ⟨he, hnn⟩ := ih k (by lia)
            obtain ⟨he1, hnn1⟩ := ih (k + 1) (by lia)
            have hc_nn : HasNonnegCoeffs (C (c k) * X : ℝ[X]) :=
              (hasNonnegCoeffs_C (le_of_lt (hc_pos k))).mul hasNonnegCoeffs_X
            rw [hrec k]
            exact ⟨by simp [he, he1], (hnn_oneX.mul hnn1).add (hc_nn.mul hnn)⟩
  have heval0 (n : ℕ) : (P n).eval 0 = 1 := (hinv n).1
  have hnn (n : ℕ) : HasNonnegCoeffs (P n) := (hinv n).2
  have hpos (n : ℕ) : HasPosLeadingCoeff (P n) :=
    (hnn n).pos_leadingCoeff
      (by intro h; have := heval0 n; simp_all)
  have hdeg_succ (n : ℕ) : (P n).natDegree + 1 = (P (n + 1)).natDegree := by simp_all
  have hno : ∀ n, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
    intro n
    induction n with
    | zero =>
        simp_all
    | succ n ih =>
        intro r hr1 hr0
        have hev : (P (n + 2)).eval r =
            (1 + r) * (P (n + 1)).eval r + (c n * r) * (P n).eval r := by simp_all
        rw [IsRoot] at hr1 hr0
        rw [hr1, hr0] at hev
        have hprod : (c n * r) * (P n).eval r = 0 := by
          simpa only [mul_zero, zero_mul, zero_add] using Eq.symm hev
        rcases mul_eq_zero.mp hprod with hcr | hev0
        · rcases mul_eq_zero.mp hcr with hc | hr
          · exact ((ne_of_gt (hc_pos n)) hc).elim
          · rw [hr, heval0] at hr0
            norm_num at hr0
        · exact ih r (by rw [IsRoot]; exact hr0) (by rw [IsRoot]; exact hev0)
  exact (RealRooted.prec_lw_current_one_add_X_positive_t_lag_sequence
    (c := c) hbase hpos hnn (fun n => le_of_lt (hc_pos n)) hrec hdeg_succ hno n).toInterlaces
      (hdeg_succ n)

theorem interlaces_of_one_add_X_positive_coeff
    (P : ℕ → ℝ[X]) (c : ℕ → ℝ)
    (h0 : P 0 = 1)
    (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n)
    (hdeg : ∀ n, (P n).natDegree = n)
    (hc_pos : ∀ n, 0 < c n)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hbase : Prec (P 0) (P 1) := by
    rw [h0]
    apply Interlaces.toPrec
    apply interlaces_one_linear
    rw [h1]
    compute_degree!
  exact interlaces_of_one_add_X_positive_coeff_with_base P c h0 hrec hdeg hc_pos hbase
    (by simp_all) (by rw [h1]; exact hasNonnegCoeffs_one.add hasNonnegCoeffs_X) n


end RealRooted

end
