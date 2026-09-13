import RealRooted.Applications.OEIS.A144438
import RealRooted.GeneralizedEulerian

/-!
# Weighted deco Eulerian polynomials

This file studies the recurrence deformation

`D (n + 2; w) = X (1 - X) (D (n + 1; w))' +
  (1 + (n + 2) X) D (n + 1; w) + w X D (n; w)`.

At weight one this is the algebraic A144438 facade, while at weight zero it
is the ordinary Eulerian recurrence `generalizedEulerian 1`. These are checked
recurrence identities only; no combinatorial interpretation of the parameter
`w` is asserted here.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined weighted deco Eulerian polynomial sequence. -/
def weightedDecoEulerian (w : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (X - X ^ 2) * (weightedDecoEulerian w (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * weightedDecoEulerian w (n + 1) +
          (C w * X) * weightedDecoEulerian w n

@[simp]
theorem weightedDecoEulerian_zero (w : ℝ) : weightedDecoEulerian w 0 = 1 := rfl

@[simp]
theorem weightedDecoEulerian_one (w : ℝ) : weightedDecoEulerian w 1 = 1 + X := rfl

/-- The defining weighted second-order derivative recurrence. -/
theorem weightedDecoEulerian_recurrence (w : ℝ) (n : ℕ) :
    weightedDecoEulerian w (n + 2) =
      (X - X ^ 2) * (weightedDecoEulerian w (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * weightedDecoEulerian w (n + 1) +
          (C w * X) * weightedDecoEulerian w n := rfl

/-- The first transition, including the lag-weight contribution. -/
theorem weightedDecoEulerian_two (w : ℝ) :
    weightedDecoEulerian w 2 = 1 + C (4 + w) * X + X ^ 2 := by
  norm_num [weightedDecoEulerian, map_ofNat]
  ring

private theorem weightedDecoEulerian_affine_recurrence (w : ℝ) (n : ℕ) :
    weightedDecoEulerian w (n + 2) =
      (C 1 * X + C (-1) * X ^ 2) *
          (weightedDecoEulerian w (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * weightedDecoEulerian w (n + 1) +
          (C w * X) * weightedDecoEulerian w n := by
  simpa only [map_one, map_neg, one_mul, neg_one_mul, sub_eq_add_neg] using
    weightedDecoEulerian_recurrence w n

/-- At weight one, the weighted family is exactly the unweighted deco
Eulerian/A144438 family at every rank. -/
theorem weightedDecoEulerian_one_weight :
    ∀ n : ℕ, weightedDecoEulerian 1 n = decoEulerian n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [weightedDecoEulerian_recurrence, decoEulerian_recurrence, ih0, ih1]
      simp

/-- At weight zero, the weighted family is exactly the ordinary Eulerian
family at every rank. -/
theorem weightedDecoEulerian_zero_weight :
    ∀ n : ℕ, weightedDecoEulerian 0 n = generalizedEulerian 1 n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [generalizedEulerian]
  | one => simp [generalizedEulerian]
  | more n ih0 ih1 =>
      rw [weightedDecoEulerian_recurrence, ih0, ih1]
      conv_rhs => rw [generalizedEulerian_succ]
      simp only [map_zero, zero_mul, add_zero, map_one, one_mul]
      push_cast
      ring_nf

/-- The rankwise root and interlacing certificate for every nonnegative
weight. -/
theorem weightedDecoEulerian_certificate {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    AffineLagSecondOrderCertificate (weightedDecoEulerian w) n := by
  exact affine_lag_second_order_derivative_certificate_of_nonneg_lag
    (weightedDecoEulerian w) 1 w (by norm_num) hw
      (weightedDecoEulerian_zero w) (weightedDecoEulerian_one w) (by
        intro m
        simpa only [one_mul, one_add_one_eq_two] using
          weightedDecoEulerian_affine_recurrence w m) n

/-- The weighted polynomial at rank `n` has degree `n`, without a sign
condition on the weight. -/
@[simp]
theorem weightedDecoEulerian_natDegree (w : ℝ) (n : ℕ) :
    (weightedDecoEulerian w n).natDegree = n := by
  exact natDegree_of_second_order_derivative (weightedDecoEulerian w) 1 w
    (fun m => (2 : ℝ) + m) (weightedDecoEulerian_zero w)
      (weightedDecoEulerian_one w) (weightedDecoEulerian_affine_recurrence w)
        (by intro m; ring) n

/-- Weighted deco Eulerian polynomials are monic, without a sign condition
on the weight. -/
theorem weightedDecoEulerian_monic (w : ℝ) (n : ℕ) :
    (weightedDecoEulerian w n).Monic := by
  exact monic_of_second_order_derivative (weightedDecoEulerian w) 1 w
    (fun m => (2 : ℝ) + m) (weightedDecoEulerian_zero w)
      (weightedDecoEulerian_one w) (weightedDecoEulerian_affine_recurrence w)
        (by intro m; ring) n

/-- Every weighted row has constant coefficient one. -/
@[simp]
theorem weightedDecoEulerian_coeff_zero (w : ℝ) (n : ℕ) :
    (weightedDecoEulerian w n).coeff 0 = 1 := by
  exact coeff_zero_affine_lag_second_order_derivative
    (P := weightedDecoEulerian w) (a := 1) (c := w)
    (weightedDecoEulerian_zero w) (weightedDecoEulerian_one w) (by
      intro m
      simpa only [one_mul, one_add_one_eq_two] using
        weightedDecoEulerian_affine_recurrence w m) n

/-- Nonnegative weights give nonnegative coefficients. -/
theorem weightedDecoEulerian_hasNonnegCoeffs {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    HasNonnegCoeffs (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_certificate hw n).nonnegCoeffs

/-- Specialized coefficient recurrence for the weighted family. -/
theorem weightedDecoEulerian_coeff_succ_succ (w : ℝ) (n k : ℕ) :
    (weightedDecoEulerian w (n + 2)).coeff (k + 1) =
      ((k : ℝ) + 2) * (weightedDecoEulerian w (n + 1)).coeff (k + 1) +
        ((n : ℝ) + 2 - k) * (weightedDecoEulerian w (n + 1)).coeff k +
          w * (weightedDecoEulerian w n).coeff k := by
  rw [second_order_derivative_coeff_succ_succ (weightedDecoEulerian w) 1 w
    (fun m => (2 : ℝ) + m) (weightedDecoEulerian_affine_recurrence w)]
  ring

/-- Every coefficient in the degree support is strictly positive when the
weight is nonnegative. -/
theorem weightedDecoEulerian_coeff_pos_of_le {w : ℝ} (hw : 0 ≤ w) :
    ∀ n k : ℕ, k ≤ n → 0 < (weightedDecoEulerian w n).coeff k := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by lia
      subst k
      simp
  | one =>
      intro k hk
      interval_cases k <;>
        norm_num [weightedDecoEulerian, coeff_add, coeff_one, coeff_X]
  | more n _ ih1 =>
      intro k hk
      rcases k with _ | k
      · simp
      · rw [weightedDecoEulerian_coeff_succ_succ]
        have hk_le : k ≤ n + 1 := by lia
        have hk_real : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk_le
        have hfirst :
            0 ≤ ((k : ℝ) + 2) *
              (weightedDecoEulerian w (n + 1)).coeff (k + 1) :=
          mul_nonneg (by positivity)
            ((weightedDecoEulerian_certificate hw (n + 1)).nonnegCoeffs (k + 1))
        have hmiddle :
            0 < ((n : ℝ) + 2 - k) *
              (weightedDecoEulerian w (n + 1)).coeff k :=
          mul_pos (by linarith) (ih1 k hk_le)
        have hlast : 0 ≤ w * (weightedDecoEulerian w n).coeff k :=
          mul_nonneg hw (weightedDecoEulerian_hasNonnegCoeffs hw n k)
        linarith

/-- Coefficients at a nonnegative weight are positive exactly on the degree
support. -/
theorem weightedDecoEulerian_coeff_pos_iff {w : ℝ} (hw : 0 ≤ w) (n k : ℕ) :
    0 < (weightedDecoEulerian w n).coeff k ↔ k ≤ n := by
  constructor
  · intro hpos
    by_contra hle
    have hzero : (weightedDecoEulerian w n).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [weightedDecoEulerian_natDegree]; lia)
    linarith
  · exact weightedDecoEulerian_coeff_pos_of_le hw n k

/-- Weighted deco Eulerian polynomials are nonzero. -/
theorem weightedDecoEulerian_ne_zero (w : ℝ) (n : ℕ) :
    weightedDecoEulerian w n ≠ 0 :=
  (weightedDecoEulerian_monic w n).ne_zero

/-- Every nonnegative-weight polynomial splits over the reals. -/
theorem weightedDecoEulerian_splits {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    (weightedDecoEulerian w n).Splits := by
  have hpair := prec_and_noCommonRoot_of_affine_lag_second_order_derivative_of_nonneg_lag
    (weightedDecoEulerian w) 1 w (by norm_num) hw
      (weightedDecoEulerian_zero w) (weightedDecoEulerian_one w) (by
        intro m
        simpa only [one_mul, one_add_one_eq_two] using
          weightedDecoEulerian_affine_recurrence w m) n
  exact hpair.1.1.2

/-- Consecutive ranks at a nonnegative weight are in proper position. -/
theorem weightedDecoEulerian_prec {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    Prec (weightedDecoEulerian w n) (weightedDecoEulerian w (n + 1)) := by
  have hpair := prec_and_noCommonRoot_of_affine_lag_second_order_derivative_of_nonneg_lag
    (weightedDecoEulerian w) 1 w (by norm_num) hw
      (weightedDecoEulerian_zero w) (weightedDecoEulerian_one w) (by
        intro m
        simpa only [one_mul, one_add_one_eq_two] using
          weightedDecoEulerian_affine_recurrence w m) n
  exact hpair.1

/-- Consecutive ranks at a nonnegative weight strictly interlace. -/
theorem weightedDecoEulerian_interlaces {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    Interlaces (weightedDecoEulerian w n) (weightedDecoEulerian w (n + 1)) :=
  (weightedDecoEulerian_certificate hw n).interlaces_succ

/-- Consecutive ranks at a nonnegative weight have no common real root. -/
theorem weightedDecoEulerian_noCommonRoot {w : ℝ} (hw : 0 ≤ w) (n : ℕ)
    (r : ℝ) (hr : (weightedDecoEulerian w (n + 1)).IsRoot r) :
    ¬ (weightedDecoEulerian w n).IsRoot r :=
  (weightedDecoEulerian_certificate hw n).noCommonRoot_succ r hr

/-- Every real root at a nonnegative weight is strictly negative. -/
theorem weightedDecoEulerian_root_neg {w : ℝ} (hw : 0 ≤ w) (n : ℕ) {r : ℝ}
    (hr : (weightedDecoEulerian w n).IsRoot r) : r < 0 :=
  (weightedDecoEulerian_certificate hw n).roots_neg r hr

/-- Every polynomial at a nonnegative weight has simple roots. -/
theorem weightedDecoEulerian_hasSimpleRoots {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    HasSimpleRoots (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_certificate hw n).simpleRoots

/-- The reversed prefix through rank `n` at weight `w`. -/
def weightedDecoEulerianPrefix (w : ℝ) (n : ℕ) : List ℝ[X] :=
  (List.range (n + 1)).reverse.map (weightedDecoEulerian w)

/-- Every reversed finite prefix at a nonnegative weight is a Sturm sequence.
-/
theorem weightedDecoEulerian_isSturmSeq {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    IsSturmSeq (weightedDecoEulerianPrefix w n) := by
  exact isSturmSeq_affine_lag_second_order_derivative_of_nonneg_lag
    (weightedDecoEulerian w) 1 w (by norm_num) hw
      (weightedDecoEulerian_zero w) (weightedDecoEulerian_one w) (by
        intro m
        simpa only [one_mul, one_add_one_eq_two] using
          weightedDecoEulerian_affine_recurrence w m) n

end RealRooted.Applications.OEIS
