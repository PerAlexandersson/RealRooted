import RealRooted.Interlacing.Reversal
import RealRooted.MaWang.DerivativeStep
import RealRooted.MultiplierSequence.InvPochhammerSimple
import RealRooted.MultiplierSequence.ProperPosition
import RealRooted.Recurrence.RowModel

/-!
# OEIS A123382

The reversed rows become a one-step Ma--Wang family after coefficient `j` is
multiplied by the rising factorial `(3 / 2)_j`.  The reciprocal weights form a
strictly positive multiplier sequence, so strict interlacing descends to the
unweighted reversed rows and hence to the original rows.
-/

open Polynomial

namespace RealRooted.Applications.OEIS.A123382

noncomputable section

private def weightedStep (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 3)) *
    (C 4 * p + C (3 * ((n : ℝ) + 1) / 2) * (X * p) - X ^ 2 * p.derivative)

private def weightedPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => weightedStep n (weightedPolynomial n)

private def invPochhammer (k : ℕ) : ℝ :=
  ((ascPochhammer ℝ k).eval (3 / 2))⁻¹

private def reflectedPolynomial (n : ℕ) : ℝ[X] :=
  diagonalOperator invPochhammer (weightedPolynomial n)

/-- The polynomial model for the A123382 rows. -/
def polynomial (n : ℕ) : ℝ[X] :=
  (reflectedPolynomial n).reverse

private theorem weightedStep_degree_pos (n : ℕ) {p : ℝ[X]}
    (hdeg : p.natDegree = n) (hlc : HasPosLeadingCoeff p) :
    (weightedStep n p).natDegree = n + 1 ∧
      HasPosLeadingCoeff (weightedStep n p) := by
  have htop :
      ((-(1 : ℝ) * (p.natDegree : ℝ) + 3 * ((n : ℝ) + 1) / 2) *
        p.leadingCoeff) ≠ 0 := by
    have hfactor : 0 < -(n : ℝ) + 3 * ((n : ℝ) + 1) / 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hdeg]
    simpa only [neg_one_mul] using mul_ne_zero hfactor.ne' hlc.ne'
  have hcore := Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
    p 0 0 (-1) 4 (3 * ((n : ℝ) + 1) / 2) (by simp) htop
  have hcoreEq :
      (C 0 * X + C (-1 : ℝ) * X ^ 2) * p.derivative +
          (C 4 + C (3 * ((n : ℝ) + 1) / 2) * X) * p + 0 =
        C 4 * p + C (3 * ((n : ℝ) + 1) / 2) * (X * p) -
          X ^ 2 * p.derivative := by
    simp only [map_zero, zero_mul, zero_add, map_neg, map_one, neg_one_mul]
    ring
  rw [hcoreEq, hdeg] at hcore
  have hscale : 0 < (2 * (n : ℝ) + 3) / ((n : ℝ) + 3) := by
    positivity
  rw [weightedStep]
  constructor
  · rw [natDegree_C_mul hscale.ne', hcore.1]
  · apply hasPosLeadingCoeff_C_mul hscale
    rw [HasPosLeadingCoeff, hcore.2]
    have hfactor : 0 < -(n : ℝ) + 3 * ((n : ℝ) + 1) / 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simpa only [neg_one_mul] using mul_pos hfactor hlc

private theorem weightedStep_strictInterl (n : ℕ) {p : ℝ[X]}
    (hdeg : p.natDegree = n) (hlc : HasPosLeadingCoeff p) (hsplits : p.Splits) :
    StrictInterl p (weightedStep n p) := by
  have hstep := weightedStep_degree_pos n hdeg hlc
  have hscale : 0 < (2 * (n : ℝ) + 3) / ((n : ℝ) + 3) := by
    positivity
  let q := C 4 * p + C (3 * ((n : ℝ) + 1) / 2) * (X * p) -
    X ^ 2 * p.derivative
  have hqdeg : q.natDegree = n + 1 := by
    rw [← natDegree_C_mul hscale.ne', ← weightedStep, hstep.1]
  have hqpos : HasPosLeadingCoeff q := by
    have hscaled := hstep.2
    rw [weightedStep, HasPosLeadingCoeff,
      Polynomial.leadingCoeff_C_mul_of_isUnit
        (isUnit_iff_ne_zero.mpr hscale.ne')] at hscaled
    exact (mul_pos_iff_of_pos_left hscale).mp hscaled
  have hqeq :
      (C 4 + C (3 * ((n : ℝ) + 1) / 2) * X) * p +
          (-(C (1 : ℝ)) * X ^ 2) * p.derivative = q := by
    dsimp only [q]
    simp only [map_one, neg_one_mul]
    ring
  have hraw : StrictInterl p
      ((C 4 + C (3 * ((n : ℝ) + 1) / 2) * X) * p +
        (-(C (1 : ℝ)) * X ^ 2) * p.derivative) := by
    apply MaWang.strictInterl_derivative_neg_C_mul_X_sq_of_splits
    · exact hsplits
    · rw [hqeq, hqdeg, hdeg]
      lia
    · rw [hqeq, hqdeg, hdeg]
    · rw [hqeq]
      exact hqpos
    · exact hlc
    · norm_num
  rw [weightedStep]
  apply StrictInterl.C_mul_right _ hscale.ne'
  simp only [map_one, neg_one_mul] at hraw
  convert hraw using 1
  ring

private theorem weightedStep_coeff_zero (n : ℕ) (p : ℝ[X]) :
    (weightedStep n p).coeff 0 =
      ((2 * (n : ℝ) + 3) / ((n : ℝ) + 3)) * 4 * p.coeff 0 := by
  simp only [weightedStep, coeff_C_mul, coeff_sub, coeff_add, coeff_X_mul_zero,
    coeff_X_pow_mul']
  norm_num
  ring

private theorem weightedStep_coeff_succ (n k : ℕ) (p : ℝ[X]) :
    (weightedStep n p).coeff (k + 1) =
      ((2 * (n : ℝ) + 3) / ((n : ℝ) + 3)) *
        (4 * p.coeff (k + 1) +
          (3 * ((n : ℝ) + 1) / 2 - (k : ℝ)) * p.coeff k) := by
  simp only [weightedStep, coeff_C_mul, coeff_sub, coeff_add, coeff_X_mul,
    coeff_X_pow_mul', coeff_derivative]
  split_ifs with h
  · have hk : 1 ≤ k := by lia
    have hsub : k + 1 - 2 = k - 1 := by lia
    rw [hsub, Nat.sub_add_cancel hk, Nat.cast_sub hk]
    push_cast
    ring
  · have hk : k = 0 := by lia
    subst k
    norm_num

private theorem weightedPolynomial_properties (n : ℕ) :
    (weightedPolynomial n).natDegree = n ∧
      HasPosLeadingCoeff (weightedPolynomial n) ∧
      HasNonnegCoeffs (weightedPolynomial n) ∧
      (weightedPolynomial n).Splits := by
  induction n with
  | zero =>
      refine ⟨by simp [weightedPolynomial], by simp [weightedPolynomial, HasPosLeadingCoeff],
        ?_, by simp [weightedPolynomial]⟩
      intro k
      rw [weightedPolynomial, coeff_one]
      split_ifs <;> norm_num
  | succ n ih =>
      rcases ih with ⟨hdeg, hlc, hcoeff, hsplits⟩
      have hstepInter : StrictInterl (weightedPolynomial n) (weightedPolynomial (n + 1)) := by
        rw [weightedPolynomial]
        exact weightedStep_strictInterl n hdeg hlc hsplits
      have hstepDegree := weightedStep_degree_pos n hdeg hlc
      rw [← weightedPolynomial] at hstepDegree
      refine ⟨hstepDegree.1, hstepDegree.2, ?_, hstepInter.2.1.2⟩
      · intro k
        rcases k with _ | k
        · rw [weightedPolynomial, weightedStep_coeff_zero]
          have hzero := hcoeff 0
          positivity
        · rw [weightedPolynomial, weightedStep_coeff_succ]
          by_cases hk : k ≤ n
          · have hfactor : 0 ≤ 3 * ((n : ℝ) + 1) / 2 - (k : ℝ) := by
              have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
              linarith
            exact mul_nonneg (by positivity) (add_nonneg
              (mul_nonneg (by norm_num) (hcoeff (k + 1)))
              (mul_nonneg hfactor (hcoeff k)))
          · have hk' : n < k := Nat.lt_of_not_ge hk
            rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; lia),
              coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; lia)]
            norm_num

private theorem weightedPolynomial_strictInterl (n : ℕ) :
    StrictInterl (weightedPolynomial n) (weightedPolynomial (n + 1)) := by
  rw [weightedPolynomial]
  exact weightedStep_strictInterl n
    (weightedPolynomial_properties n).1
    (weightedPolynomial_properties n).2.1
    (weightedPolynomial_properties n).2.2.2

private theorem reflectedPolynomial_strictInterl (n : ℕ) :
    StrictInterl (reflectedPolynomial n) (reflectedPolynomial (n + 1)) := by
  apply IsMultiplierSequence.strictInterl_diagonalOperator_of_pos
    ((isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_inv_ascPochhammer
        (by norm_num : (0 : ℝ) < 3 / 2))).1)
  · intro k
    exact inv_pos.mpr (ascPochhammer_pos k (3 / 2) (by norm_num))
  · exact weightedPolynomial_strictInterl n

private theorem weightedPolynomial_coeff_zero_pos (n : ℕ) :
    0 < (weightedPolynomial n).coeff 0 := by
  induction n with
  | zero => simp [weightedPolynomial]
  | succ n ih =>
      rw [weightedPolynomial, weightedStep_coeff_zero]
      positivity

private theorem reflectedPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (reflectedPolynomial n) := by
  intro k
  rw [reflectedPolynomial, coeff_diagonalOperator]
  exact mul_nonneg (le_of_lt (inv_pos.mpr
    (ascPochhammer_pos k (3 / 2) (by norm_num))))
    ((weightedPolynomial_properties n).2.2.1 k)

private theorem reflectedPolynomial_coeff_zero_pos (n : ℕ) :
    0 < (reflectedPolynomial n).coeff 0 := by
  rw [reflectedPolynomial, coeff_diagonalOperator, invPochhammer]
  have hpoch : (ascPochhammer ℝ 0).eval (3 / 2) = 1 := by simp
  rw [hpoch, inv_one, one_mul]
  exact weightedPolynomial_coeff_zero_pos n

private theorem reflectedPolynomial_natDegree (n : ℕ) :
    (reflectedPolynomial n).natDegree = n := by
  unfold reflectedPolynomial invPochhammer
  rw [natDegree_diagonalOperator_inv_ascPochhammer
      (by norm_num : (0 : ℝ) < 3 / 2)]
  · exact (weightedPolynomial_properties n).1
  · exact (weightedPolynomial_properties n).2.1.ne_zero

private theorem reflectedPolynomial_roots_neg (n : ℕ) :
    ∀ r ∈ (reflectedPolynomial n).roots, r < 0 := by
  intro r hr
  apply lt_of_le_of_ne
    (roots_nonpos_of_hasNonnegCoeffs (reflectedPolynomial_hasNonnegCoeffs n) r hr)
  intro hrzero
  subst r
  have hne : reflectedPolynomial n ≠ 0 := by
    exact fun hzero ↦ (reflectedPolynomial_coeff_zero_pos n).ne' (by simp [hzero])
  have hroot := (mem_roots hne).mp hr
  rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero] at hroot
  exact (reflectedPolynomial_coeff_zero_pos n).ne' hroot

/-- Consecutive A123382 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) := by
  exact interlaces_reverse_of_roots_neg
    ((reflectedPolynomial_strictInterl n).toInterlaces (by
      rw [reflectedPolynomial_natDegree, reflectedPolynomial_natDegree]))
    (reflectedPolynomial_roots_neg (n + 1))
    (reflectedPolynomial_roots_neg n)

/-- Every A123382 weighted-reversal model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (polynomial_interlaces n).2.1.2

/-- Consecutive A123382 model rows are in directed proper position. -/
theorem polynomial_strictInterl (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) :=
  (polynomial_interlaces n).toStrictInterl


/-! ## The literal downstream recurrence

`recurrenceRow` is the A123382 recurrence as stated downstream: a two-step recurrence with a
derivative term. The identification `recurrenceRow n = polynomial n` was found by Aristotle
(Harmonic): coefficientwise, the reversed reweighted orbit satisfies the two-step relation by an
induction in which each relation is a linear combination of the two previous ones.
-/

private def recurrenceRow : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 4 * X
  | n + 2 => ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (24 + (9
      * (n : ℝ))))) * X + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ)))))
      * (-96 + (-36 * (n : ℝ))))) * X ^ 2)) * (recurrenceRow (n + 1)).derivative
      + ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((35 / 2) + ((3
      + (n : ℝ))) ^ (2) + ((13 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3
      + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-220 + (-80 * (n : ℝ)) + (50 * ((3
      + (n : ℝ))) ^ (2))))) * X)) * recurrenceRow (n + 1) + ((C (((1 / ((10 + (2 * ((3
      + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((-15 / 2) + ((3 + (n : ℝ))) ^ (2)
      + ((-7 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3
      * (n : ℝ))))) * (60 + (-8 * ((3 + (n : ℝ))) ^ (2)) + (28 * (n : ℝ))))) * X
      + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-120 + (-56
      * (n : ℝ)) + (16 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * recurrenceRow n


/-- Coefficients of the weighted orbit. -/
private def w (n k : ℕ) : ℝ := (weightedPolynomial n).coeff k

/-- The rising factorial `(3/2)_j`. -/
private def poch (j : ℕ) : ℝ := (ascPochhammer ℝ j).eval (3 / 2)

private lemma poch_pos (j : ℕ) : 0 < poch j := ascPochhammer_pos j _ (by norm_num)

private lemma poch_succ (j : ℕ) : poch (j + 1) = poch j * (3 / 2 + j) := by
  simp [poch, ascPochhammer_succ_eval]

private lemma poch_zero : poch 0 = 1 := by simp [poch]

private lemma w_zero_zero : w 0 0 = 1 := by simp [w, weightedPolynomial]

private lemma w_zero_succ (k : ℕ) : w 0 (k + 1) = 0 := by
  simp [w, weightedPolynomial, coeff_one]

private lemma w_succ_zero (n : ℕ) :
    w (n + 1) 0 = (2 * (n : ℝ) + 3) / ((n : ℝ) + 3) * (4 * w n 0) := by
  simp [w, weightedPolynomial, weightedStep, pow_two, mul_assoc]

private lemma w_succ_succ (n j : ℕ) :
    w (n + 1) (j + 1) = (2 * (n : ℝ) + 3) / ((n : ℝ) + 3) *
      (4 * w n (j + 1) + (3 * ((n : ℝ) + 1) / 2 - j) * w n j) := by
  rcases j with _ | j
  · simp [w, weightedPolynomial, weightedStep, coeff_C_mul, pow_two, mul_assoc, coeff_X_mul]
  · simp only [w, weightedPolynomial, weightedStep, coeff_C_mul, coeff_add, coeff_sub, pow_two,
      mul_assoc, coeff_X_mul, coeff_derivative]
    push_cast
    ring

private lemma w_eq_zero_of_lt : ∀ (n k : ℕ), n < k → w n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩; exact w_zero_succ k
  | succ n ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    rw [w_succ_succ, ih _ (by lia), ih _ (by lia)]
    ring

/-- Reweighted coefficients, extended by zero to negative indices. -/
private def bz (n : ℕ) (k : ℤ) : ℝ := if 0 ≤ k then w n k.toNat / poch k.toNat else 0

private lemma bz_nat (n j : ℕ) : bz n (j : ℤ) = w n j / poch j := by simp [bz]

private lemma bz_neg (n : ℕ) {k : ℤ} (hk : k < 0) : bz n k = 0 := by
  simp [bz]; lia

private lemma bz_big (n : ℕ) {k : ℤ} (hk : (n : ℤ) < k) : bz n k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by lia⟩
  rw [bz_nat, w_eq_zero_of_lt n j (by lia)]; simp

private lemma bz_step_mul (n : ℕ) (k : ℤ) :
    (2 * (k : ℝ) + 1) * ((n : ℝ) + 3) * bz (n + 1) k =
      (2 * (n : ℝ) + 3) * (4 * (2 * (k : ℝ) + 1) * bz n k
        + (3 * (n : ℝ) + 5 - 2 * k) * bz n (k - 1)) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [bz_neg _ hk, bz_neg _ hk, bz_neg _ (by lia)]; ring
  · rw [bz_neg n (show (0:ℤ) - 1 < 0 by norm_num)]
    have := bz_nat (n + 1) 0
    have h2 := bz_nat n 0
    simp only [Nat.cast_zero] at this h2
    rw [this, h2, w_succ_zero, poch_zero]
    have : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨k.toNat - 1, by lia⟩
    have e1 : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [show ((j : ℤ) + 1 - 1) = (j : ℤ) by ring, e1, bz_nat, bz_nat, bz_nat, w_succ_succ,
      poch_succ]
    have := poch_pos j
    have : (n : ℝ) + 3 ≠ 0 := by positivity
    have : (3 / 2 + (j : ℝ)) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

private lemma two_k_add_one_ne (k : ℤ) : 2 * (k : ℝ) + 1 ≠ 0 := by
  have : (2 * k + 1 : ℤ) ≠ 0 := by lia
  exact_mod_cast this

private lemma bz_step (n : ℕ) (k : ℤ) :
    bz (n + 1) k = (2 * (n : ℝ) + 3) * (4 * (2 * (k : ℝ) + 1) * bz n k
        + (3 * (n : ℝ) + 5 - 2 * k) * bz n (k - 1)) / ((2 * (k : ℝ) + 1) * ((n : ℝ) + 3)) := by
  rw [← bz_step_mul, mul_div_cancel_left₀]
  exact mul_ne_zero (two_k_add_one_ne k) (by positivity)

/-- The coefficient form of the recurrenceRow recurrence, reindexed by `k = n + 2 - m`. -/
private def Erel (n : ℕ) (k : ℤ) : Prop :=
  (2 * (n : ℝ) ^ 2 + 15 * n + 28) * bz (n + 2) k =
    (24 + 9 * (n : ℝ)) * ((n + 2 - k) * bz (n + 1) (k - 1) - 4 * (n + 1 - k) * bz (n + 1) k)
    + (2 * (n : ℝ) ^ 2 + 25 * n + 53) / 2 * bz (n + 1) (k - 1)
    + (50 * (n : ℝ) ^ 2 + 220 * n + 230) * bz (n + 1) k
    + ((n : ℝ) + 1) * (2 * n + 3) / 2 * (bz n (k - 2) - 8 * bz n (k - 1) + 16 * bz n k)

private lemma Erel_succ (n : ℕ) (k : ℤ) (h1 : Erel n k) (h2 : Erel n (k - 1)) : Erel (n + 1) k := by
  unfold Erel at *
  rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at *
  rw [show k - 1 - 1 = k - 2 by ring, show k - 1 - 2 = k - 3 by ring] at h2
  have s3 := bz_step (n + 2) k
  have s2a := bz_step (n + 1) k
  have s2b := bz_step (n + 1) (k - 1)
  have s1a := bz_step n k
  have s1b := bz_step n (k - 1)
  have s1c := bz_step n (k - 2)
  rw [show n + 2 + 1 = n + 3 from rfl] at s3
  rw [show n + 1 + 1 = n + 2 from rfl] at s2a s2b
  rw [show k - 1 - 1 = k - 2 by ring] at s2b s1b
  rw [show k - 2 - 1 = k - 3 by ring] at s1c
  rw [s3]
  simp only [s2a, s2b] at h1 h2 ⊢
  simp only [s1a, s1b, s1c] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  generalize bz n k = x0 at h1 h2 ⊢
  generalize bz n (k - 1) = x1 at h1 h2 ⊢
  generalize bz n (k - 2) = x2 at h1 h2 ⊢
  generalize bz n (k - 3) = x3 at h1 h2 ⊢
  have hk0 := two_k_add_one_ne k
  have hk1 : 2 * ((k : ℝ) - 1) + 1 ≠ 0 := by
    have := two_k_add_one_ne (k - 1); push_cast at this; exact this
  have hk2 : 2 * ((k : ℝ) - 2) + 1 ≠ 0 := by
    have := two_k_add_one_ne (k - 2); push_cast at this; exact this
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have hn4 : (n : ℝ) + 1 + 3 ≠ 0 := by positivity
  have hn5 : (n : ℝ) + 2 + 3 ≠ 0 := by positivity
  have hn6 : (n : ℝ) + 4 ≠ 0 := by positivity
  have hn7 : 9 * (n : ℝ) + 24 ≠ 0 := by positivity
  linear_combination (norm := skip)
    (12 * (2 * (n : ℝ) + 5) * (3 * n + 11) / ((n + 4) * (9 * n + 24))) * h1
    + (12 * (2 * (n : ℝ) + 5) * (3 * n + 11) / ((n + 4) * (9 * n + 24))) *
      ((3 * n + 9 - 2 * k) / (4 * (2 * k + 1))) * h2
  field_simp
  ring

private lemma bz_zero (k : ℤ) : bz 0 k = if k = 0 then 1 else 0 := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [bz_neg _ hk, ite_eq_right (by lia)]
  · have := bz_nat 0 0
    simp only [Nat.cast_zero] at this
    rw [this, w_zero_zero, poch_zero]; simp
  · rw [bz_big _ (by simpa using hk), ite_eq_right (by lia)]

private lemma Erel_zero (k : ℤ) : Erel 0 k := by
  unfold Erel
  have s2a := bz_step 1 k
  have s2b := bz_step 0 k
  have s1b := bz_step 0 (k - 1)
  rw [show k - 1 - 1 = k - 2 by ring] at s1b
  rw [show (0 : ℕ) + 2 = 1 + 1 from rfl, s2a]
  simp only [show (0 : ℕ) + 1 = 1 from rfl] at s2b s1b ⊢
  rw [s2b, s1b]
  rw [bz_zero k, bz_zero (k - 1), bz_zero (k - 2)]
  have hk0 := two_k_add_one_ne k
  rcases (by lia : k = 0 ∨ k = 1 ∨ k = 2 ∨ (k ≠ 0 ∧ k - 1 ≠ 0 ∧ k - 2 ≠ 0)) with
    rfl | rfl | rfl | ⟨h0, h1, h2⟩
  · norm_num
  · norm_num
  · norm_num
  · simp [h0, h1, h2]

private lemma Erel_all (n : ℕ) : ∀ k : ℤ, Erel n k := by
  induction n with
  | zero => exact Erel_zero
  | succ n ih => exact fun k => Erel_succ n k (ih k) (ih (k - 1))

/-- Coefficients of a polynomial, extended by zero to negative indices. -/
private def cz (p : ℝ[X]) (i : ℤ) : ℝ := if 0 ≤ i then p.coeff i.toNat else 0

private lemma cz_nat (p : ℝ[X]) (m : ℕ) : cz p (m : ℤ) = p.coeff m := by simp [cz]

private lemma cz_zero (p : ℝ[X]) : cz p 0 = p.coeff 0 := by simp [cz]

private lemma cz_one (p : ℝ[X]) : cz p 1 = p.coeff 1 := by simp [cz]

private lemma cz_neg (p : ℝ[X]) {i : ℤ} (hi : i < 0) : cz p i = 0 := by
  simp [cz]; lia

/-- The reversed reweighted polynomial. -/
private def Bp (n : ℕ) : ℝ[X] := ∑ j ∈ Finset.range (n + 1),
  C ((weightedPolynomial n).coeff j / (ascPochhammer ℝ j).eval (3 / 2)) * X ^ (n - j)

private lemma coeff_Bp (n m : ℕ) : (Bp n).coeff m = bz n ((n : ℤ) - m) := by
  unfold Bp
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m ≤ n
  · rw [Finset.sum_eq_single (n - m)]
    · rw [ite_eq_left (by lia), show ((n : ℤ) - m) = ((n - m : ℕ) : ℤ) by lia, bz_nat]
      rfl
    · intro j hj hne
      rw [ite_eq_right]
      simp at hj
      lia
    · intro h; simp at h
  · rw [Finset.sum_eq_zero, bz_neg _ (by lia)]
    intro j hj
    rw [ite_eq_right]
    simp at hj
    lia

private lemma cz_Bp (n : ℕ) (i : ℤ) : cz (Bp n) i = bz n ((n : ℤ) - i) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [cz_neg _ hi, bz_big _ (by lia)]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = m := ⟨i.toNat, by lia⟩
    rw [cz_nat, coeff_Bp]

private lemma coeff_rec (p q : ℝ[X]) (a1 a2 b0 b1 g0 g1 g2 : ℝ) (m : ℕ) :
    ((C a1 * X + C a2 * X ^ 2) * derivative p + (C b0 + C b1 * X) * p
      + (C g0 + C g1 * X + C g2 * X ^ 2) * q).coeff m =
    a1 * m * cz p m + a2 * ((m : ℝ) - 1) * cz p ((m : ℤ) - 1) + b0 * cz p m
      + b1 * cz p ((m : ℤ) - 1) + g0 * cz q m + g1 * cz q ((m : ℤ) - 1)
      + g2 * cz q ((m : ℤ) - 2) := by
  rcases m with _ | _ | m
  · simp [add_mul, mul_assoc, pow_two, cz_zero, cz_neg]
  · simp [add_mul, mul_assoc, pow_two, coeff_C_mul, coeff_X_mul, cz_zero, cz_one, cz_neg,
      coeff_derivative]
    ring
  · rw [show ((m + 1 + 1 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      show ((m + 1 + 1 : ℕ) : ℤ) - 2 = (m : ℤ) by push_cast; ring]
    simp only [cz_nat]
    simp [add_mul, mul_assoc, pow_two, coeff_C_mul, coeff_X_mul, coeff_derivative]
    ring

private lemma A_step (n : ℕ) (h0 : recurrenceRow n = Bp n) (h1 : recurrenceRow (n
  + 1) = Bp (n + 1)) :
    recurrenceRow (n + 2) = Bp (n + 2) := by
  rw [recurrenceRow, h0, h1]
  ext m
  rw [coeff_rec, coeff_Bp]
  simp only [cz_Bp]
  have E := Erel_all n ((n : ℤ) + 2 - m)
  unfold Erel at E
  rw [show ((n + 1 : ℕ) : ℤ) - (m : ℤ) = (n : ℤ) + 2 - m - 1 by push_cast; ring,
    show ((n + 1 : ℕ) : ℤ) - ((m : ℤ) - 1) = (n : ℤ) + 2 - m by push_cast; ring,
    show (n : ℤ) - ((m : ℤ) - 1) = (n : ℤ) + 2 - m - 1 by ring,
    show (n : ℤ) - ((m : ℤ) - 2) = (n : ℤ) + 2 - m by ring,
    show (n : ℤ) - (m : ℤ) = (n : ℤ) + 2 - m - 2 by ring,
    show ((n + 2 : ℕ) : ℤ) - (m : ℤ) = (n : ℤ) + 2 - m by push_cast; ring]
  push_cast at E
  have hD : (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * n) ≠ 0 := by positivity
  field_simp
  linear_combination -2 * E

private lemma A_zero : recurrenceRow 0 = Bp 0 := by
  ext m
  rw [coeff_Bp, bz_zero]
  rcases m with _ | m
  · simp [recurrenceRow]
  · simp [recurrenceRow, coeff_one]
    lia

private lemma bz_one_zero : bz 1 0 = 4 := by
  have := bz_step 0 0
  rw [bz_zero, bz_zero] at this
  norm_num at this
  exact this

private lemma bz_one_one : bz 1 1 = 1 := by
  have := bz_step 0 1
  rw [bz_zero, bz_zero] at this
  norm_num at this
  exact this

private lemma A_one : recurrenceRow 1 = Bp 1 := by
  ext m
  rw [coeff_Bp]
  rcases m with _ | _ | m
  · simp [recurrenceRow, bz_one_one]
  · simp [recurrenceRow, bz_one_zero, coeff_X, coeff_one]
  · rw [bz_neg _ (by lia)]
    simp [recurrenceRow, coeff_X, coeff_one]


/-- The literal recurrence produces the reversed, reweighted orbit. -/
private theorem recurrenceRow_eq_Bp (n : ℕ) : recurrenceRow n = Bp n := by
  have key : ∀ n, recurrenceRow n = Bp n ∧ recurrenceRow (n + 1) = Bp (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨A_zero, A_one⟩
    | succ n ih => exact ⟨ih.2, A_step n ih.1 ih.2⟩
  exact (key n).1

/-- The model rows are the reversed, reweighted orbit. -/
private theorem polynomial_eq_Bp (n : ℕ) : polynomial n = Bp n := by
  ext m
  rw [coeff_Bp, polynomial, coeff_reverse, reflectedPolynomial_natDegree]
  rcases le_or_gt m n with hm | hm
  · rw [revAt_le hm, show ((n : ℤ) - m) = ((n - m : ℕ) : ℤ) by lia, bz_nat, reflectedPolynomial,
      coeff_diagonalOperator, invPochhammer, w, poch]
    ring
  · rw [bz_neg _ (by lia), coeff_eq_zero_of_natDegree_lt]
    rw [reflectedPolynomial_natDegree]
    change n < (if m ≤ n then n - m else m)
    simpa [not_le.mpr hm] using hm

/-- A sequence with the A123382 initial rows and the downstream recurrence is the A123382
model sequence. -/
private theorem eq_polynomial_of_recurrence {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1) (hone : P 1 = 1 + 4 * X)
    (hrec : ∀ n, P (n + 2) =
      ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (24 + (9
        * (n : ℝ))))) * X + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ)))))
        * (-96 + (-36 * (n : ℝ))))) * X ^ 2)) * (P (n + 1)).derivative
        + ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((35 / 2) + ((3
        + (n : ℝ))) ^ (2) + ((13 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3
        + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-220 + (-80 * (n : ℝ)) + (50 * ((3
        + (n : ℝ))) ^ (2))))) * X)) * P (n + 1) + ((C (((1 / ((10 + (2 * ((3
        + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((-15 / 2) + ((3 + (n : ℝ))) ^ (2)
        + ((-7 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3
        * (n : ℝ))))) * (60 + (-8 * ((3 + (n : ℝ))) ^ (2)) + (28 * (n : ℝ))))) * X
        + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-120 + (-56
        * (n : ℝ)) + (16 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * P n) :
    ∀ n, P n = polynomial n := by
  have hrow : ∀ n, P n = recurrenceRow n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => exact hzero
      | 1 => exact hone
      | n + 2 =>
        rw [hrec, ih n (by lia), ih (n + 1) (by lia)]
        rfl
  intro n
  rw [hrow, recurrenceRow_eq_Bp, polynomial_eq_Bp]

/-- Any sequence with the A123382 initial rows and recurrence has interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1) (hone : P 1 = 1 + 4 * X)
    (hrec : ∀ n, P (n + 2) =
      ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (24 + (9
        * (n : ℝ))))) * X + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ)))))
        * (-96 + (-36 * (n : ℝ))))) * X ^ 2)) * (P (n + 1)).derivative
        + ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((35 / 2) + ((3
        + (n : ℝ))) ^ (2) + ((13 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3
        + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-220 + (-80 * (n : ℝ)) + (50 * ((3
        + (n : ℝ))) ^ (2))))) * X)) * P (n + 1) + ((C (((1 / ((10 + (2 * ((3
        + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((-15 / 2) + ((3 + (n : ℝ))) ^ (2)
        + ((-7 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3
        * (n : ℝ))))) * (60 + (-8 * ((3 + (n : ℝ))) ^ (2)) + (28 * (n : ℝ))))) * X
        + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-120 + (-56
        * (n : ℝ)) + (16 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * P n)
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  rw [eq_polynomial_of_recurrence hzero hone hrec n,
    eq_polynomial_of_recurrence hzero hone hrec (n + 1)]
  exact polynomial_interlaces n

/-- Any sequence with the A123382 initial rows and recurrence has strictly interlacing
consecutive rows. -/
@[rr_row_model]
theorem strictInterl_of_recurrence {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1) (hone : P 1 = 1 + 4 * X)
    (hrec : ∀ n, P (n + 2) =
      ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (24 + (9
        * (n : ℝ))))) * X + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ)))))
        * (-96 + (-36 * (n : ℝ))))) * X ^ 2)) * (P (n + 1)).derivative
        + ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((35 / 2) + ((3
        + (n : ℝ))) ^ (2) + ((13 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3
        + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-220 + (-80 * (n : ℝ)) + (50 * ((3
        + (n : ℝ))) ^ (2))))) * X)) * P (n + 1) + ((C (((1 / ((10 + (2 * ((3
        + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * ((-15 / 2) + ((3 + (n : ℝ))) ^ (2)
        + ((-7 / 2) * (n : ℝ))))) + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3
        * (n : ℝ))))) * (60 + (-8 * ((3 + (n : ℝ))) ^ (2)) + (28 * (n : ℝ))))) * X
        + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-120 + (-56
        * (n : ℝ)) + (16 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * P n)
    (n : ℕ) : StrictInterl (P n) (P (n + 1)) := by
  rw [eq_polynomial_of_recurrence hzero hone hrec n,
    eq_polynomial_of_recurrence hzero hone hrec (n + 1)]
  exact polynomial_strictInterl n

end

end RealRooted.Applications.OEIS.A123382
