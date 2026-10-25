module

public import RealRooted.FiniteFreeRootCount
public import RealRooted.EulerOperator
public import RealRooted.Interlacing.ReversalCommonFactor
public import RealRooted.LinearPowerFamily
public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.MultiplierSequence.Infinite
public import RealRooted.MultiplierSequence.ProperPosition

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The reciprocal rising-factorial weight at three. -/
def affineThetaLeftWeight (k : ℕ) : ℝ :=
  ((ascPochhammer ℝ k).eval 3)⁻¹

/-- The reciprocal rising-factorial weight at two. -/
def affineThetaRightWeight (k : ℕ) : ℝ :=
  ((ascPochhammer ℝ k).eval 2)⁻¹

/-- The affine theta source row: `2` at `0`, and
`(1 + X) ^ n * ((n + 3) + (2 * n + 4) * X)` at `n + 1`. -/
def affineThetaSource : ℕ → ℝ[X]
  | 0 => 2
  | n + 1 =>
      (1 + X) ^ n * (C (n + 3 : ℝ) + C (2 * n + 4 : ℝ) * X)

/-- The image of `affineThetaSource n` under the diagonal operator with weights
`affineThetaRightWeight`. -/
def affineThetaMiddle (n : ℕ) : ℝ[X] :=
  diagonalOperator affineThetaRightWeight (affineThetaSource n)

/-- The reversed double reciprocal-Pochhammer image of an affine theta row. -/
def affineThetaJensenPolynomial (n : ℕ) : ℝ[X] :=
  C ((n + 1).factorial / 2 : ℝ) *
    diagonalOperator affineThetaLeftWeight (affineThetaMiddle n).reverse

private theorem leftWeight_pos (k : ℕ) : 0 < affineThetaLeftWeight k := by
  exact inv_pos.mpr (ascPochhammer_pos k 3 (by norm_num))

private theorem rightWeight_pos (k : ℕ) : 0 < affineThetaRightWeight k := by
  exact inv_pos.mpr (ascPochhammer_pos k 2 (by norm_num))

private theorem leftWeight_multiplier : IsMultiplierSequence affineThetaLeftWeight := by
  exact (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
    (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 3))).1

private theorem rightWeight_multiplier : IsMultiplierSequence affineThetaRightWeight := by
  exact (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
    (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 2))).1

private theorem source_zero : affineThetaSource 0 = 2 := by
  rfl

private theorem source_succ_factor (n : ℕ) :
    affineThetaSource (n + 1) =
      (1 + X) ^ n * (C (n + 3 : ℝ) + C (2 * n + 4 : ℝ) * X) := by
  rfl

private theorem source_eq_theta (n : ℕ) :
    affineThetaSource n = C (n + 2 : ℝ) * (1 + X) ^ n + theta ((1 + X) ^ n) := by
  cases n with
  | zero =>
      simp only [affineThetaSource, pow_zero, theta, derivative_one, mul_zero, add_zero,
        Nat.cast_zero, zero_add]
      rw [mul_one]
      exact (map_ofNat (Polynomial.C : ℝ →+* ℝ[X]) 2).symm
  | succ n =>
      rw [source_succ_factor]
      unfold theta
      rw [derivative_pow]
      simp only [derivative_add, derivative_one, derivative_X, zero_add,
        Nat.cast_add, Nat.cast_one]
      rw [show n + 1 - 1 = n by lia, pow_succ]
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one]
      ring_nf

private theorem coeff_source (n j : ℕ) :
    (affineThetaSource n).coeff j = (n.choose j : ℝ) * (n + 2 + j : ℝ) := by
  rw [source_eq_theta, coeff_add, coeff_C_mul, coeff_theta,
    show (1 + X : ℝ[X]) = X + 1 by ring_nf, coeff_X_add_one_pow]
  ring_nf

private theorem source_interlaces_succ (n : ℕ) :
    Interlaces (affineThetaSource n) (affineThetaSource (n + 1)) := by
  cases n with
  | zero =>
      rw [source_zero, source_succ_factor]
      have h := interlaces_one_linear (p := (3 + 4 * X : ℝ[X]))
        (by compute_degree!)
      convert h.C_mul_both (c := (2 : ℝ)) (d := (1 : ℝ))
          (by norm_num) one_ne_zero using 1
      · rw [mul_one]
        exact (map_ofNat (Polynomial.C : ℝ →+* ℝ[X]) 2).symm
      · norm_num only [Nat.cast_zero, zero_add, zero_mul, pow_zero, one_mul,
          C_1]
        rw [show C (3 : ℝ) = 3 from map_ofNat C 3,
          show C (4 : ℝ) = 4 from map_ofNat C 4]
  | succ n =>
      rw [source_succ_factor n, source_succ_factor (n + 1)]
      have hlinear : Interlaces
          (C (n + 3 : ℝ) + C (2 * n + 4 : ℝ) * X)
          ((1 + X) * (C (n + 4 : ℝ) + C (2 * n + 6 : ℝ) * X)) := by
        have h := interlaces_linear_quadratic_of_roots_between
          (c := (2 * n + 6 : ℝ))
          (r := (-1 : ℝ))
          (s := -((n + 4 : ℝ) / (2 * n + 6 : ℝ)))
          (α := -((n + 3 : ℝ) / (2 * n + 4 : ℝ)))
          (by positivity) (by
            rw [neg_le_neg_iff, div_le_one (by positivity : (0 : ℝ) < 2 * n + 4)]
            have hn : (0 : ℝ) ≤ n := by positivity
            nlinarith) (by
            rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n + 6)
              (by positivity : (0 : ℝ) < 2 * n + 4)]
            have hn : (0 : ℝ) ≤ n := by positivity
            nlinarith)
        convert h.C_mul_both (c := (2 * n + 4 : ℝ))
            (d := (1 : ℝ)) (by positivity) one_ne_zero using 1 <;>
          apply Polynomial.funext <;> intro x <;>
          simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_one] <;>
          field_simp <;> ring_nf
      have hmul := hlinear.mul_both_of_splits ((Splits.X_add_C 1).pow n)
        (pow_ne_zero n (X_add_C_ne_zero 1))
      have hx : (1 + X : ℝ[X]) = X + C 1 := by rw [C_1]; ring_nf
      rw [hx]
      rw [C_1] at hmul ⊢
      convert hmul using 1
      · norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        ring_nf

private theorem source_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (affineThetaSource n) := by
  cases n with
  | zero =>
      intro k
      change 0 ≤ (2 : ℝ[X]).coeff k
      cases k <;> simp
  | succ n =>
      rw [source_succ_factor]
      exact ((hasNonnegCoeffs_one.add hasNonnegCoeffs_X).pow n).mul
        ((hasNonnegCoeffs_C (by positivity)).add
          ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X))

private theorem middle_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (affineThetaMiddle n) := by
  exact (source_hasNonnegCoeffs n).diagonalOperator
    (fun k => (rightWeight_pos k).le)

private theorem middle_coeff_zero (n : ℕ) : (affineThetaMiddle n).coeff 0 = n + 2 := by
  rw [affineThetaMiddle, coeff_diagonalOperator, affineThetaRightWeight]
  simp only [ascPochhammer_zero, eval_one, inv_one, one_mul]
  cases n with
  | zero => norm_num [affineThetaSource, coeff_zero_eq_eval_zero]
  | succ n =>
      rw [source_succ_factor]
      simp [coeff_zero_eq_eval_zero]
      ring_nf

private theorem source_natDegree (n : ℕ) : (affineThetaSource n).natDegree = n := by
  apply Nat.le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_source, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul]
  · apply le_natDegree_of_ne_zero
    rw [coeff_source]
    simp only [Nat.choose_self, Nat.cast_one, one_mul]
    positivity

private theorem middle_natDegree (n : ℕ) : (affineThetaMiddle n).natDegree = n := by
  apply Nat.le_antisymm
  · exact (natDegree_diagonalOperator_le _ _).trans_eq (source_natDegree n)
  · apply le_natDegree_of_ne_zero
    rw [affineThetaMiddle, coeff_diagonalOperator]
    change affineThetaRightWeight n * (affineThetaSource n).coeff n ≠ 0
    have hcoeff : (affineThetaSource n).coeff n ≠ 0 := by
      simpa only [leadingCoeff, source_natDegree] using
        (leadingCoeff_ne_zero.mpr (source_interlaces_succ n).2.1.1)
    exact mul_ne_zero (rightWeight_pos _).ne' hcoeff

private theorem ascPochhammer_eval_two (k : ℕ) :
    (ascPochhammer ℝ k).eval 2 = ((k + 1).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (k + 1)]
      push_cast
      ring_nf

private theorem two_mul_ascPochhammer_eval_three (k : ℕ) :
    2 * (ascPochhammer ℝ k).eval 3 = ((k + 2).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, Nat.factorial_succ (k + 2)]
      push_cast
      nlinarith

/-- Coefficients of the affine-theta Jensen model before factorial simplification. -/
theorem coeff_affineThetaJensenPolynomial_of_le (n k : ℕ) (hk : k ≤ n) :
    (affineThetaJensenPolynomial n).coeff k =
      (n + 1).factorial / 2 * affineThetaLeftWeight k * affineThetaRightWeight (n - k) *
        (n.choose (n - k) : ℝ) * (2 * n + 2 - k : ℝ) := by
  rw [affineThetaJensenPolynomial, coeff_C_mul, coeff_diagonalOperator, Polynomial.coeff_reverse,
    middle_natDegree, Polynomial.revAt_le hk, affineThetaMiddle, coeff_diagonalOperator,
    coeff_source]
  rw [Nat.cast_sub hk]
  ring_nf

/-- The affine-theta Jensen row has degree equal to its rank. -/
theorem natDegree_affineThetaJensenPolynomial (n : ℕ) :
    (affineThetaJensenPolynomial n).natDegree = n := by
  apply Nat.le_antisymm
  · exact (natDegree_C_mul_le _ _).trans
      ((natDegree_diagonalOperator_le _ _).trans
        ((Polynomial.reverse_natDegree_le _).trans_eq (middle_natDegree n)))
  · apply le_natDegree_of_ne_zero
    rw [coeff_affineThetaJensenPolynomial_of_le n n le_rfl]
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
    have hleft := leftWeight_pos n
    have hright := rightWeight_pos 0
    have hn : (0 : ℝ) ≤ n := by positivity
    have hlast : (0 : ℝ) < 2 * n + 2 - n := by nlinarith
    positivity

private theorem middle_isPF (n : ℕ) : IsPFPolynomial (affineThetaMiddle n) := by
  have hsplits := (source_interlaces_succ n).2.1.2
  have hsource : IsPFPolynomial (affineThetaSource n) :=
    IsPFPolynomial.of_realRooted_nonneg (source_hasNonnegCoeffs n) hsplits
  exact (isPFMultiplierSequence_inv_ascPochhammer
    (by norm_num : (0 : ℝ) < 2)).diagonalOperator_isPF hsource

private theorem middle_interlaces_succ (n : ℕ) :
    StrictInterl (affineThetaMiddle n) (affineThetaMiddle (n + 1)) := by
  exact rightWeight_multiplier.strictInterl_diagonalOperator_of_pos rightWeight_pos
    (source_interlaces_succ n).toStrictInterl

/-- Consecutive affine-theta Jensen rows are in directed proper position. -/
theorem affineThetaJensenPolynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (affineThetaJensenPolynomial n) (affineThetaJensenPolynomial (n + 1)) := by
  have hmiddleDegree (m : ℕ) :
      (affineThetaMiddle m).natDegree = (affineThetaSource m).natDegree := by
    apply Nat.le_antisymm
    · exact natDegree_diagonalOperator_le _ _
    · apply le_natDegree_of_ne_zero
      rw [affineThetaMiddle, coeff_diagonalOperator]
      exact mul_ne_zero (rightWeight_pos _).ne'
        (leadingCoeff_ne_zero.mpr (source_interlaces_succ m).2.1.1)
  have hreverse : Interlaces (affineThetaMiddle n).reverse (affineThetaMiddle (n + 1)).reverse :=
    interlaces_reverse_of_roots_neg
      ((middle_interlaces_succ n).toInterlaces (by
        rw [hmiddleDegree, hmiddleDegree]
        exact (source_interlaces_succ n).2.2.1))
      ((middle_isPF (n + 1)).roots_neg_of_coeff_zero_ne (by
        rw [middle_coeff_zero]
        positivity))
      ((middle_isPF n).roots_neg_of_coeff_zero_ne (by
        rw [middle_coeff_zero]
        positivity))
  have hdiag := leftWeight_multiplier.strictInterl_diagonalOperator_of_pos
    leftWeight_pos hreverse.toStrictInterl
  exact (hdiag.C_mul_left (by positivity)).C_mul_right (by positivity)

end RealRooted
