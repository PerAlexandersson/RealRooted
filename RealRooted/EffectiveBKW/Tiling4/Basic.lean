module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import RealRooted.EffectiveBKW.PairExpansion
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Complex.Basic
import RealRooted.EffectiveBKW.Domination
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!+# Recurrence polynomials for the four-row tiling family

We define the rows by the order-three recurrence associated with the rational
generating function `(1 - t z) / (1 - (1+t) z - (2t+t²) z² + (t²+t³) z³)`.
The definition includes the empty row and requires no tiling model.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.Tiling4

open Polynomial

/-- The recurrence polynomial for a rectangle with four rows and `n` columns. -/
noncomputable def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1 + 3 * X + X ^ 2
  | n + 3 => (1 + X) * polynomial (n + 2) +
      (2 * X + X ^ 2) * polynomial (n + 1) - (X ^ 2 + X ^ 3) * polynomial n

/-- The empty rectangle has weight one. -/
@[simp] theorem polynomial_zero : polynomial 0 = 1 := rfl

/-- No square fits in a one-column rectangle. -/
@[simp] theorem polynomial_one : polynomial 1 = 1 := rfl

/-- The first nonconstant row. -/
theorem polynomial_two : polynomial 2 = 1 + 3 * X + X ^ 2 := rfl

/-- The order-three recurrence, with indices beginning at zero. -/
theorem polynomial_add_three (n : ℕ) :
    polynomial (n + 3) = (1 + X) * polynomial (n + 2) +
      (2 * X + X ^ 2) * polynomial (n + 1) - (X ^ 2 + X ^ 3) * polynomial n := rfl

private theorem coeff_step (a b c : ℝ[X]) (n : ℕ) :
    (((1 + X) * c + (2 * X + X ^ 2) * b - (X ^ 2 + X ^ 3) * a).coeff
      (n + 3)) = c.coeff (n + 3) + c.coeff (n + 2) +
        2 * b.coeff (n + 2) + b.coeff (n + 1) -
        (a.coeff (n + 1) + a.coeff n) := by
  simp only [add_mul, one_mul, mul_assoc, coeff_add, coeff_sub,
    coeff_X_mul, coeff_ofNat_mul, coeff_X_pow_mul',
    show 2 ≤ n + 3 by lia, show 3 ≤ n + 3 by lia, ite_true,
    show n + 3 - 2 = n + 1 by lia, show n + 3 - 3 = n by lia]
  ring

/-- The recurrence gives the degree bound before accounting for parity cancellation. -/
theorem natDegree_polynomial_le (n : ℕ) : (polynomial n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | 2 => dsimp only [polynomial]; compute_degree
    | n + 3 =>
      have h0 := ih n (by lia)
      have h1 := ih (n + 1) (by lia)
      have h2 := ih (n + 2) (by lia)
      rw [polynomial_add_three]
      compute_degree
      lia

/-- The constant coefficient of every row is one. -/
@[simp] theorem coeff_polynomial_zero (n : ℕ) : (polynomial n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | 2 => norm_num [polynomial]
    | n + 3 => simpa [polynomial_add_three] using ih (n + 2) (by lia)

/-- No row is the zero polynomial. -/
theorem polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 := by
  intro h
  have := coeff_polynomial_zero n
  simp [h] at this

/-- The coefficient at the prospective top degree is the parity indicator. -/
theorem coeff_polynomial_self (n : ℕ) :
    (polynomial n).coeff n = (1 + (-1 : ℝ) ^ n) / 2 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => norm_num
    | 1 => norm_num [coeff_one]
    | 2 => norm_num [polynomial, coeff_one, coeff_X]
    | n + 3 =>
      rw [polynomial_add_three, coeff_step]
      have ha := natDegree_le_iff_coeff_eq_zero.mp (natDegree_polynomial_le n)
      have hb := natDegree_le_iff_coeff_eq_zero.mp (natDegree_polynomial_le (n + 1))
      have hc := natDegree_le_iff_coeff_eq_zero.mp (natDegree_polynomial_le (n + 2))
      rw [hc _ (by lia), hb _ (by lia), ha _ (by lia),
        ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
      simp only [pow_succ]
      ring

private theorem coeff_second_step (n : ℕ) :
    (polynomial (n + 4)).coeff (n + 3) =
      (polynomial (n + 3)).coeff (n + 3) + (polynomial (n + 3)).coeff (n + 2) +
        2 * (polynomial (n + 2)).coeff (n + 2) + (polynomial (n + 2)).coeff (n + 1) -
        ((polynomial (n + 1)).coeff (n + 1) + (polynomial (n + 1)).coeff n) := by
  have h := coeff_step (polynomial (n + 1)) (polynomial (n + 2))
    (polynomial (n + 3)) n
  rw [show n + 4 = (n + 1) + 3 by lia, polynomial_add_three]
  convert h using 1

/-- The next prospective coefficient, including the leading coefficient of each odd row. -/
theorem coeff_polynomial_succ (n : ℕ) :
    (polynomial (n + 1)).coeff n =
      (2 * (n : ℝ) ^ 2 + 10 * n + 9 - (2 * n + 1) * (-1 : ℝ) ^ n) / 8 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => norm_num
    | 1 => norm_num [polynomial, coeff_one]
    | 2 => norm_num [polynomial, add_mul, mul_add, mul_assoc, coeff_one, coeff_X]
    | n + 3 =>
      rw [show n + 3 + 1 = n + 4 by lia, coeff_second_step,
        coeff_polynomial_self, coeff_polynomial_self, coeff_polynomial_self,
        ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
      ring

/-- Every even row has top coefficient one. -/
@[simp] theorem coeff_polynomial_even (k : ℕ) :
    (polynomial (2 * k)).coeff (2 * k) = 1 := by
  rw [coeff_polynomial_self, pow_mul, neg_one_sq, one_pow]
  norm_num

/-- Every odd row loses its prospective top coefficient. -/
@[simp] theorem coeff_polynomial_odd (k : ℕ) :
    (polynomial (2 * k + 1)).coeff (2 * k + 1) = 0 := by
  rw [coeff_polynomial_self, pow_add, pow_mul, neg_one_sq, one_pow]
  norm_num

/-- The actual top coefficient of the odd row is a positive square. -/
theorem coeff_polynomial_odd_top (k : ℕ) :
    (polynomial (2 * k + 1)).coeff (2 * k) = ((k : ℝ) + 1) ^ 2 := by
  rw [coeff_polynomial_succ, pow_mul, neg_one_sq, one_pow]
  push_cast
  ring

/-- The even rows have degree equal to their index. -/
@[simp] theorem natDegree_polynomial_even (k : ℕ) :
    (polynomial (2 * k)).natDegree = 2 * k := by
  exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_polynomial_le _) (by simp)

/-- The odd rows have degree one less than their index. -/
@[simp] theorem natDegree_polynomial_odd (k : ℕ) :
    (polynomial (2 * k + 1)).natDegree = 2 * k := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_cases heq : j = 2 * k + 1
    · subst j
      exact coeff_polynomial_odd k
    · exact coeff_eq_zero_of_natDegree_lt ((natDegree_polynomial_le _).trans_lt (by lia))
  · rw [coeff_polynomial_odd_top]
    positivity

/-- The degree law for all rows, including indices zero and one. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = 2 * (n / 2) := by
  have hn : n % 2 < 2 := Nat.mod_lt n (by lia)
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by lia) with h | h
  · have heq : n = 2 * (n / 2) := by lia
    conv_lhs => rw [heq]
    exact natDegree_polynomial_even _
  · have heq : n = 2 * (n / 2) + 1 := by lia
    conv_lhs => rw [heq]
    exact natDegree_polynomial_odd _

/-- Every even row is monic. -/
theorem monic_polynomial_even (k : ℕ) : (polynomial (2 * k)).Monic := by
  unfold Monic leadingCoeff
  rw [natDegree_polynomial_even, coeff_polynomial_even]

/-- The odd row has leading coefficient `((n+1)/2)²`. -/
theorem leadingCoeff_polynomial_odd (k : ℕ) :
    (polynomial (2 * k + 1)).leadingCoeff = ((k : ℝ) + 1) ^ 2 := by
  rw [leadingCoeff, natDegree_polynomial_odd, coeff_polynomial_odd_top]

/-- Every row takes the value one at zero. -/
@[simp] theorem eval_polynomial_zero (n : ℕ) : (polynomial n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_polynomial_zero]

/-- The formal generating series, with coefficients in the polynomial ring. -/
noncomputable def rowSeries : PowerSeries ℝ[X] := PowerSeries.mk polynomial

/-- The cubic denominator as a formal series in the column variable. -/
noncomputable def denominator : PowerSeries ℝ[X] :=
  1 - PowerSeries.C (1 + X) * PowerSeries.X -
    PowerSeries.C (2 * X + X ^ 2) * PowerSeries.X ^ 2 +
    PowerSeries.C (X ^ 2 + X ^ 3) * PowerSeries.X ^ 3

/-- The linear numerator as a formal series in the column variable. -/
noncomputable def numerator : PowerSeries ℝ[X] := 1 - PowerSeries.C X * PowerSeries.X

/-- The recurrence proves the rational generating-function identity. -/
theorem denominator_mul_rowSeries : denominator * rowSeries = numerator := by
  apply PowerSeries.ext
  intro n
  simp only [denominator, numerator, sub_mul, add_mul, one_mul, mul_assoc,
    map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', rowSeries, PowerSeries.coeff_mk]
  match n with
  | 0 => simp
  | 1 => norm_num [PowerSeries.coeff_one, PowerSeries.coeff_X]
  | 2 =>
    norm_num [polynomial, PowerSeries.coeff_one, PowerSeries.coeff_X]
    ring
  | n + 3 =>
    rw [show n + 3 = (n + 2) + 1 by lia, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk]
    simp only [show 2 ≤ n + 2 + 1 by lia, show 3 ≤ n + 2 + 1 by lia, ite_true,
      show n + 3 - 2 = n + 1 by lia, show n + 3 - 3 = n by lia,
      PowerSeries.coeff_one, PowerSeries.coeff_X,
      show n + 3 ≠ 0 by lia, show n + 3 ≠ 1 by lia, ite_false,
      mul_zero, sub_zero, polynomial_add_three]
    ring

/-- The formal series equals the numerator times the canonical inverse denominator. -/
theorem rowSeries_eq_mul_invOfUnit :
    rowSeries = numerator * PowerSeries.invOfUnit denominator 1 := by
  have hinv : denominator * PowerSeries.invOfUnit denominator 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [denominator])
  calc
    rowSeries = rowSeries * (denominator * PowerSeries.invOfUnit denominator 1) := by
      rw [hinv, mul_one]
    _ = (denominator * rowSeries) * PowerSeries.invOfUnit denominator 1 := by ring
    _ = _ := by rw [denominator_mul_rowSeries]

/-- The reciprocal characteristic cubic of the recurrence. -/
def characteristic (t r : ℝ) : ℝ :=
  r ^ 3 - (1 + t) * r ^ 2 - (2 * t + t ^ 2) * r + t ^ 2 + t ^ 3

/-- The real part of the conjugate pair after removing the real root `r`. -/
noncomputable def pairReal (t r : ℝ) : ℝ := (1 + t - r) / 2

/-- The squared modulus of the conjugate pair. -/
def pairNormSq (t r : ℝ) : ℝ := r ^ 2 - (1 + t) * r - t * (2 + t)

/-- The squared imaginary part of the conjugate pair. -/
noncomputable def pairImagSq (t r : ℝ) : ℝ := pairNormSq t r - pairReal t r ^ 2

/-- The positive imaginary part on the pair region. -/
noncomputable def pairImag (t r : ℝ) : ℝ := Real.sqrt (pairImagSq t r)

/-- The upper-half-plane eigenvalue determined by a real root. -/
noncomputable def eigenvalue (t r : ℝ) : ℂ := ⟨pairReal t r, pairImag t r⟩

/-- The derivative of the reciprocal characteristic cubic at `r`. -/
def characteristicDeriv (t r : ℝ) : ℝ := 3 * r ^ 2 - 2 * (1 + t) * r - t * (2 + t)

/-- The discriminant identity after factoring off a real characteristic root. -/
theorem characteristicDeriv_sq_mul_pairImagSq {t r : ℝ} (hr : characteristic t r = 0) :
    characteristicDeriv t r ^ 2 * pairImagSq t r =
      -(t ^ 2 * (16 * t ^ 3 + 37 * t ^ 2 + 24 * t + 2)) := by
  dsimp [characteristic, characteristicDeriv, pairImagSq, pairNormSq, pairReal] at *
  linear_combination
    (27 * r ^ 3 - 27 * r ^ 2 * t - 27 * r ^ 2 - 27 * r * t ^ 2 - 54 * r * t -
      5 * t ^ 3 + 39 * t ^ 2 + 48 * t + 4) / 4 * hr

/-- A negative discriminant factor forces every real characteristic root to leave a nonreal pair. -/
theorem pairImagSq_pos {t r : ℝ} (hr : characteristic t r = 0) (ht : t ≠ 0)
    (hQ : 16 * t ^ 3 + 37 * t ^ 2 + 24 * t + 2 < 0) : 0 < pairImagSq t r := by
  have hpos : 0 < characteristicDeriv t r ^ 2 * pairImagSq t r := by
    rw [characteristicDeriv_sq_mul_pairImagSq hr]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht) hQ)
  exact pos_of_mul_pos_right hpos (sq_nonneg _)

/-- The coefficient of the real exponential mode. -/
noncomputable def thirdAmplitude (t r : ℝ) : ℝ :=
  r * (r - t) / characteristicDeriv t r

/-- The dominant amplitude, solved from the zeroth and first recurrence rows. -/
noncomputable def amplitude (t r : ℝ) : ℂ :=
  ⟨(1 - thirdAmplitude t r) / 2,
    ((1 - thirdAmplitude t r) * pairReal t r - 1 + thirdAmplitude t r * r) /
      (2 * pairImag t r)⟩

/-- Positivity of the squared imaginary part selects the upper half-plane. -/
theorem pairImag_pos {t r : ℝ} (h : 0 < pairImagSq t r) : 0 < pairImag t r :=
  Real.sqrt_pos.mpr h

/-- The chosen imaginary part has the prescribed square. -/
theorem pairImag_sq {t r : ℝ} (h : 0 ≤ pairImagSq t r) :
    pairImag t r ^ 2 = pairImagSq t r := Real.sq_sqrt h

/-- A genuine nonreal pair makes the real characteristic root simple. -/
theorem characteristicDeriv_pos {t r : ℝ} (hy : 0 < pairImagSq t r) :
    0 < characteristicDeriv t r := by
  have heq : characteristicDeriv t r = (r - pairReal t r) ^ 2 + pairImagSq t r := by
    dsimp [characteristicDeriv, pairReal, pairImagSq, pairNormSq]
    ring
  rw [heq]
  positivity

/-- The chosen complex eigenvalue has the prescribed squared modulus. -/
theorem norm_eigenvalue_sq {t r : ℝ} (h : 0 ≤ pairImagSq t r) :
    ‖eigenvalue t r‖ ^ 2 = pairNormSq t r := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  change pairReal t r * pairReal t r + pairImag t r * pairImag t r = _
  have hs := pairImag_sq h
  dsimp [pairImagSq] at hs
  nlinarith [hs]

private theorem amplitude_initial_zero (t r : ℝ) :
    2 * (amplitude t r).re + thirdAmplitude t r = 1 := by
  dsimp [amplitude]
  ring

private theorem amplitude_initial_one {t r : ℝ} (hy : 0 < pairImagSq t r) :
    2 * (amplitude t r * eigenvalue t r).re + thirdAmplitude t r * r = 1 := by
  have hne := (pairImag_pos hy).ne'
  dsimp [amplitude, eigenvalue]
  simp only [Complex.mul_re]
  field_simp
  ring

private theorem amplitude_initial_two {t r : ℝ} (hy : 0 < pairImagSq t r)
    (hd : characteristicDeriv t r ≠ 0) :
    2 * (amplitude t r * eigenvalue t r ^ 2).re + thirdAmplitude t r * r ^ 2 =
      1 + 3 * t + t ^ 2 := by
  have hne := (pairImag_pos hy).ne'
  have hs := pairImag_sq hy.le
  have hc : thirdAmplitude t r * characteristicDeriv t r = r * (r - t) := by
    exact div_mul_cancel₀ _ hd
  have heq : 2 * (amplitude t r * eigenvalue t r ^ 2).re +
      thirdAmplitude t r * r ^ 2 =
        (1 - thirdAmplitude t r) * (pairReal t r ^ 2 - pairImag t r ^ 2) -
          2 * pairReal t r * ((1 - thirdAmplitude t r) * pairReal t r - 1 +
            thirdAmplitude t r * r) + thirdAmplitude t r * r ^ 2 := by
    dsimp [amplitude, eigenvalue]
    simp only [pow_two, Complex.mul_re, Complex.mul_im]
    field_simp
    ring
  rw [heq, hs]
  dsimp [pairImagSq, pairNormSq, pairReal, characteristicDeriv] at *
  nlinarith [hc]

private theorem eigenvalue_quadratic {t r : ℝ} (hy : 0 ≤ pairImagSq t r) :
    eigenvalue t r ^ 2 - (2 * pairReal t r : ℂ) * eigenvalue t r +
      (pairNormSq t r : ℂ) = 0 := by
  have hs := pairImag_sq hy
  dsimp [pairImagSq] at hs
  apply Complex.ext
  · simp [eigenvalue, pow_two, Complex.mul_re, Complex.mul_im]
    nlinarith
  · simp [eigenvalue, pow_two, Complex.mul_im, Complex.mul_re]
    ring

private theorem characteristic_factor (t r : ℝ) (z : ℂ) :
    z ^ 3 - (1 + (t : ℂ)) * z ^ 2 - (2 * (t : ℂ) + (t : ℂ) ^ 2) * z +
        (t : ℂ) ^ 2 + (t : ℂ) ^ 3 =
      (z - (r : ℂ)) * (z ^ 2 - (2 * pairReal t r : ℂ) * z + (pairNormSq t r : ℂ)) +
        (characteristic t r : ℂ) := by
  dsimp [characteristic, pairReal, pairNormSq]
  push_cast
  ring

/-- The selected upper-half-plane number is a root of the reciprocal cubic. -/
theorem characteristic_eigenvalue {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 ≤ pairImagSq t r) :
    eigenvalue t r ^ 3 - (1 + (t : ℂ)) * eigenvalue t r ^ 2 -
        (2 * (t : ℂ) + (t : ℂ) ^ 2) * eigenvalue t r +
          (t : ℂ) ^ 2 + (t : ℂ) ^ 3 = 0 := by
  rw [characteristic_factor, eigenvalue_quadratic hy, hr]
  simp

private theorem real_mode_recurrence {t r : ℝ} (hr : characteristic t r = 0) (n : ℕ) :
    r ^ (n + 3) = (1 + t) * r ^ (n + 2) + (2 * t + t ^ 2) * r ^ (n + 1) -
      (t ^ 2 + t ^ 3) * r ^ n := by
  dsimp [characteristic] at hr
  simp only [pow_add, pow_one]
  linear_combination r ^ n * hr

private theorem pair_mode_recurrence {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 ≤ pairImagSq t r) (n : ℕ) :
    eigenvalue t r ^ (n + 3) = (1 + (t : ℂ)) * eigenvalue t r ^ (n + 2) +
      (2 * (t : ℂ) + (t : ℂ) ^ 2) * eigenvalue t r ^ (n + 1) -
        ((t : ℂ) ^ 2 + (t : ℂ) ^ 3) * eigenvalue t r ^ n := by
  have h := characteristic_eigenvalue hr hy
  simp only [pow_add, pow_one]
  linear_combination eigenvalue t r ^ n * h

private theorem pair_recurrence {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 ≤ pairImagSq t r) (n : ℕ) :
    2 * (amplitude t r * eigenvalue t r ^ (n + 3)).re + thirdAmplitude t r * r ^ (n + 3) =
      (1 + t) * (2 * (amplitude t r * eigenvalue t r ^ (n + 2)).re +
        thirdAmplitude t r * r ^ (n + 2)) +
      (2 * t + t ^ 2) * (2 * (amplitude t r * eigenvalue t r ^ (n + 1)).re +
        thirdAmplitude t r * r ^ (n + 1)) -
      (t ^ 2 + t ^ 3) * (2 * (amplitude t r * eigenvalue t r ^ n).re +
        thirdAmplitude t r * r ^ n) := by
  rw [pair_mode_recurrence hr hy n, real_mode_recurrence hr n]
  simp [mul_add, mul_sub, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- The exact single-remainder expansion, derived from the recurrence at every index.
The hypotheses describe one real characteristic root and a genuine nonreal pair;
they do not assume any root-count or real-rootedness conclusion. -/
theorem eval_polynomial_eq_pair {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 < pairImagSq t r) (n : ℕ) :
    (polynomial n).eval t =
      2 * (amplitude t r * eigenvalue t r ^ n).re + thirdAmplitude t r * r ^ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simpa using (amplitude_initial_zero t r).symm
    | 1 => simpa using (amplitude_initial_one hy).symm
    | 2 =>
      simpa [polynomial, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat] using
        (amplitude_initial_two hy (characteristicDeriv_pos hy).ne').symm
    | n + 3 =>
      rw [polynomial_add_three]
      simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
      rw [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
      exact (pair_recurrence hr hy.le n).symm

/-- The numerator of the rational generating function cannot cancel a nonreal mode. -/
theorem amplitude_ne_zero {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 < pairImagSq t r) (ht : t ≠ 0) : amplitude t r ≠ 0 := by
  intro hz
  have h0 := amplitude_initial_zero t r
  have h1 := amplitude_initial_one hy
  have h2 := amplitude_initial_two hy (characteristicDeriv_pos hy).ne'
  rw [hz] at h0 h1 h2
  simp only [zero_mul, Complex.zero_re, mul_zero, zero_add] at h0 h1 h2
  rw [h0, one_mul] at h1
  subst r
  have hp : t * (t + 3) = 0 := by nlinarith [h2]
  have ht3 : t = -3 := by
    rcases mul_eq_zero.mp hp with h | h
    · exact (ht h).elim
    · linarith
  subst t
  norm_num [characteristic] at hr

/-- The chosen eigenvalue varies continuously with any continuous real-root branch. -/
theorem continuousOn_eigenvalue {J : Set ℝ} {r : ℝ → ℝ}
    (hc : ContinuousOn r J) : ContinuousOn (fun t ↦ eigenvalue t (r t)) J := by
  have hx : ContinuousOn (fun t ↦ pairReal t (r t)) J := by
    dsimp [pairReal]
    fun_prop
  have hi : ContinuousOn (fun t ↦ pairImag t (r t)) J := by
    dsimp [pairImag, pairImagSq, pairNormSq, pairReal]
    fun_prop
  simp only [eigenvalue, Complex.mk_eq_add_mul_I]
  exact (Complex.continuous_ofReal.comp_continuousOn hx).add
    ((Complex.continuous_ofReal.comp_continuousOn hi).mul continuousOn_const)

private theorem continuousOn_thirdAmplitude {J : Set ℝ} {r : ℝ → ℝ}
    (hc : ContinuousOn r J) (hd : ∀ t ∈ J, characteristicDeriv t (r t) ≠ 0) :
    ContinuousOn (fun t ↦ thirdAmplitude t (r t)) J := by
  apply ContinuousOn.div
  · fun_prop
  · unfold characteristicDeriv
    fun_prop
  · exact hd

/-- The explicit amplitude is continuous wherever the pair is nonreal and
the real root is simple. -/
theorem continuousOn_amplitude {J : Set ℝ} {r : ℝ → ℝ}
    (hc : ContinuousOn r J) (hy : ∀ t ∈ J, 0 < pairImagSq t (r t))
    (hd : ∀ t ∈ J, characteristicDeriv t (r t) ≠ 0) :
    ContinuousOn (fun t ↦ amplitude t (r t)) J := by
  have hC := continuousOn_thirdAmplitude hc hd
  have hx : ContinuousOn (fun t ↦ pairReal t (r t)) J := by
    unfold pairReal
    fun_prop
  have hi : ContinuousOn (fun t ↦ pairImag t (r t)) J := by
    unfold pairImag pairImagSq pairNormSq pairReal
    fun_prop
  have him : ContinuousOn (fun t ↦
      ((1 - thirdAmplitude t (r t)) * pairReal t (r t) - 1 +
        thirdAmplitude t (r t) * r t) / (2 * pairImag t (r t))) J := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      exact mul_ne_zero (by norm_num) (pairImag_pos (hy t ht)).ne'
  simp only [amplitude, Complex.mk_eq_add_mul_I]
  have hre : ContinuousOn (fun t ↦ (1 - thirdAmplitude t (r t)) / 2) J := by
    fun_prop
  exact (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul continuousOn_const)

/-- A continuous real-root branch supplies the exact dominant-pair data.
The branch and the sign inequalities are explicit instance obligations. In particular,
this construction does not assert that such a branch has been certified on any given ray. -/
noncomputable def pairExpansion (J : Set ℝ) (r : ℝ → ℝ)
    (hc : ContinuousOn r J) (hr : ∀ t ∈ J, characteristic t (r t) = 0)
    (hy : ∀ t ∈ J, 0 < pairImagSq t (r t))
    (ht : ∀ t ∈ J, t ≠ 0) : PairExpansion polynomial J where
  first := 0
  lam := fun t ↦ eigenvalue t (r t)
  amplitude := fun t ↦ amplitude t (r t)
  rest := fun n t ↦ thirdAmplitude t (r t) * r t ^ n
  continuousOn_lam := continuousOn_eigenvalue hc
  continuousOn_amplitude := continuousOn_amplitude hc hy
    (fun t ht ↦ (characteristicDeriv_pos (hy t ht)).ne')
  im_pos := fun t ht ↦ pairImag_pos (hy t ht)
  amplitude_ne_zero := fun t ht' ↦ amplitude_ne_zero (hr t ht') (hy t ht') (ht t ht')
  expand := by
    intro n _ t ht
    exact eval_polynomial_eq_pair (hr t ht) (hy t ht) n

/-- The polynomial condition for the strict spectral gap. -/
def gapCondition (t r : ℝ) : ℝ := (1 + t) * r + t * (2 + t)

/-- The polynomial condition for positivity of the real amplitude. -/
def realCondition (t r : ℝ) : ℝ := characteristicDeriv t r - r * (r - t)

/-- The polynomial numerator controlling the sign of the imaginary amplitude. -/
def imagCondition (t r : ℝ) : ℝ :=
  realCondition t r * (1 + t - r) - 2 * characteristicDeriv t r + 2 * r ^ 2 * (r - t)

/-- The polynomial numerator of the strict amplitude-domination inequality. -/
noncomputable def dominationCondition (t r : ℝ) : ℝ :=
  (characteristicDeriv t r ^ 2 - 2 * r * (r - t) * characteristicDeriv t r) *
    (4 * pairImagSq t r) + imagCondition t r ^ 2

/-- The certified gap polynomial compares the moduli of the two modes. -/
theorem norm_real_lt_norm_eigenvalue {t r : ℝ} (hy : 0 ≤ pairImagSq t r)
    (hg : gapCondition t r < 0) : ‖(r : ℂ)‖ < ‖eigenvalue t r‖ := by
  have hn := norm_eigenvalue_sq hy
  dsimp [pairNormSq] at hn
  dsimp [gapCondition] at hg
  rw [Complex.norm_real, Real.norm_eq_abs]
  nlinarith [sq_abs r, norm_nonneg (eigenvalue t r), abs_nonneg r]

/-- The real-amplitude condition makes its real part strictly positive. -/
theorem thirdAmplitude_lt_one {t r : ℝ} (hy : 0 < pairImagSq t r)
    (hR : 0 < realCondition t r) : thirdAmplitude t r < 1 := by
  apply (div_lt_one (characteristicDeriv_pos hy)).mpr
  dsimp [realCondition] at hR
  linarith

private theorem dominationCondition_eq {t r : ℝ} (hy : 0 < pairImagSq t r) :
    dominationCondition t r = characteristicDeriv t r ^ 2 * (4 * pairImagSq t r) *
      (4 * ‖amplitude t r‖ ^ 2 - thirdAmplitude t r ^ 2) := by
  have hd := (characteristicDeriv_pos hy).ne'
  have hi := (pairImag_pos hy).ne'
  unfold dominationCondition
  rw [← pairImag_sq hy.le, Complex.sq_norm, Complex.normSq_apply]
  dsimp [amplitude, thirdAmplitude, imagCondition, realCondition, pairReal]
  field_simp
  ring

/-- The polynomial certificate implies strict domination of the third amplitude. -/
theorem abs_thirdAmplitude_lt_two_norm_amplitude {t r : ℝ} (hy : 0 < pairImagSq t r)
    (hK : 0 < dominationCondition t r) :
    |thirdAmplitude t r| < 2 * ‖amplitude t r‖ := by
  have hscale : 0 < characteristicDeriv t r ^ 2 * (4 * pairImagSq t r) := by
    have := characteristicDeriv_pos hy
    positivity
  rw [dominationCondition_eq hy] at hK
  have hpos : 0 < 4 * ‖amplitude t r‖ ^ 2 - thirdAmplitude t r ^ 2 :=
    (mul_pos_iff_of_pos_left hscale).mp hK
  nlinarith [sq_abs (thirdAmplitude t r), abs_nonneg (thirdAmplitude t r),
    norm_nonneg (amplitude t r)]

/-- The gap and domination polynomial inequalities give cutoff one on any certified branch. -/
theorem pairExpansion_dom {J : Set ℝ} {r : ℝ → ℝ}
    (hc : ContinuousOn r J) (hr : ∀ t ∈ J, characteristic t (r t) = 0)
    (hy : ∀ t ∈ J, 0 < pairImagSq t (r t))
    (ht₀ : ∀ t ∈ J, t ≠ 0)
    (hg : ∀ t ∈ J, gapCondition t (r t) < 0)
    (hK : ∀ t ∈ J, 0 < dominationCondition t (r t)) :
    (pairExpansion J r hc hr hy ht₀).Dom J 1 := by
  apply PairExpansion.dom_of_single_mode _
    (fun t ↦ (thirdAmplitude t (r t) : ℂ)) (fun t ↦ (r t : ℂ))
  · intro n t ht
    simp [pairExpansion, ← Complex.ofReal_pow]
  · intro t ht
    exact norm_real_lt_norm_eigenvalue (hy t ht).le (hg t ht)
  · intro t ht
    change ‖(thirdAmplitude t (r t) : ℂ)‖ ≤ 2 * ‖amplitude t (r t)‖
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_thirdAmplitude_lt_two_norm_amplitude (hy t ht) (hK t ht)).le
  · exact fun _ ht ↦ ht

/-- Every continuous real characteristic branch on a negative-discriminant domain
has an exact pair expansion. -/
noncomputable def pairExpansionOfDiscriminant (J : Set ℝ) (r : ℝ → ℝ)
    (hc : ContinuousOn r J) (hr : ∀ t ∈ J, characteristic t (r t) = 0)
    (ht : ∀ t ∈ J, t ≠ 0)
    (hQ : ∀ t ∈ J, 16 * t ^ 3 + 37 * t ^ 2 + 24 * t + 2 < 0) :
    PairExpansion polynomial J :=
  pairExpansion J r hc hr
    (fun t ht' ↦ pairImagSq_pos (hr t ht') (ht t ht') (hQ t ht'))
    ht

end RealRooted.EffectiveBKW.Tiling4
