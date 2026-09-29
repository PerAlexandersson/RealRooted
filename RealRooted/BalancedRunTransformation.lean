import RealRooted.BasisTransform
import RealRooted.MaWang.DerivativeStep
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.RootBounds
import RealRooted.ScalarNormalization

/-!
# Balanced run transformation

This file defines the balanced kernel

`U n m = choose n m ⁻¹ · ∑ k, choose m k · choose (n - m) k · X ^ k`

and the coefficientwise linear map sending `X ^ m` to `U n m`.  This is the
kernel transform used by the interlacing comparison for Motzkin ascent
polynomials.  Its reflection symmetry gives the equal central pair when the
rank is odd.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The normalized balanced run kernel `U_{n,m}`. -/
def balancedRunPolynomial (n m : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k
      (((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
        (Nat.choose n m : ℝ))

private def balancedRunCoeff (n m k : ℕ) : ℝ :=
  ((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
    (Nat.choose n m : ℝ)

/-- Coefficients of the balanced run kernel. -/
theorem coeff_balancedRunPolynomial (n m k : ℕ) (hm : m ≤ n) :
    (balancedRunPolynomial n m).coeff k =
      ((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
        (Nat.choose n m : ℝ) := by
  rw [balancedRunPolynomial, Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [coeff_monomial, hbk]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim
  · have hmk : m < k := lt_of_le_of_lt hm (Nat.lt_of_not_ge hk)
    have hsum :
        (∑ b ∈ Finset.range (n + 1),
          (monomial b
            (((Nat.choose m b : ℝ) *
                (Nat.choose (n - m) b : ℝ)) /
              (Nat.choose n m : ℝ))).coeff k) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [coeff_monomial]
      split_ifs with hbk
      · subst b
        exact (hk (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).elim
      · rfl
    rw [hsum, Nat.choose_eq_zero_of_lt hmk]
    simp

private theorem coeff_balancedRunPolynomial_eq_balancedRunCoeff
    (n m k : ℕ) (hm : m ≤ n) :
    (balancedRunPolynomial n m).coeff k = balancedRunCoeff n m k := by
  exact coeff_balancedRunPolynomial n m k hm

@[simp] theorem balancedRunPolynomial_zero (n : ℕ) :
    balancedRunPolynomial n 0 = 1 := by
  ext k
  rw [coeff_balancedRunPolynomial n 0 k (Nat.zero_le n)]
  cases k with
  | zero => simp
  | succ k => simp [Polynomial.coeff_one]

/-- Every balanced run kernel has nonnegative coefficients. -/
theorem hasNonnegCoeffs_balancedRunPolynomial (n m : ℕ) :
    HasNonnegCoeffs (balancedRunPolynomial n m) := by
  intro j
  rw [balancedRunPolynomial, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun k _ => by
    rw [coeff_monomial]
    split <;> positivity

/-- A balanced run kernel in its natural range is nonzero. -/
theorem balancedRunPolynomial_ne_zero (n m : ℕ) (hm : m ≤ n) :
    balancedRunPolynomial n m ≠ 0 := by
  have hcoeff : 0 < (balancedRunPolynomial n m).coeff 0 := by
    rw [coeff_balancedRunPolynomial n m 0 hm]
    have hchoose : 0 < (Nat.choose n m : ℝ) := by
      exact_mod_cast Nat.choose_pos hm
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    positivity
  intro hzero
  rw [hzero] at hcoeff
  simp at hcoeff

/-- Before the midpoint, the degree of `U_{n,m}` is exactly `m`. -/
theorem natDegree_balancedRunPolynomial_eq (n m : ℕ) (hmid : 2 * m ≤ n) :
    (balancedRunPolynomial n m).natDegree = m := by
  have hm : m ≤ n := by lia
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hmk
    rw [coeff_balancedRunPolynomial n m k hm,
      Nat.choose_eq_zero_of_lt hmk]
    simp
  · rw [coeff_balancedRunPolynomial n m m hm]
    have hmnm : m ≤ n - m := by lia
    have hleft : (Nat.choose m m : ℝ) ≠ 0 := by simp
    have hright : (Nat.choose (n - m) m : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero hmnm
    have hden : (Nat.choose n m : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hm
    exact div_ne_zero (mul_ne_zero hleft hright) hden

/-- Before the midpoint, every balanced run kernel has positive leading
coefficient. -/
theorem hasPosLeadingCoeff_balancedRunPolynomial
    (n m : ℕ) (hmid : 2 * m ≤ n) :
    HasPosLeadingCoeff (balancedRunPolynomial n m) := by
  rw [HasPosLeadingCoeff, leadingCoeff,
    natDegree_balancedRunPolynomial_eq n m hmid,
    coeff_balancedRunPolynomial n m m (by lia)]
  have hmnm : m ≤ n - m := by lia
  have hnum : 0 < (Nat.choose (n - m) m : ℝ) := by
    exact_mod_cast Nat.choose_pos hmnm
  have hden : 0 < (Nat.choose n m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by lia : m ≤ n)
  simp only [Nat.choose_self, Nat.cast_one, one_mul]
  exact div_pos hnum hden

private theorem balancedRunCoeff_recurrence
    (n m k : ℕ) (hmid : 2 * m + 1 < n)
    (hkpos : 0 < k) (hkm : k ≤ m + 1) :
    ((n - m : ℕ) : ℝ) ^ 2 * balancedRunCoeff n (m + 1) k =
      ((((n - m : ℕ) : ℝ) * (m + 1 : ℝ) +
          ((n - 2 * m - 1 : ℕ) : ℝ) * (k : ℝ)) *
        balancedRunCoeff n m k) +
      (((n - 2 * m - 1 : ℕ) : ℝ) *
          ((n + 1 - m - k : ℕ) : ℝ)) *
        balancedRunCoeff n m (k - 1) := by
  have hm : m ≤ n := by lia
  have hmsucc : m + 1 ≤ n := by lia
  have hnchoose : (Nat.choose n m : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hm
  have hnchoose_succ : (Nat.choose n (m + 1) : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero hmsucc
  have hdenNat := Nat.choose_succ_right_eq n m
  have hAupNat :
      Nat.choose (m + 1) k * (m + 1 - k) =
        Nat.choose m k * (m + 1) := by
    simpa only [mul_comm] using (Nat.choose_mul_succ_eq m k).symm
  have hBdownNat :
      (n - m) * Nat.choose (n - m - 1) k =
        Nat.choose (n - m) k * (n - m - k) := by
    simpa only [show n - m - 1 + 1 = n - m by lia, mul_comm] using
      Nat.choose_mul_succ_eq (n - m - 1) k
  have hBprevNat :
      Nat.choose (n - m) k * k =
        Nat.choose (n - m) (k - 1) * (n + 1 - m - k) := by
    simpa only [show k - 1 + 1 = k by lia,
      show n - m - (k - 1) = n + 1 - m - k by lia] using
        Nat.choose_succ_right_eq (n - m) (k - 1)
  have hPascalNat :
      Nat.choose (m + 1) k =
        Nat.choose m (k - 1) + Nat.choose m k := by
    simpa only [show k - 1 + 1 = k by lia] using
      Nat.choose_succ_succ' m (k - 1)
  have hden :
      (Nat.choose n (m + 1) : ℝ) * (m + 1 : ℝ) =
        (Nat.choose n m : ℝ) * ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hAup :
      (Nat.choose (m + 1) k : ℝ) * ((m + 1 - k : ℕ) : ℝ) =
        (Nat.choose m k : ℝ) * (m + 1 : ℝ) := by
    exact_mod_cast hAupNat
  have hBdown :
      ((n - m : ℕ) : ℝ) * (Nat.choose (n - m - 1) k : ℝ) =
        (Nat.choose (n - m) k : ℝ) *
          ((n - m - k : ℕ) : ℝ) := by
    exact_mod_cast hBdownNat
  have hBprev :
      (Nat.choose (n - m) k : ℝ) * (k : ℝ) =
        (Nat.choose (n - m) (k - 1) : ℝ) *
          ((n + 1 - m - k : ℕ) : ℝ) := by
    exact_mod_cast hBprevNat
  have hPascal :
      (Nat.choose (m + 1) k : ℝ) =
        (Nat.choose m (k - 1) : ℝ) + (Nat.choose m k : ℝ) := by
    exact_mod_cast hPascalNat
  have hdenRatio :
      ((n - m : ℕ) : ℝ) / (Nat.choose n (m + 1) : ℝ) =
        (m + 1 : ℝ) / (Nat.choose n m : ℝ) := by
    field_simp [hnchoose, hnchoose_succ]
    nlinarith [hden]
  have hnum :
      ((n - m : ℕ) : ℝ) * (m + 1 : ℝ) *
          (Nat.choose (m + 1) k : ℝ) *
            (Nat.choose (n - m - 1) k : ℝ) =
        (((n - m : ℕ) : ℝ) * (m + 1 : ℝ) +
            ((n - 2 * m - 1 : ℕ) : ℝ) * (k : ℝ)) *
              (Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ) +
          ((n - 2 * m - 1 : ℕ) : ℝ) *
            ((n + 1 - m - k : ℕ) : ℝ) *
              (Nat.choose m (k - 1) : ℝ) *
                (Nat.choose (n - m) (k - 1) : ℝ) := by
    norm_num only [Nat.cast_sub hm, Nat.cast_sub hkm,
      Nat.cast_sub (by lia : k ≤ n - m),
      Nat.cast_sub (by lia : 2 * m ≤ n),
      Nat.cast_sub (by lia : 1 ≤ n - 2 * m),
      Nat.cast_sub (by lia : m ≤ n + 1),
      Nat.cast_sub (by lia : k ≤ n + 1 - m), Nat.cast_add,
      Nat.cast_one, Nat.cast_mul] at hAup hBdown hBprev ⊢
    linear_combination
      (m + 1 : ℝ) * (Nat.choose (m + 1) k : ℝ) * hBdown +
      ((n : ℝ) - (m : ℝ)) * (Nat.choose (n - m) k : ℝ) * hAup +
      ((n : ℝ) - 2 * (m : ℝ) - 1) * (k : ℝ) *
        (Nat.choose (n - m) k : ℝ) * hPascal +
      ((n : ℝ) - 2 * (m : ℝ) - 1) *
        (Nat.choose m (k - 1) : ℝ) * hBprev
  simp only [balancedRunCoeff]
  rw [show n - (m + 1) = n - m - 1 by lia]
  calc
    ((n - m : ℕ) : ℝ) ^ 2 *
        ((Nat.choose (m + 1) k : ℝ) *
          (Nat.choose (n - m - 1) k : ℝ) /
            (Nat.choose n (m + 1) : ℝ)) =
      ((n - m : ℕ) : ℝ) *
        (((n - m : ℕ) : ℝ) /
          (Nat.choose n (m + 1) : ℝ)) *
        (Nat.choose (m + 1) k : ℝ) *
          (Nat.choose (n - m - 1) k : ℝ) := by ring
    _ = ((n - m : ℕ) : ℝ) *
        ((m + 1 : ℝ) / (Nat.choose n m : ℝ)) *
        (Nat.choose (m + 1) k : ℝ) *
          (Nat.choose (n - m - 1) k : ℝ) := by rw [hdenRatio]
    _ = _ := by
      field_simp [hnchoose]
      linear_combination hnum

private theorem coeff_X_mul_one_sub_X_mul_derivative
    (p : ℝ[X]) (k : ℕ) :
    (X * (1 - X) * p.derivative).coeff k =
      (k : ℝ) * p.coeff k -
        ((k - 1 : ℕ) : ℝ) * p.coeff (k - 1) := by
  have hpoly :
      X * (1 - X) * p.derivative =
        X * p.derivative - X * (X * p.derivative) := by ring
  rw [hpoly, coeff_sub]
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero => simp [coeff_X_mul, coeff_derivative]
      | succ k =>
          simp [coeff_X_mul, coeff_derivative]
          ring

/-- Denominator-cleared differential recurrence for consecutive balanced run
kernels strictly before the midpoint. -/
theorem balancedRunPolynomial_differential_recurrence
    (n m : ℕ) (hmid : 2 * m + 1 < n) :
    C (((n - m : ℕ) : ℝ) ^ 2) * balancedRunPolynomial n (m + 1) =
      C (((n - m : ℕ) : ℝ) * (m + 1 : ℝ)) *
          balancedRunPolynomial n m +
        C (((n - m : ℕ) : ℝ) *
            ((n - 2 * m - 1 : ℕ) : ℝ)) *
          (X * balancedRunPolynomial n m) +
        C ((n - 2 * m - 1 : ℕ) : ℝ) *
          (X * (1 - X) * (balancedRunPolynomial n m).derivative) := by
  ext k
  have hm : m ≤ n := by lia
  have hmsucc : m + 1 ≤ n := by lia
  by_cases hk0 : k = 0
  · subst k
    simp only [coeff_C_mul, coeff_add, coeff_X_mul_zero,
      coeff_X_mul_one_sub_X_mul_derivative,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n (m + 1) 0 hmsucc,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n m 0 hm]
    simp only [balancedRunCoeff, Nat.choose_zero_right, Nat.cast_one,
      one_mul, Nat.zero_sub, Nat.cast_zero, zero_mul, mul_zero, sub_zero,
      add_zero]
    have hnchoose : (Nat.choose n m : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero hm
    have hnchoose_succ : (Nat.choose n (m + 1) : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero hmsucc
    have hden :
        (Nat.choose n (m + 1) : ℝ) * (m + 1 : ℝ) =
          (Nat.choose n m : ℝ) * ((n - m : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq n m
    field_simp [hnchoose, hnchoose_succ]
    nlinarith [hden]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hX :
      (X * balancedRunPolynomial n m).coeff k =
        (balancedRunPolynomial n m).coeff (k - 1) := by
    simpa [Nat.sub_add_cancel (by lia : 1 ≤ k)] using
      Polynomial.coeff_X_mul (balancedRunPolynomial n m) (k - 1)
  by_cases hkm : k ≤ m + 1
  · rw [coeff_C_mul, coeff_add, coeff_add, coeff_C_mul,
      coeff_C_mul, coeff_C_mul, hX,
      coeff_X_mul_one_sub_X_mul_derivative,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n (m + 1) k hmsucc,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n m k hm,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n m (k - 1) hm]
    have hrec := balancedRunCoeff_recurrence n m k hmid hkpos hkm
    simp only [Nat.cast_sub hm,
      Nat.cast_sub (by lia : 2 * m ≤ n),
      Nat.cast_sub (by lia : 1 ≤ n - 2 * m),
      Nat.cast_sub (by lia : m ≤ n + 1),
      Nat.cast_sub (by lia : k ≤ n + 1 - m),
      Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_add, Nat.cast_one,
      Nat.cast_mul] at hrec ⊢
    linear_combination hrec
  · have hkm' : m + 1 < k := Nat.lt_of_not_ge hkm
    rw [coeff_C_mul, coeff_add, coeff_add, coeff_C_mul,
      coeff_C_mul, coeff_C_mul, hX,
      coeff_X_mul_one_sub_X_mul_derivative,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n (m + 1) k hmsucc,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n m k hm,
      coeff_balancedRunPolynomial_eq_balancedRunCoeff n m (k - 1) hm]
    simp [balancedRunCoeff,
      Nat.choose_eq_zero_of_lt hkm',
      Nat.choose_eq_zero_of_lt (by lia : m < k),
      Nat.choose_eq_zero_of_lt (by lia : m < k - 1)]

/-- Normalized differential recurrence for consecutive balanced run kernels
strictly before the midpoint. -/
theorem balancedRunPolynomial_differential_recurrence_normalized
    (n m : ℕ) (hmid : 2 * m + 1 < n) :
    balancedRunPolynomial n (m + 1) =
      (C ((m + 1 : ℝ) / ((n - m : ℕ) : ℝ)) +
          C (((n - 2 * m - 1 : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) * X) *
          balancedRunPolynomial n m +
        (C (((n - 2 * m - 1 : ℕ) : ℝ) /
            (((n - m : ℕ) : ℝ) ^ 2)) * X * (1 - X)) *
          (balancedRunPolynomial n m).derivative := by
  have hnm_nat : 0 < n - m := by lia
  have hnm : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hnm_nat
  have hraw := balancedRunPolynomial_differential_recurrence n m hmid
  let d : ℝ := ((n - m : ℕ) : ℝ) ^ 2
  let b : ℝ := ((n - 2 * m - 1 : ℕ) : ℝ)
  let c : ℝ := b / d
  let A : ℝ[X] :=
    (C ((m + 1 : ℝ) / ((n - m : ℕ) : ℝ)) +
      C (((n - 2 * m - 1 : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) * X) *
        balancedRunPolynomial n m
  let Q : ℝ[X] := X * (1 - X) * (balancedRunPolynomial n m).derivative
  have hd : d ≠ 0 := pow_ne_zero 2 hnm.ne'
  have hbc : d⁻¹ * b = c := by
    dsimp [d, b, c]
    field_simp [hnm.ne']
  have hsplit :
      C d * balancedRunPolynomial n (m + 1) = C d * A + C b * Q := by
    have hconst :
        d * ((m + 1 : ℝ) / ((n - m : ℕ) : ℝ)) =
          ((n - m : ℕ) : ℝ) * (m + 1 : ℝ) := by
      dsimp [d]
      field_simp [hnm.ne']
    have hlinear :
        d * (((n - 2 * m - 1 : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) =
          ((n - m : ℕ) : ℝ) * ((n - 2 * m - 1 : ℕ) : ℝ) := by
      dsimp [d]
      field_simp [hnm.ne']
    have hCconst :
        C d * C ((m + 1 : ℝ) / ((n - m : ℕ) : ℝ)) =
          C (((n - m : ℕ) : ℝ) * (m + 1 : ℝ)) := by
      rw [← C_mul]
      exact congrArg C hconst
    have hClinear :
        C d * C (((n - 2 * m - 1 : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) =
          C (((n - m : ℕ) : ℝ) * ((n - 2 * m - 1 : ℕ) : ℝ)) := by
      rw [← C_mul]
      exact congrArg C hlinear
    dsimp only [A, Q]
    rw [hraw, ← hCconst, ← hClinear]
    ring
  simpa [d, b, c, A, Q, mul_assoc] using
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul hd hbc hsplit

/-- Consecutive balanced run kernels strictly interlace before the midpoint. -/
theorem strictInterl_balancedRunPolynomial_succ
    (n m : ℕ) (hmid : 2 * m + 1 < n) :
    StrictInterl (balancedRunPolynomial n m)
      (balancedRunPolynomial n (m + 1)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm0 : m = 0
      · subst m
        rw [balancedRunPolynomial_zero]
        exact (interlaces_one_linear
          (natDegree_balancedRunPolynomial_eq n 1 (by lia))).toStrictInterl
      have hmpos_nat : 0 < m := Nat.pos_of_ne_zero hm0
      have hmdeg : (balancedRunPolynomial n m).natDegree = m :=
        natDegree_balancedRunPolynomial_eq n m (by lia)
      have hsuccdeg :
          (balancedRunPolynomial n (m + 1)).natDegree = m + 1 :=
        natDegree_balancedRunPolynomial_eq n (m + 1) (by lia)
      have hmpos : HasPosLeadingCoeff (balancedRunPolynomial n m) :=
        hasPosLeadingCoeff_balancedRunPolynomial n m (by lia)
      have hsuccpos :
          HasPosLeadingCoeff (balancedRunPolynomial n (m + 1)) :=
        hasPosLeadingCoeff_balancedRunPolynomial n (m + 1) (by lia)
      have hmsplits : (balancedRunPolynomial n m).Splits := by
        have hprev := ih (m - 1) (by lia) (by lia)
        simpa [Nat.sub_add_cancel (by lia : 1 ≤ m)] using hprev.2.1.2
      let u : ℝ[X] :=
        C ((m + 1 : ℝ) / ((n - m : ℕ) : ℝ)) +
          C (((n - 2 * m - 1 : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) * X
      let c : ℝ :=
        ((n - 2 * m - 1 : ℕ) : ℝ) / (((n - m : ℕ) : ℝ) ^ 2)
      let v : ℝ[X] := C c * X * (1 - X)
      have hrec :
          balancedRunPolynomial n (m + 1) =
            u * balancedRunPolynomial n m +
              v * (balancedRunPolynomial n m).derivative := by
        simpa [u, c, v, mul_assoc] using
          balancedRunPolynomial_differential_recurrence_normalized n m hmid
      have hc : 0 ≤ c := by
        dsimp [c]
        positivity
      have hv : ∀ r, (balancedRunPolynomial n m).IsRoot r → v.eval r ≤ 0 := by
        intro r hr
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_of_realrooted_of_nonneg_coeffs
            ⟨hmpos.ne_zero, hmsplits⟩
            (hasNonnegCoeffs_balancedRunPolynomial n m) r hr
        dsimp [v]
        exact eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos hc hr_nonpos
      have hstep :
          StrictInterl (balancedRunPolynomial n m)
            (u * balancedRunPolynomial n m +
              v * (balancedRunPolynomial n m).derivative) :=
        strictInterl_mw_derivative_of_nonpos_of_pos_natDegree
          hmsplits (by rw [hmdeg]; exact hmpos_nat)
          (by rw [← hrec, hmdeg, hsuccdeg]; lia)
          (by rw [← hrec, hmdeg, hsuccdeg])
          (by rw [← hrec]; exact hsuccpos) hmpos hv
      rw [← hrec] at hstep
      exact hstep

/-- The balanced kernel is invariant under complementing its basis index. -/
theorem balancedRunPolynomial_reflection (n m : ℕ) (hm : m ≤ n) :
    balancedRunPolynomial n m = balancedRunPolynomial n (n - m) := by
  ext k
  rw [coeff_balancedRunPolynomial n m k hm,
    coeff_balancedRunPolynomial n (n - m) k (Nat.sub_le n m),
    Nat.sub_sub_self hm, Nat.choose_symm hm]
  ring

/-- At odd rank, the two central balanced kernels coincide. -/
theorem balancedRunPolynomial_odd_central (r : ℕ) :
    balancedRunPolynomial (2 * r + 1) (r + 1) =
      balancedRunPolynomial (2 * r + 1) r := by
  have hreflect := balancedRunPolynomial_reflection (2 * r + 1) r (by lia)
  have hindex : 2 * r + 1 - r = r + 1 := by lia
  rw [hindex] at hreflect
  exact hreflect.symm

/-- Uniform forward orientation for every adjacent balanced run kernel through
the midpoint.  When `n = 2 * m + 1`, this is the allowed equal central pair. -/
theorem strictInterl_balancedRunPolynomial_succ_of_two_mul_add_one_le
    (n m : ℕ) (hmid : 2 * m + 1 ≤ n) :
    StrictInterl (balancedRunPolynomial n m)
      (balancedRunPolynomial n (m + 1)) := by
  by_cases hstrict : 2 * m + 1 < n
  · exact strictInterl_balancedRunPolynomial_succ n m hstrict
  have heq : 2 * m + 1 = n := by lia
  have hcentral :
      balancedRunPolynomial n (m + 1) = balancedRunPolynomial n m := by
    subst n
    exact balancedRunPolynomial_odd_central m
  rw [hcentral]
  have hne : balancedRunPolynomial n m ≠ 0 :=
    balancedRunPolynomial_ne_zero n m (by lia)
  have hsplits : (balancedRunPolynomial n m).Splits := by
    by_cases hm0 : m = 0
    · subst m
      simp
    have hprev := strictInterl_balancedRunPolynomial_succ n (m - 1) (by lia)
    simpa [Nat.sub_add_cancel (by lia : 1 ≤ m)] using hprev.2.1.2
  exact StrictInterl.refl hne hsplits

/-- The fixed-rank balanced run basis transform. -/
def balancedRunTransform (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (balancedRunPolynomial n) p

@[simp] theorem balancedRunTransform_X_pow (n m : ℕ) :
    balancedRunTransform n (X ^ m) = balancedRunPolynomial n m := by
  simp [balancedRunTransform]

@[simp] theorem balancedRunTransform_zero (n : ℕ) :
    balancedRunTransform n 0 = 0 := by
  simp [balancedRunTransform]

theorem balancedRunTransform_add (n : ℕ) (p q : ℝ[X]) :
    balancedRunTransform n (p + q) =
      balancedRunTransform n p + balancedRunTransform n q := by
  simp [balancedRunTransform, Polynomial.basisTransform_add]

theorem balancedRunTransform_smul (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    balancedRunTransform n (a • p) = a • balancedRunTransform n p := by
  change Polynomial.basisTransform (balancedRunPolynomial n) (a • p) =
    a • Polynomial.basisTransform (balancedRunPolynomial n) p
  rw [Polynomial.basisTransform_smul, Polynomial.smul_eq_C_mul]

/-- The balanced run transform as a real-linear map. -/
def balancedRunTransformLinearMap (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := balancedRunTransform n
  map_add' := balancedRunTransform_add n
  map_smul' := balancedRunTransform_smul n

@[simp] theorem balancedRunTransformLinearMap_apply (n : ℕ) (p : ℝ[X]) :
    balancedRunTransformLinearMap n p = balancedRunTransform n p := rfl

/-- The balanced run transform preserves coefficientwise nonnegativity. -/
theorem HasNonnegCoeffs.balancedRunTransform {n : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (balancedRunTransform n p) :=
  hp.basisTransform (hasNonnegCoeffs_balancedRunPolynomial n)

end RealRooted
