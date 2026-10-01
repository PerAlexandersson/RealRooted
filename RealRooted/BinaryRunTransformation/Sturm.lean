import RealRooted.BinaryRunTransformation.Coefficients
import RealRooted.MaWang.DerivativeStep
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.RootBounds
import RealRooted.ScalarNormalization

/-!
# Sturm chain of binary-run basis images

This file proves the differential recurrence for consecutive binary-run basis
polynomials.  It is the local input for their strict interlacing up to the
midpoint; reflection then reverses the chain.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

private def binaryRunCoeff (n m k : ℕ) : ℝ :=
  ((Nat.choose (m - 1) (k - 1) : ℝ) *
      (Nat.choose (n + 1 - m) k : ℝ)) /
    (Nat.choose n m : ℝ)

private theorem coeff_binaryRunPolynomial_of_pos (n m k : ℕ)
    (hm0 : 0 < m) (hk0 : 0 < k) :
    (binaryRunPolynomial n m).coeff k = binaryRunCoeff n m k := by
  rw [coeff_binaryRunPolynomial_of_pos_formula n m k hm0 hk0]
  rfl

private theorem binaryRunCoeff_recurrence (n m k : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) :
    ((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ) *
        binaryRunCoeff n (m + 1) k =
      (((m : ℝ) * ((n + 1 - m : ℕ) : ℝ) +
          ((n - 2 * m : ℕ) : ℝ) * (k : ℝ)) * binaryRunCoeff n m k) +
        (((n - 2 * m : ℕ) : ℝ) * ((n + 2 - m - k : ℕ) : ℝ)) *
          binaryRunCoeff n m (k - 1) := by
  have hmn : m < n := by lia
  have hmle : m ≤ n := hmn.le
  have hmsucc : m + 1 ≤ n := by lia
  have hnchoose : (Nat.choose n m : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hmle
  have hnchoose_succ : (Nat.choose n (m + 1) : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero hmsucc
  have hdenNat := Nat.choose_succ_right_eq n m
  have hleftNat :
      Nat.choose (m - 1) (k - 1) * (k - 1) =
        Nat.choose (m - 1) (k - 2) * (m + 1 - k) := by
    simpa only [show k - 2 + 1 = k - 1 by lia,
      show m - 1 - (k - 2) = m + 1 - k by lia] using
        Nat.choose_succ_right_eq (m - 1) (k - 2)
  have hrightNat :
      Nat.choose (n + 1 - m) k * k =
        Nat.choose (n + 1 - m) (k - 1) * (n + 2 - m - k) := by
    simpa only [show k - 1 + 1 = k by lia,
      show n + 1 - m - (k - 1) = n + 2 - m - k by lia] using
        Nat.choose_succ_right_eq (n + 1 - m) (k - 1)
  have hpascalLeftNat :
      Nat.choose m (k - 1) =
        Nat.choose (m - 1) (k - 2) + Nat.choose (m - 1) (k - 1) := by
    simpa only [show m - 1 + 1 = m by lia,
      show k - 2 + 1 = k - 1 by lia] using
        Nat.choose_succ_succ' (m - 1) (k - 2)
  have hdownNat :
      (n + 1 - m) * Nat.choose (n - m) k =
        Nat.choose (n + 1 - m) k * (n + 1 - m - k) := by
    simpa only [show n - m + 1 = n + 1 - m by lia, mul_comm] using
      Nat.choose_mul_succ_eq (n - m) k
  have hden :
      (Nat.choose n (m + 1) : ℝ) * (m + 1 : ℝ) =
        (Nat.choose n m : ℝ) * ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hleft :
      (Nat.choose (m - 1) (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) =
        (Nat.choose (m - 1) (k - 2) : ℝ) *
          ((m + 1 - k : ℕ) : ℝ) := by
    exact_mod_cast hleftNat
  have hright :
      (Nat.choose (n + 1 - m) k : ℝ) * (k : ℝ) =
        (Nat.choose (n + 1 - m) (k - 1) : ℝ) *
          ((n + 2 - m - k : ℕ) : ℝ) := by
    exact_mod_cast hrightNat
  have hpascalLeft :
      (Nat.choose m (k - 1) : ℝ) =
        (Nat.choose (m - 1) (k - 2) : ℝ) +
          (Nat.choose (m - 1) (k - 1) : ℝ) := by
    exact_mod_cast hpascalLeftNat
  have hdown :
      ((n + 1 - m : ℕ) : ℝ) * (Nat.choose (n - m) k : ℝ) =
        (Nat.choose (n + 1 - m) k : ℝ) *
          ((n + 1 - m - k : ℕ) : ℝ) := by
    exact_mod_cast hdownNat
  have hdenRatio :
      ((n - m : ℕ) : ℝ) / (Nat.choose n (m + 1) : ℝ) =
        ((m + 1 : ℕ) : ℝ) / (Nat.choose n m : ℝ) := by
    field_simp [hnchoose, hnchoose_succ]
    norm_num only [Nat.cast_add, Nat.cast_one] at hden ⊢
    linarith [hden]
  simp only [binaryRunCoeff]
  rw [show m + 1 - 1 = m by lia, show k - 1 - 1 = k - 2 by lia,
    show n + 1 - (m + 1) = n - m by lia]
  calc
    ((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ) *
        ((Nat.choose m (k - 1) : ℝ) * (Nat.choose (n - m) k : ℝ) /
          (Nat.choose n (m + 1) : ℝ)) =
      ((n + 1 - m : ℕ) : ℝ) *
        (((n - m : ℕ) : ℝ) / (Nat.choose n (m + 1) : ℝ)) *
          (Nat.choose m (k - 1) : ℝ) * (Nat.choose (n - m) k : ℝ) := by ring
    _ = ((n + 1 - m : ℕ) : ℝ) *
        (((m + 1 : ℕ) : ℝ) / (Nat.choose n m : ℝ)) *
          (Nat.choose m (k - 1) : ℝ) * (Nat.choose (n - m) k : ℝ) := by
      rw [hdenRatio]
    _ = (((m : ℝ) * ((n + 1 - m : ℕ) : ℝ) +
          ((n - 2 * m : ℕ) : ℝ) * (k : ℝ)) *
            ((Nat.choose (m - 1) (k - 1) : ℝ) *
              (Nat.choose (n + 1 - m) k : ℝ) / (Nat.choose n m : ℝ))) +
        (((n - 2 * m : ℕ) : ℝ) * ((n + 2 - m - k : ℕ) : ℝ)) *
          ((Nat.choose (m - 1) (k - 2) : ℝ) *
            (Nat.choose (n + 1 - m) (k - 1) : ℝ) /
              (Nat.choose n m : ℝ)) := by
      rw [hpascalLeft]
      field_simp [hnchoose]
      rw [Nat.cast_sub (by lia : 1 ≤ k),
        Nat.cast_sub (by lia : k ≤ m + 1)] at hleft
      rw [Nat.cast_sub (by lia : k ≤ n + 2 - m),
        Nat.cast_sub (by lia : m ≤ n + 2)] at hright
      rw [Nat.cast_sub (by lia : m ≤ n + 1),
        Nat.cast_sub (by lia : k ≤ n + 1 - m),
        Nat.cast_sub (by lia : m ≤ n + 1)] at hdown
      rw [Nat.cast_sub (by lia : m ≤ n + 1),
        Nat.cast_sub (by lia : 2 * m ≤ n),
        Nat.cast_sub (by lia : k ≤ n + 2 - m),
        Nat.cast_sub (by lia : m ≤ n + 2)]
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
        at hleft hright hdown ⊢
      linear_combination
        -((n : ℝ) + 1 - (m : ℝ)) *
            (Nat.choose (n + 1 - m) k : ℝ) * hleft +
          ((n : ℝ) - 2 * (m : ℝ)) *
            (Nat.choose (m - 1) (k - 2) : ℝ) * hright +
          ((m : ℝ) + 1) *
            ((Nat.choose (m - 1) (k - 2) : ℝ) +
              (Nat.choose (m - 1) (k - 1) : ℝ)) * hdown

private theorem coeff_X_mul_one_sub_X_mul_derivative (p : ℝ[X]) (k : ℕ) :
    (X * (1 - X) * p.derivative).coeff k =
      (k : ℝ) * p.coeff k - ((k - 1 : ℕ) : ℝ) * p.coeff (k - 1) := by
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

/-- Denominator-cleared differential recurrence for consecutive binary-run
basis images before the midpoint. -/
theorem binaryRunPolynomial_differential_recurrence (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) :
    C (((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ)) *
        binaryRunPolynomial n (m + 1) =
      C ((m : ℝ) * ((n + 1 - m : ℕ) : ℝ)) * binaryRunPolynomial n m +
        C (((n - 2 * m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ)) *
          (X * binaryRunPolynomial n m) +
        C ((n - 2 * m : ℕ) : ℝ) *
          (X * (1 - X) * (binaryRunPolynomial n m).derivative) := by
  ext k
  have hmle : m ≤ n := by lia
  have hmsucc : m + 1 ≤ n := by lia
  by_cases hk0 : k = 0
  · subst k
    simp [coeff_zero_binaryRunPolynomial_of_pos n m hm0,
      coeff_zero_binaryRunPolynomial_of_pos n (m + 1) (by lia)]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  by_cases hk1 : k = 1
  · subst k
    rw [coeff_C_mul, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_C_mul, coeff_X_mul,
      coeff_binaryRunPolynomial_of_pos n (m + 1) 1 (by lia) (by lia),
      coeff_binaryRunPolynomial_of_pos n m 1 hm0 (by lia),
      coeff_X_mul_one_sub_X_mul_derivative]
    rw [coeff_zero_binaryRunPolynomial_of_pos n m hm0,
      coeff_binaryRunPolynomial_of_pos n m 1 hm0 (by lia)]
    simp only [binaryRunCoeff, Nat.choose_zero_right, Nat.choose_one_right,
      mul_zero, add_zero, Nat.cast_one, one_mul, tsub_self,
      CharP.cast_eq_zero, sub_zero]
    have hnchoose : (Nat.choose n m : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hmle
    have hnchoose_succ : (Nat.choose n (m + 1) : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero hmsucc
    have hden := Nat.cast_choose_succ_right_eq (R := ℝ) n m
    rw [Nat.cast_sub (by lia : m ≤ n),
      Nat.cast_sub (by lia : m + 1 ≤ n + 1),
      Nat.cast_sub (by lia : m ≤ n + 1),
      Nat.cast_sub (by lia : 2 * m ≤ n)]
    rw [Nat.cast_sub hmle] at hden
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at hden ⊢
    field_simp [hnchoose, hnchoose_succ]
    linear_combination
      -((n : ℝ) + 1 - (m : ℝ)) * ((n : ℝ) - (m : ℝ)) * hden
  by_cases hkm : k ≤ m + 1
  · have hk2 : 2 ≤ k := by lia
    have hX :
        (X * binaryRunPolynomial n m).coeff k =
          (binaryRunPolynomial n m).coeff (k - 1) := by
      simpa [Nat.sub_add_cancel (by lia : 1 ≤ k)] using
        Polynomial.coeff_X_mul (binaryRunPolynomial n m) (k - 1)
    rw [coeff_C_mul, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_C_mul, hX,
      coeff_binaryRunPolynomial_of_pos n (m + 1) k (by lia) hkpos,
      coeff_binaryRunPolynomial_of_pos n m k hm0 hkpos,
      coeff_X_mul_one_sub_X_mul_derivative]
    rw [coeff_binaryRunPolynomial_of_pos n m (k - 1) hm0 (by lia),
      coeff_binaryRunPolynomial_of_pos n m k hm0 hkpos]
    have hrec := binaryRunCoeff_recurrence n m k hm0 hmid hk2 hkm
    simp only [Nat.cast_sub hmle, Nat.cast_sub (by lia : m ≤ n + 1),
      Nat.cast_sub (by lia : 2 * m ≤ n), Nat.cast_sub (by lia : 1 ≤ k),
      Nat.cast_sub (by lia : k ≤ n + 2 - m),
      Nat.cast_sub (by lia : m ≤ n + 2), Nat.cast_add, Nat.cast_one,
      Nat.cast_mul] at hrec ⊢
    linear_combination hrec
  · have hkm' : m + 1 < k := Nat.lt_of_not_ge hkm
    have hX :
        (X * binaryRunPolynomial n m).coeff k =
          (binaryRunPolynomial n m).coeff (k - 1) := by
      simpa [Nat.sub_add_cancel (by lia : 1 ≤ k)] using
        Polynomial.coeff_X_mul (binaryRunPolynomial n m) (k - 1)
    rw [coeff_C_mul, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_C_mul, hX,
      coeff_binaryRunPolynomial_of_pos n (m + 1) k (by lia) hkpos,
      coeff_binaryRunPolynomial_of_pos n m k hm0 hkpos,
      coeff_X_mul_one_sub_X_mul_derivative]
    rw [coeff_binaryRunPolynomial_of_pos n m (k - 1) hm0 (by lia),
      coeff_binaryRunPolynomial_of_pos n m k hm0 hkpos]
    simp [binaryRunCoeff, Nat.choose_eq_zero_of_lt (by lia : m < k - 1),
      Nat.choose_eq_zero_of_lt (by lia : m - 1 < k - 1),
      Nat.choose_eq_zero_of_lt (by lia : m - 1 < k - 2), Nat.sub_sub]

/-- Normalized differential recurrence for consecutive binary-run basis
images before the midpoint. -/
theorem binaryRunPolynomial_differential_recurrence_normalized (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) :
    binaryRunPolynomial n (m + 1) =
      (C ((m : ℝ) / ((n - m : ℕ) : ℝ)) +
          C (((n - 2 * m : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) * X) *
          binaryRunPolynomial n m +
        (C (((n - 2 * m : ℕ) : ℝ) /
            (((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ))) *
          X * (1 - X)) * (binaryRunPolynomial n m).derivative := by
  have hnm_nat : 0 < n - m := by lia
  have hnmp_nat : 0 < n + 1 - m := by lia
  have hnm : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast hnm_nat
  have hnmp : (0 : ℝ) < ((n + 1 - m : ℕ) : ℝ) := by exact_mod_cast hnmp_nat
  have hraw := binaryRunPolynomial_differential_recurrence n m hm0 hmid
  let d : ℝ := ((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ)
  let b : ℝ := ((n - 2 * m : ℕ) : ℝ)
  let c : ℝ := b / d
  let A : ℝ[X] :=
    (C ((m : ℝ) / ((n - m : ℕ) : ℝ)) +
      C (((n - 2 * m : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) * X) *
        binaryRunPolynomial n m
  let Q : ℝ[X] := X * (1 - X) * (binaryRunPolynomial n m).derivative
  have hd : d ≠ 0 := mul_ne_zero hnm.ne' hnmp.ne'
  have hbc : d⁻¹ * b = c := by
    dsimp [d, b, c]
    field_simp [hnm.ne', hnmp.ne']
  have hsplit :
      C d * binaryRunPolynomial n (m + 1) = C d * A + C b * Q := by
    have hconst :
        d * ((m : ℝ) / ((n - m : ℕ) : ℝ)) =
          (m : ℝ) * ((n + 1 - m : ℕ) : ℝ) := by
      dsimp [d]
      field_simp [hnm.ne']
    have hlinear :
        d * (((n - 2 * m : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) =
          ((n - 2 * m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ) := by
      dsimp [d]
      field_simp [hnm.ne']
    have hCconst :
        C d * C ((m : ℝ) / ((n - m : ℕ) : ℝ)) =
          C ((m : ℝ) * ((n + 1 - m : ℕ) : ℝ)) := by
      rw [← C_mul]
      exact congrArg C hconst
    have hClinear :
        C d * C (((n - 2 * m : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) =
          C (((n - 2 * m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ)) := by
      rw [← C_mul]
      exact congrArg C hlinear
    dsimp only [A, Q]
    rw [hraw]
    rw [← hCconst, ← hClinear]
    ring
  simpa [d, b, c, A, Q, mul_assoc] using
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul hd hbc hsplit

/-- Before the midpoint, the `m`th binary-run basis image has exact degree
`m`. -/
theorem natDegree_binaryRunPolynomial_eq (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m ≤ n + 1) :
    (binaryRunPolynomial n m).natDegree = m := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_binaryRunPolynomial_of_pos n m k hm0 (by lia)]
    simp [binaryRunCoeff,
      Nat.choose_eq_zero_of_lt (by lia : m - 1 < k - 1)]
  · rw [coeff_binaryRunPolynomial_of_pos n m m hm0 hm0]
    have hnum : (Nat.choose (n + 1 - m) m : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero (by lia)
    have hden : (Nat.choose n m : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero (by lia)
    simp [binaryRunCoeff, hnum, hden]

theorem hasPosLeadingCoeff_binaryRunPolynomial (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m ≤ n + 1) :
    HasPosLeadingCoeff (binaryRunPolynomial n m) := by
  rw [HasPosLeadingCoeff, Polynomial.leadingCoeff,
    natDegree_binaryRunPolynomial_eq n m hm0 hmid,
    coeff_binaryRunPolynomial_of_pos n m m hm0 hm0]
  have hnum : (0 : ℝ) < Nat.choose (n + 1 - m) m := by
    exact_mod_cast Nat.choose_pos (by lia)
  have hden : (0 : ℝ) < Nat.choose n m := by
    exact_mod_cast Nat.choose_pos (by lia)
  simp only [binaryRunCoeff, Nat.choose_self, Nat.cast_one, one_mul]
  exact div_pos hnum hden

@[simp] theorem binaryRunPolynomial_one (n : ℕ) (hn : 0 < n) :
    binaryRunPolynomial n 1 = X := by
  ext k
  cases k with
  | zero =>
      simp [coeff_zero_binaryRunPolynomial_of_pos n 1 (by simp)]
  | succ k =>
      rw [coeff_binaryRunPolynomial_of_pos n 1 (k + 1) (by simp) (by lia)]
      cases k with
      | zero =>
          simp [binaryRunCoeff, Nat.choose_one_right,
            Nat.cast_ne_zero.mpr hn.ne']
      | succ k =>
          simp [binaryRunCoeff, coeff_X,
            Nat.choose_eq_zero_of_lt (by lia : 0 < k + 1)]

private theorem X_mul_divX_binaryRunPolynomial (n m : ℕ) (hm0 : 0 < m) :
    X * (binaryRunPolynomial n m).divX = binaryRunPolynomial n m := by
  simpa [coeff_zero_binaryRunPolynomial_of_pos n m hm0] using
    Polynomial.X_mul_divX_add (binaryRunPolynomial n m)

theorem eval_zero_binaryRunPolynomial_divX_pos
    (n m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
    0 < (binaryRunPolynomial n m).divX.eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX]
  rw [coeff_binaryRunPolynomial_of_pos n m 1 hm0 (by lia)]
  have hnum : (0 : ℝ) < Nat.choose (n + 1 - m) 1 := by
    exact_mod_cast Nat.choose_pos (by lia : 1 ≤ n + 1 - m)
  have hden : (0 : ℝ) < Nat.choose n m := by
    exact_mod_cast Nat.choose_pos hm
  simpa [binaryRunCoeff] using div_pos hnum hden

/-- Consecutive binary-run basis images strictly interlace up to the midpoint.
The shared zero at the origin is retained by the project's `StrictInterl`
relation. -/
theorem strictInterl_binaryRunPolynomial_succ (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) :
    StrictInterl (binaryRunPolynomial n m) (binaryRunPolynomial n (m + 1)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      have hmdeg :
          (binaryRunPolynomial n m).natDegree = m :=
        natDegree_binaryRunPolynomial_eq n m hm0 (by lia)
      have hsuccdeg :
          (binaryRunPolynomial n (m + 1)).natDegree = m + 1 :=
        natDegree_binaryRunPolynomial_eq n (m + 1) (by lia) (by lia)
      have hmpos : HasPosLeadingCoeff (binaryRunPolynomial n m) :=
        hasPosLeadingCoeff_binaryRunPolynomial n m hm0 (by lia)
      have hsuccpos : HasPosLeadingCoeff (binaryRunPolynomial n (m + 1)) :=
        hasPosLeadingCoeff_binaryRunPolynomial n (m + 1) (by lia) (by lia)
      have hmsplits : (binaryRunPolynomial n m).Splits := by
        by_cases hm1 : m = 1
        · subst m
          simp [binaryRunPolynomial_one n (by lia)]
        · have hm_pred_pos : 0 < m - 1 := by lia
          have hprev := ih (m - 1) (by lia) hm_pred_pos (by lia)
          simpa [Nat.sub_add_cancel (by lia : 1 ≤ m)] using hprev.2.1.2
      let u : ℝ[X] :=
        C ((m : ℝ) / ((n - m : ℕ) : ℝ)) +
          C (((n - 2 * m : ℕ) : ℝ) / ((n - m : ℕ) : ℝ)) * X
      let c : ℝ :=
        ((n - 2 * m : ℕ) : ℝ) /
          (((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ))
      let v : ℝ[X] := C c * X * (1 - X)
      have hrec :
          binaryRunPolynomial n (m + 1) =
            u * binaryRunPolynomial n m +
              v * (binaryRunPolynomial n m).derivative := by
        simpa [u, c, v, mul_assoc] using
          binaryRunPolynomial_differential_recurrence_normalized n m hm0 hmid
      have hc : 0 ≤ c := by
        dsimp [c]
        positivity
      have hv : ∀ r, (binaryRunPolynomial n m).IsRoot r → v.eval r ≤ 0 := by
        intro r hr
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_of_realrooted_of_nonneg_coeffs
            ⟨hmpos.ne_zero, hmsplits⟩
            (hasNonnegCoeffs_binaryRunPolynomial n m) r hr
        dsimp [v]
        exact eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos hc hr_nonpos
      have hstep :
          StrictInterl (binaryRunPolynomial n m)
            (u * binaryRunPolynomial n m +
              v * (binaryRunPolynomial n m).derivative) :=
        strictInterl_mw_derivative_of_nonpos_of_pos_natDegree
          hmsplits (by rw [hmdeg]; exact hm0)
          (by rw [← hrec, hmdeg, hsuccdeg]; lia)
          (by rw [← hrec, hmdeg, hsuccdeg])
          (by rw [← hrec]; exact hsuccpos) hmpos hv
      rw [← hrec] at hstep
      exact hstep

/-- The constant and linear endpoint begins the binary-run Sturm chain. -/
theorem strictInterl_binaryRunPolynomial_zero_one (n : ℕ) (hn : 0 < n) :
    StrictInterl (binaryRunPolynomial n 0) (binaryRunPolynomial n 1) := by
  rw [binaryRunPolynomial_zero, binaryRunPolynomial_one n hn]
  exact (interlaces_one_linear (p := (X : ℝ[X])) (by simp)).toStrictInterl

/-- Uniform forward orientation for every adjacent pair strictly before the
midpoint, including the constant-to-linear endpoint. -/
theorem strictInterl_binaryRunPolynomial_succ_of_two_mul_lt
    (n m : ℕ) (hmid : 2 * m < n) :
    StrictInterl (binaryRunPolynomial n m)
      (binaryRunPolynomial n (m + 1)) := by
  by_cases hm0 : m = 0
  · subst m
    simpa using strictInterl_binaryRunPolynomial_zero_one n (by lia)
  · exact strictInterl_binaryRunPolynomial_succ n m
      (Nat.pos_of_ne_zero hm0) hmid

/-- At an even midpoint, the two central binary-run basis images coincide. -/
theorem binaryRunPolynomial_eq_succ_of_two_mul_eq
    (n m : ℕ) (hm0 : 0 < m) (hmid : 2 * m = n) :
    binaryRunPolynomial n m = binaryRunPolynomial n (m + 1) := by
  have hreflect := binaryRunPolynomial_reflection n m hm0 (by lia)
  have hindex : n + 1 - m = m + 1 := by lia
  simpa [hindex] using hreflect.symm

/-- Past the midpoint, reflection reverses the orientation of the adjacent
Sturm pair. -/
theorem strictInterl_binaryRunPolynomial_succ_reverse
    (n m : ℕ) (hm : m < n) (hmid : n < 2 * m) :
    StrictInterl (binaryRunPolynomial n (m + 1))
      (binaryRunPolynomial n m) := by
  let j := n - m
  have hj0 : 0 < j := by simp [j]; lia
  have hjmid : 2 * j < n := by simp [j]; lia
  have hforward := strictInterl_binaryRunPolynomial_succ n j hj0 hjmid
  have hm0 : 0 < m := by lia
  have hmle : m ≤ n := hm.le
  have hmsucc : 0 < m + 1 := by lia
  have hmsuccle : m + 1 ≤ n := by lia
  have hreflect_m := binaryRunPolynomial_reflection n m hm0 hmle
  have hreflect_succ :=
    binaryRunPolynomial_reflection n (m + 1) hmsucc hmsuccle
  have hj : j = n - m := rfl
  have hleft : n + 1 - (m + 1) = j := by simp [j]
  have hright : n + 1 - m = j + 1 := by simp [j]; lia
  rw [hleft] at hreflect_succ
  rw [hright] at hreflect_m
  simpa [hreflect_succ, hreflect_m] using hforward

/-- Removing the shared zero at the origin gives strict interlacing in the
usual no-common-root sense. -/
theorem strictInterl_binaryRunPolynomial_divX_succ (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) :
    StrictInterl (binaryRunPolynomial n m).divX
      (binaryRunPolynomial n (m + 1)).divX := by
  have hmfac :
      (X - C 0) * (binaryRunPolynomial n m).divX =
        binaryRunPolynomial n m := by
    simpa [coeff_zero_binaryRunPolynomial_of_pos n m hm0] using
      Polynomial.X_mul_divX_add (binaryRunPolynomial n m)
  have hsuccfac :
      (X - C 0) * (binaryRunPolynomial n (m + 1)).divX =
        binaryRunPolynomial n (m + 1) := by
    simpa [coeff_zero_binaryRunPolynomial_of_pos n (m + 1) (by lia)] using
      Polynomial.X_mul_divX_add (binaryRunPolynomial n (m + 1))
  apply StrictInterl.of_mul_X_sub_C_both (r := 0)
  rw [hmfac, hsuccfac]
  exact strictInterl_binaryRunPolynomial_succ n m hm0 hmid

private theorem noCommonRoot_binaryRunPolynomial_divX_succ_of_simple
    (n m : ℕ) (hm0 : 0 < m) (hmid : 2 * m < n)
    (hsimple : HasSimpleRoots (binaryRunPolynomial n m).divX) :
    ∀ r : ℝ, ¬ ((binaryRunPolynomial n m).divX.IsRoot r ∧
      (binaryRunPolynomial n (m + 1)).divX.IsRoot r) := by
  intro r hr
  have hmle : m ≤ n := by lia
  have hr_nonpos : r ≤ 0 :=
    roots_nonpos_of_realrooted_of_nonneg_coeffs
      ⟨hsimple.ne_zero,
        (strictInterl_binaryRunPolynomial_divX_succ n m hm0 hmid).1.2⟩
      (hasNonnegCoeffs_binaryRunPolynomial n m).divX r hr.1
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    exact (ne_of_gt (eval_zero_binaryRunPolynomial_divX_pos n m hm0 hmle)) hr.1
  have hr_neg : r < 0 := lt_of_le_of_ne hr_nonpos hr0
  have hmfac := X_mul_divX_binaryRunPolynomial n m hm0
  have hsuccfac := X_mul_divX_binaryRunPolynomial n (m + 1) (by lia)
  have hrJ : (binaryRunPolynomial n m).IsRoot r := by
    rw [← hmfac, Polynomial.IsRoot, eval_mul, eval_X, hr.1, mul_zero]
  have hrJsucc : (binaryRunPolynomial n (m + 1)).IsRoot r := by
    rw [← hsuccfac, Polynomial.IsRoot, eval_mul, eval_X, hr.2, mul_zero]
  have hder_ne : (binaryRunPolynomial n m).derivative.eval r ≠ 0 := by
    have hfactor_deriv := congrArg
      (fun q : ℝ[X] => q.derivative.eval r) hmfac
    have hrF : (binaryRunPolynomial n m).divX.eval r = 0 := hr.1
    simp only [derivative_mul, derivative_X, one_mul, eval_add, eval_mul,
      eval_X] at hfactor_deriv
    rw [hrF, zero_add] at hfactor_deriv
    rw [← hfactor_deriv]
    exact mul_ne_zero hr0 (hsimple.eval_derivative_ne_zero hr.1)
  have hrec := binaryRunPolynomial_differential_recurrence_normalized
    n m hm0 hmid
  have heval := congrArg (fun q : ℝ[X] => q.eval r) hrec
  have hrJeval : (binaryRunPolynomial n m).eval r = 0 := hrJ
  have hrJsuccEval : (binaryRunPolynomial n (m + 1)).eval r = 0 := hrJsucc
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_sub] at heval
  rw [hrJeval, hrJsuccEval] at heval
  simp only [mul_zero, zero_add] at heval
  have hc : 0 < ((n - 2 * m : ℕ) : ℝ) /
      (((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ)) := by
    apply div_pos
    · exact_mod_cast (by lia : 0 < n - 2 * m)
    · exact mul_pos (by exact_mod_cast (by lia : 0 < n - m))
        (by exact_mod_cast (by lia : 0 < n + 1 - m))
  have hfactor : r * (1 - r) ≠ 0 :=
    mul_ne_zero hr0 (by linarith)
  have hnonzero :
      (((n - 2 * m : ℕ) : ℝ) /
        (((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ))) *
          (r * (1 - r)) *
            (binaryRunPolynomial n m).derivative.eval r ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc.ne' hfactor) hder_ne
  apply hnonzero
  calc
    _ = ((n - 2 * m : ℕ) : ℝ) /
        (((n - m : ℕ) : ℝ) * ((n + 1 - m : ℕ) : ℝ)) * r *
          (1 - r) * (binaryRunPolynomial n m).derivative.eval r := by ring
    _ = 0 := heval.symm

/-- Before and at the top of the forward half, removing the common factor
`X` leaves a polynomial with simple roots. -/
theorem hasSimpleRoots_binaryRunPolynomial_divX
    (n m : ℕ) (hm0 : 0 < m) (hmid : 2 * m ≤ n + 1) :
    HasSimpleRoots (binaryRunPolynomial n m).divX := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        rw [binaryRunPolynomial_one n (by lia)]
        have hdiv : (X : ℝ[X]).divX = 1 := by
          simpa using (Polynomial.divX_X_pow (R := ℝ) (n := 1))
        rw [hdiv]
        simp [HasSimpleRoots]
      · let j := m - 1
        have hj0 : 0 < j := by simp [j]; lia
        have hjmid : 2 * j < n := by simp [j]; lia
        have hjsimple : HasSimpleRoots (binaryRunPolynomial n j).divX :=
          ih j (by simp [j]; lia) hj0 (by simp [j]; lia)
        have hstrict := strictInterl_binaryRunPolynomial_divX_succ
          n j hj0 hjmid
        have hno := noCommonRoot_binaryRunPolynomial_divX_succ_of_simple
          n j hj0 hjmid hjsimple
        have hsimple := hstrict.hasSimpleRoots_of_no_common_root hno
        have hj : j + 1 = m := by simp [j, Nat.sub_add_cancel (by lia : 1 ≤ m)]
        simpa [hj] using hsimple.2

/-- Every root of a reduced forward-half basis image is strictly negative. -/
theorem roots_neg_binaryRunPolynomial_divX
    (n m : ℕ) (hm0 : 0 < m) (hmid : 2 * m ≤ n + 1) :
    ∀ r, (binaryRunPolynomial n m).divX.IsRoot r → r < 0 := by
  intro r hr
  by_cases hm1 : m = 1
  · subst m
    rw [binaryRunPolynomial_one n (by lia)] at hr
    have hdiv : (X : ℝ[X]).divX = 1 := by
      simpa using (Polynomial.divX_X_pow (R := ℝ) (n := 1))
    simp [hdiv, Polynomial.IsRoot] at hr
  · let j := m - 1
    have hj0 : 0 < j := by simp [j]; lia
    have hjmid : 2 * j < n := by simp [j]; lia
    have hstrict := strictInterl_binaryRunPolynomial_divX_succ n j hj0 hjmid
    have hj : j + 1 = m := by simp [j, Nat.sub_add_cancel (by lia : 1 ≤ m)]
    have hsplits : (binaryRunPolynomial n m).divX.Splits := by
      simpa [hj] using hstrict.2.1.2
    have hne : (binaryRunPolynomial n m).divX ≠ 0 := by
      simpa [hj] using hstrict.2.1.1
    have hr_nonpos := roots_nonpos_of_realrooted_of_nonneg_coeffs
      ⟨hne, hsplits⟩ (hasNonnegCoeffs_binaryRunPolynomial n m).divX r hr
    have hr0 : r ≠ 0 := by
      intro hrzero
      subst r
      exact (ne_of_gt (eval_zero_binaryRunPolynomial_divX_pos n m hm0 (by lia))) hr
    exact lt_of_le_of_ne hr_nonpos hr0

/-- Consecutive reduced basis images before the midpoint have no common root;
hence their interlacing is strict in the ordinary root sense. -/
theorem noCommonRoot_binaryRunPolynomial_divX_succ
    (n m : ℕ) (hm0 : 0 < m) (hmid : 2 * m < n) :
    ∀ r : ℝ, ¬ ((binaryRunPolynomial n m).divX.IsRoot r ∧
      (binaryRunPolynomial n (m + 1)).divX.IsRoot r) :=
  noCommonRoot_binaryRunPolynomial_divX_succ_of_simple n m hm0 hmid
    (hasSimpleRoots_binaryRunPolynomial_divX n m hm0 (by lia))

/-- Every real signed pencil of two consecutive basis images is real-rooted
(or zero). -/
theorem splits_binaryRunPolynomial_adjacent_pencil (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) (α β : ℝ) :
    (C α * binaryRunPolynomial n m +
      C β * binaryRunPolynomial n (m + 1)).Splits :=
  allComboRealRooted_of_strictInterl
    (strictInterl_binaryRunPolynomial_succ n m hm0 hmid) α β

/-- Every real signed pencil of adjacent binary-run basis images is
real-rooted (or zero), across both orientations and the even central pair. -/
theorem splits_binaryRunPolynomial_adjacent_pencil_all
    (n m : ℕ) (hm : m < n) (α β : ℝ) :
    (C α * binaryRunPolynomial n m +
      C β * binaryRunPolynomial n (m + 1)).Splits := by
  rcases lt_trichotomy (2 * m) n with hbefore | hcentral | hafter
  · exact allComboRealRooted_of_strictInterl
      (strictInterl_binaryRunPolynomial_succ_of_two_mul_lt n m hbefore) α β
  · have hm0 : 0 < m := by
      lia
    have hsplit : (binaryRunPolynomial n m).Splits := by
      have hpair := strictInterl_binaryRunPolynomial_succ_of_two_mul_lt
        n (m - 1) (by lia)
      simpa [Nat.sub_add_cancel (by lia : 1 ≤ m)] using hpair.2.1.2
    have heq := binaryRunPolynomial_eq_succ_of_two_mul_eq n m hm0 hcentral
    have hsuccsplit : (binaryRunPolynomial n (m + 1)).Splits := by
      rw [← heq]
      exact hsplit
    rw [heq]
    rw [← add_mul, ← C_add]
    exact hsuccsplit.C_mul (α + β)
  · exact allComboRealRooted_comm
      (allComboRealRooted_of_strictInterl
        (strictInterl_binaryRunPolynomial_succ_reverse n m hm hafter)) α β

/-- The binary-run transform sends every real signed pencil supported on two
adjacent monomials to a real-rooted polynomial (or zero). -/
theorem splits_binaryRunTransform_adjacent_monomial_pencil
    (n m : ℕ) (hm : m < n) (α β : ℝ) :
    (binaryRunTransform n
      (X ^ m * (C α + C β * X))).Splits := by
  have hinput :
      (X ^ m * (C α + C β * X) : ℝ[X]) =
        C α * X ^ m + C β * X ^ (m + 1) := by
    ring
  rw [hinput, binaryRunTransform_add]
  simp only [binaryRunTransform, Polynomial.basisTransform_C_mul_X_pow]
  exact splits_binaryRunPolynomial_adjacent_pencil_all n m hm α β

end RealRooted
