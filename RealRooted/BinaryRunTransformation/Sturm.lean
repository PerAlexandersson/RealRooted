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
  rw [binaryRunPolynomial, ite_eq_right (ne_of_gt hm0),
    Polynomial.finsetSum_coeff]
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp [binaryRunCoeff]
    · intro b hb hbk
      simp [coeff_monomial, hbk]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨hk0, hkn⟩)).elim
  · have htop : n + 1 - m < k := by lia
    rw [Finset.sum_eq_zero]
    · simp [binaryRunCoeff, Nat.choose_eq_zero_of_lt htop]
    · intro b hb
      rw [coeff_monomial, ite_eq_right]
      intro hbk
      subst b
      exact hkn (Finset.mem_Icc.mp hb).2

private theorem coeff_binaryRunPolynomial_zero_of_pos (n m : ℕ) (hm0 : 0 < m) :
    (binaryRunPolynomial n m).coeff 0 = 0 := by
  rw [binaryRunPolynomial, ite_eq_right (ne_of_gt hm0),
    Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1
  simp [coeff_monomial, hk0]

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
    nlinarith [hden]
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
    simp [coeff_binaryRunPolynomial_zero_of_pos n m hm0,
      coeff_binaryRunPolynomial_zero_of_pos n (m + 1) (by lia)]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  by_cases hk1 : k = 1
  · subst k
    rw [coeff_C_mul, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_C_mul, coeff_X_mul,
      coeff_binaryRunPolynomial_of_pos n (m + 1) 1 (by lia) (by lia),
      coeff_binaryRunPolynomial_of_pos n m 1 hm0 (by lia),
      coeff_X_mul_one_sub_X_mul_derivative]
    rw [coeff_binaryRunPolynomial_zero_of_pos n m hm0,
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
      simp [coeff_binaryRunPolynomial_zero_of_pos n 1 (by simp)]
  | succ k =>
      rw [coeff_binaryRunPolynomial_of_pos n 1 (k + 1) (by simp) (by lia)]
      cases k with
      | zero =>
          simp [binaryRunCoeff, Nat.choose_one_right,
            Nat.cast_ne_zero.mpr hn.ne']
      | succ k =>
          simp [binaryRunCoeff, coeff_X,
            Nat.choose_eq_zero_of_lt (by lia : 0 < k + 1)]

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

/-- Removing the shared zero at the origin gives strict interlacing in the
usual no-common-root sense. -/
theorem strictInterl_binaryRunPolynomial_divX_succ (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) :
    StrictInterl (binaryRunPolynomial n m).divX
      (binaryRunPolynomial n (m + 1)).divX := by
  have hmfac :
      (X - C 0) * (binaryRunPolynomial n m).divX =
        binaryRunPolynomial n m := by
    simpa [coeff_binaryRunPolynomial_zero_of_pos n m hm0] using
      Polynomial.X_mul_divX_add (binaryRunPolynomial n m)
  have hsuccfac :
      (X - C 0) * (binaryRunPolynomial n (m + 1)).divX =
        binaryRunPolynomial n (m + 1) := by
    simpa [coeff_binaryRunPolynomial_zero_of_pos n (m + 1) (by lia)] using
      Polynomial.X_mul_divX_add (binaryRunPolynomial n (m + 1))
  apply StrictInterl.of_mul_X_sub_C_both (r := 0)
  rw [hmfac, hsuccfac]
  exact strictInterl_binaryRunPolynomial_succ n m hm0 hmid

/-- Every real signed pencil of two consecutive basis images is real-rooted
(or zero). -/
theorem splits_binaryRunPolynomial_adjacent_pencil (n m : ℕ)
    (hm0 : 0 < m) (hmid : 2 * m < n) (α β : ℝ) :
    (C α * binaryRunPolynomial n m +
      C β * binaryRunPolynomial n (m + 1)).Splits :=
  allComboRealRooted_of_strictInterl
    (strictInterl_binaryRunPolynomial_succ n m hm0 hmid) α β

end RealRooted
