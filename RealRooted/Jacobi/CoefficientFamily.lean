module

public import RealRooted.NarayanaTransformation.Coefficients
public import RealRooted.PFPolynomial
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
import RealRooted.MaWang.StrictStep
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.RootBounds

/-!
# The positive-coefficient Jacobi family

We define the terminating hypergeometric polynomial

`H n a b = sum_k binom(n,k) binom(n+b,k) / binom(a+k,k) X^k`.

For Jacobi parameters `a, b > -1`, its coefficients are positive on the
whole support.  The file proves its first-order derivative recurrence and
the parameter-shift derivative identity, then derives simple negative roots
and strict adjacent interlacing.
-/

public section

open Nat Finset Polynomial

noncomputable section

namespace RealRooted

/-- The `k`th coefficient of the positive-coefficient Jacobi polynomial. -/
@[expose]
noncomputable def jacobiCoefficient (n k : ℕ) (a b : ℝ) : ℝ :=
  (n.choose k : ℝ) * Ring.choose (n + b) k / Ring.choose (a + k) k

/-- The positive-coefficient Jacobi polynomial
`sum_k binom(n,k) binom(n+b,k) / binom(a+k,k) X^k`. -/
@[expose]
noncomputable def jacobiCoefficientPolynomial (n : ℕ) (a b : ℝ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C (jacobiCoefficient n k a b) * X ^ k

/-- Coefficients of `jacobiCoefficientPolynomial` are given by
`jacobiCoefficient` on its support and vanish above it. -/
theorem coeff_jacobiCoefficientPolynomial (n k : ℕ) (a b : ℝ) :
    (jacobiCoefficientPolynomial n a b).coeff k =
      if k ≤ n then jacobiCoefficient n k a b else 0 := by
  rw [jacobiCoefficientPolynomial, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hk : k ≤ n
  · simp [hk, Nat.lt_succ_iff.mpr hk]
  · simp [hk, Nat.lt_succ_iff.not.mpr hk]

private lemma ring_choose_den_pos (k : ℕ) {a : ℝ} (ha : -1 < a) :
    0 < Ring.choose (a + k) k := by
  cases k with
  | zero => simp
  | succ k =>
      apply Polynomial.ring_choose_pos
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith

private lemma ring_choose_num_pos {n k : ℕ} {b : ℝ}
    (hb : -1 < b) (hk : k ≤ n) :
    0 < Ring.choose (n + b) k := by
  cases k with
  | zero => simp
  | succ k =>
      apply Polynomial.ring_choose_pos
      have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith

/-- Every coefficient on the displayed support is positive when both Jacobi
parameters exceed `-1`. -/
theorem jacobiCoefficient_pos {n k : ℕ} {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) (hk : k ≤ n) :
    0 < jacobiCoefficient n k a b := by
  rw [jacobiCoefficient]
  exact div_pos
    (mul_pos (by exact_mod_cast Nat.choose_pos hk) (ring_choose_num_pos hb hk))
    (ring_choose_den_pos k ha)

/-- The positive-coefficient Jacobi polynomial has nonnegative coefficients. -/
theorem jacobiCoefficientPolynomial_hasNonnegCoeffs (n : ℕ) {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) :
    HasNonnegCoeffs (jacobiCoefficientPolynomial n a b) := by
  intro k
  rw [coeff_jacobiCoefficientPolynomial]
  split_ifs with hk
  · exact (jacobiCoefficient_pos ha hb hk).le
  · exact le_rfl

/-- The positive-coefficient Jacobi polynomial has degree exactly `n`. -/
@[simp]
theorem natDegree_jacobiCoefficientPolynomial (n : ℕ) {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) :
    (jacobiCoefficientPolynomial n a b).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [coeff_jacobiCoefficientPolynomial, Nat.not_le_of_lt hk]
  · rw [coeff_jacobiCoefficientPolynomial, ite_eq_left le_rfl]
    exact (jacobiCoefficient_pos ha hb le_rfl).ne'

/-- The positive-coefficient Jacobi polynomial has positive leading
coefficient. -/
theorem jacobiCoefficientPolynomial_hasPosLeadingCoeff (n : ℕ) {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) :
    HasPosLeadingCoeff (jacobiCoefficientPolynomial n a b) := by
  rw [HasPosLeadingCoeff, leadingCoeff,
    natDegree_jacobiCoefficientPolynomial n ha hb,
    coeff_jacobiCoefficientPolynomial, ite_eq_left le_rfl]
  exact jacobiCoefficient_pos ha hb le_rfl

/-- The constant coefficient of every positive-coefficient Jacobi polynomial
is one. -/
@[simp]
theorem jacobiCoefficientPolynomial_coeff_zero (n : ℕ) (a b : ℝ) :
    (jacobiCoefficientPolynomial n a b).coeff 0 = 1 := by
  simp [coeff_jacobiCoefficientPolynomial, jacobiCoefficient]

/-- The degree-zero member of the positive-coefficient Jacobi family is one. -/
@[simp]
theorem jacobiCoefficientPolynomial_zero (a b : ℝ) :
    jacobiCoefficientPolynomial 0 a b = 1 := by
  ext k
  cases k <;>
    simp [coeff_jacobiCoefficientPolynomial, jacobiCoefficient, Polynomial.coeff_one]

/-- On nonnegative integer diagonal parameters, the positive-coefficient
Jacobi family is the existing generalized Narayana family. -/
theorem jacobiCoefficientPolynomial_nat_diagonal (m n : ℕ) :
    jacobiCoefficientPolynomial n m m = narayanaPolynomial m n := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_jacobiCoefficientPolynomial, ite_eq_left hk,
      coeff_narayanaPolynomial_of_le hk]
    simp only [jacobiCoefficient, narayanaTransformCoeff]
    rw [show (n : ℝ) + (m : ℝ) = ((n + m : ℕ) : ℝ) by norm_num,
      show (m : ℝ) + (k : ℝ) = ((m + k : ℕ) : ℝ) by norm_num,
      Ring.choose_natCast, Ring.choose_natCast]
  · rw [coeff_jacobiCoefficientPolynomial, ite_eq_right hk,
      coeff_narayanaPolynomial_of_lt (Nat.lt_of_not_ge hk)]

private lemma succ_mul_ring_choose_add_one (x : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose (x + 1) (k + 1) =
      (x + 1) * Ring.choose x k := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_left, smeval_mul,
    smeval_X, pow_one, smeval_comp, smeval_sub, smeval_one, pow_zero,
    one_smul, add_sub_cancel_right, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private lemma sub_mul_ring_choose_add_one (x : ℝ) (k : ℕ) :
    (x + 1 - k) * Ring.choose (x + 1) k =
      (x + 1) * Ring.choose x k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Ring.choose_succ_succ]
      have h := Ring.choose_smul_choose (R := ℝ) x
        (n := k + 1) (k := k) (by lia)
      simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, Nat.add_sub_cancel_left, Ring.choose_one_right] at h
      push_cast at h ⊢
      linear_combination -h

/-- Differentiation increments the first parameter, up to the displayed
positive scalar. -/
theorem derivative_jacobiCoefficientPolynomial (n : ℕ) {a b : ℝ}
    (ha : -1 < a) :
    (jacobiCoefficientPolynomial (n + 1) a b).derivative =
      C (((n + 1 : ℕ) : ℝ) * (n + b + 1) / (a + 1)) *
        jacobiCoefficientPolynomial n (a + 1) b := by
  ext k
  rw [coeff_derivative, coeff_C_mul,
    coeff_jacobiCoefficientPolynomial, coeff_jacobiCoefficientPolynomial]
  by_cases hk : k ≤ n
  · rw [ite_eq_left (Nat.succ_le_succ hk), ite_eq_left hk]
    simp only [jacobiCoefficient]
    have hnat :
        (((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ)) =
          ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) := by
      have h := congrArg (fun m : ℕ ↦ (m : ℝ))
        (Nat.add_one_mul_choose_eq n k).symm
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h ⊢
      nlinarith
    have hnum := succ_mul_ring_choose_add_one (n + b) k
    have hdenSucc := succ_mul_ring_choose_add_one (a + k) k
    have hdenShift := sub_mul_ring_choose_add_one (a + k) k
    have hden0 : Ring.choose (a + (k + 1)) (k + 1) ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ring_choose_den_pos (k + 1) ha).ne'
    have hden1 : Ring.choose (a + 1 + k) k ≠ 0 := by
      apply (ring_choose_den_pos k (show -1 < a + 1 by linarith)).ne'
    have ha1 : a + 1 ≠ 0 := by linarith
    norm_num only [Nat.cast_add, Nat.cast_one] at hnat hnum hdenSucc hdenShift ⊢
    have hdenShift' :
        (a + 1) * Ring.choose (a + 1 + k) k =
          (a + k + 1) * Ring.choose (a + k) k := by
      ring_nf at hdenShift ⊢
      exact hdenShift
    have hdenEq :
        ((k : ℝ) + 1) * Ring.choose (a + (k : ℝ) + 1) (k + 1) =
          (a + 1) * Ring.choose (a + 1 + k) k := by
      calc
        _ = (a + (k : ℝ) + 1) * Ring.choose (a + k) k := hdenSucc
        _ = _ := hdenShift'.symm
    have hproduct :
        (((k : ℝ) + 1) * ((n + 1).choose (k + 1) : ℝ) *
            Ring.choose (n + b + 1) (k + 1)) *
            ((a + 1) * Ring.choose (a + 1 + k) k) =
          ((((n : ℝ) + 1) * (n.choose k : ℝ)) *
            ((n + b + 1) * Ring.choose (n + b) k)) *
            Ring.choose (a + k + 1) (k + 1) := by
      calc
        _ = (((k : ℝ) + 1) * ((n + 1).choose (k + 1) : ℝ) *
              Ring.choose (n + b + 1) (k + 1)) *
              (((k : ℝ) + 1) * Ring.choose (a + k + 1) (k + 1)) := by
            rw [hdenEq]
        _ = ((((k : ℝ) + 1) * ((n + 1).choose (k + 1) : ℝ)) *
              (((k : ℝ) + 1) * Ring.choose (n + b + 1) (k + 1))) *
              Ring.choose (a + k + 1) (k + 1) := by ring
        _ = _ := by rw [hnat, hnum]
    field_simp [hden0, hden1, ha1]
    convert hproduct using 1 <;> ring
  · rw [ite_eq_right hk]
    have hk' : ¬ k + 1 ≤ n + 1 := by lia
    rw [ite_eq_right hk']
    simp

private lemma jacobiCoefficient_succ_rank_mul {n k : ℕ} (a b : ℝ)
    (hk : k ≤ n) :
    (((n : ℝ) + 1 - k) * (n + b + 1 - k)) *
        jacobiCoefficient (n + 1) k a b =
      (((n : ℝ) + 1) * (n + b + 1)) *
        jacobiCoefficient n k a b := by
  have hnat0 := Nat.choose_mul_succ_eq n k
  have hnat :
      (((n : ℝ) + 1 - k) * ((n + 1).choose k : ℝ)) =
        ((n : ℝ) + 1) * (n.choose k : ℝ) := by
    have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hnat0
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast ⊢
    rw [Nat.cast_sub (show k ≤ n + 1 by lia)] at hcast
    push_cast at hcast
    ring_nf at hcast ⊢
    exact hcast.symm
  have hring := sub_mul_ring_choose_add_one (n + b) k
  rw [jacobiCoefficient, jacobiCoefficient]
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ = ((((n : ℝ) + 1 - k) * ((n + 1).choose k : ℝ)) *
          ((n + b + 1 - k) * Ring.choose (n + b + 1) k)) /
        Ring.choose (a + k) k := by ring
    _ = ((((n : ℝ) + 1) * (n.choose k : ℝ)) *
          ((n + b + 1) * Ring.choose (n + b) k)) /
        Ring.choose (a + k) k := by rw [hnat, hring]
    _ = _ := by ring

private lemma succ_mul_ring_choose_same (x : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose x (k + 1) =
      (x - k) * Ring.choose x k := by
  have hleft := succ_mul_ring_choose_add_one (x - 1) k
  have hright := sub_mul_ring_choose_add_one (x - 1) k
  calc
    (k + 1 : ℝ) * Ring.choose x (k + 1) =
        x * Ring.choose (x - 1) k := by convert hleft using 1 <;> ring
    _ = (x - k) * Ring.choose x k := by
      convert hright.symm using 1 <;> ring

private lemma jacobiCoefficient_pred_rank_mul {n k : ℕ} {a b : ℝ}
    (ha : -1 < a) (hk0 : 1 ≤ k) (hk : k ≤ n) :
    (((n : ℝ) + 1 - k) * (n + b + 1 - k)) *
        jacobiCoefficient n (k - 1) a b =
      ((k : ℝ) * (a + k)) * jacobiCoefficient n k a b := by
  have hkpred : k - 1 + 1 = k := by lia
  have hnat0 := Nat.choose_succ_right_eq n (k - 1)
  have hnat :
      (((n : ℝ) + 1 - k) * (n.choose (k - 1) : ℝ)) =
        (k : ℝ) * (n.choose k : ℝ) := by
    have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hnat0
    rw [hkpred] at hcast
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast ⊢
    rw [Nat.cast_sub (show k - 1 ≤ n by lia)] at hcast
    rw [Nat.cast_sub hk0] at hcast
    norm_num at hcast
    ring_nf at hcast ⊢
    exact hcast.symm
  have hnum0 := succ_mul_ring_choose_same (n + b) (k - 1)
  have hnum :
      (n + b + 1 - k) * Ring.choose (n + b) (k - 1) =
        (k : ℝ) * Ring.choose (n + b) k := by
    rw [hkpred] at hnum0
    norm_num only [Nat.cast_sub hk0, Nat.cast_one] at hnum0
    nlinarith
  have hden0 := succ_mul_ring_choose_add_one (a + (k - 1)) (k - 1)
  have hden :
      (k : ℝ) * Ring.choose (a + k) k =
        (a + k) * Ring.choose (a + (k - 1)) (k - 1) := by
    rw [hkpred] at hden0
    norm_num only [Nat.cast_sub hk0, Nat.cast_one] at hden0 ⊢
    convert hden0 using 1 <;> ring
  have hdenPred : Ring.choose (a + (k - 1)) (k - 1) ≠ 0 :=
    by
      convert (ring_choose_den_pos (k - 1) ha).ne' using 1
      rw [Nat.cast_sub hk0]
      norm_num
  have hdenK : Ring.choose (a + k) k ≠ 0 :=
    (ring_choose_den_pos k ha).ne'
  rw [jacobiCoefficient, jacobiCoefficient]
  norm_num only [Nat.cast_sub hk0]
  field_simp [hdenPred, hdenK]
  have hprod :
      ((((n : ℝ) + 1 - k) * (n.choose (k - 1) : ℝ)) *
          ((n + b + 1 - k) * Ring.choose (n + b) (k - 1))) *
          Ring.choose (a + k) k =
        (((k : ℝ) * (n.choose k : ℝ)) *
          ((k : ℝ) * Ring.choose (n + b) k)) *
          Ring.choose (a + k) k := by rw [hnat, hnum]
  calc
    _ = ((((n : ℝ) + 1 - k) * (n.choose (k - 1) : ℝ)) *
          ((n + b + 1 - k) * Ring.choose (n + b) (k - 1))) *
          Ring.choose (a + k) k := by ring
    _ = (((k : ℝ) * (n.choose k : ℝ)) *
          ((k : ℝ) * Ring.choose (n + b) k)) *
          Ring.choose (a + k) k := hprod
    _ = (((k : ℝ) * (n.choose k : ℝ) * Ring.choose (n + b) k) *
          ((k : ℝ) * Ring.choose (a + k) k)) := by ring
    _ = (((k : ℝ) * (n.choose k : ℝ) * Ring.choose (n + b) k) *
          ((a + k) * Ring.choose (a + (k - 1)) (k - 1))) := by rw [hden]
    _ = _ := by ring

private lemma jacobiCoefficient_succ_top_mul (n : ℕ) {a b : ℝ}
    (ha : -1 < a) :
    (n + a + 1) * jacobiCoefficient (n + 1) (n + 1) a b =
      (n + b + 1) * jacobiCoefficient n n a b := by
  have hnum := succ_mul_ring_choose_add_one (n + b) n
  have hden := succ_mul_ring_choose_add_one (a + n) n
  have hden0 : Ring.choose (a + (n + 1)) (n + 1) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ring_choose_den_pos (n + 1) ha).ne'
  have hden1 : Ring.choose (a + n) n ≠ 0 :=
    (ring_choose_den_pos n ha).ne'
  rw [jacobiCoefficient, jacobiCoefficient]
  norm_num only [Nat.choose_self, Nat.cast_one, one_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp [hden0, hden1]
  have hprod :
      (n + a + 1) * Ring.choose (n + b + 1) (n + 1) *
          Ring.choose (a + n) n =
        (n + b + 1) * Ring.choose (n + b) n *
          Ring.choose (a + n + 1) (n + 1) := by
    calc
      _ = Ring.choose (n + b + 1) (n + 1) *
          (((n : ℝ) + 1) * Ring.choose (a + n + 1) (n + 1)) := by
            rw [hden]
            ring
      _ = (((n : ℝ) + 1) * Ring.choose (n + b + 1) (n + 1)) *
          Ring.choose (a + n + 1) (n + 1) := by ring
      _ = _ := by rw [hnum]
  convert hprod using 1 <;> ring

/-- Scalar on the next row in the first-order Jacobi recurrence. -/
@[expose]
def jacobiCoefficientRecurrenceDen (n : ℕ) (a b : ℝ) : ℝ :=
  (n + a + 1) * (n + a + b + 1)

/-- Scalar multiplying the derivative in the first-order Jacobi recurrence. -/
@[expose]
def jacobiCoefficientDerivativeWeight (n : ℕ) (a b : ℝ) : ℝ :=
  2 * n + a + b + 2

/-- Coefficient of `X` in the row multiplier of the first-order Jacobi
recurrence. -/
@[expose]
def jacobiCoefficientXWeight (n : ℕ) (a b : ℝ) : ℝ :=
  jacobiCoefficientDerivativeWeight n a b * (2 * n + a + b + 1) -
    jacobiCoefficientRecurrenceDen n a b

private lemma jacobiCoefficient_recurrence_scalar_identity
    (n k a b : ℝ) :
    (n + a + 1) * (n + a + b + 1) * ((n + 1) * (n + b + 1)) =
      ((n + a + 1) * (n + a + b + 1) + (2 * n + a + b + 2) * k) *
          ((n + 1 - k) * (n + b + 1 - k)) +
        ((2 * n + a + b + 2) * (2 * n + a + b + 1) -
            (n + a + 1) * (n + a + b + 1) -
            (2 * n + a + b + 2) * (k - 1)) * (k * (a + k)) := by
  ring

/-- First-order derivative recurrence for the positive-coefficient Jacobi
family. -/
theorem jacobiCoefficientPolynomial_derivative_recurrence
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    C (jacobiCoefficientRecurrenceDen n a b) *
        jacobiCoefficientPolynomial (n + 1) a b =
      (C (jacobiCoefficientRecurrenceDen n a b) +
          C (jacobiCoefficientXWeight n a b) * X) *
          jacobiCoefficientPolynomial n a b +
        (C (jacobiCoefficientDerivativeWeight n a b) * X * (1 - X)) *
          (jacobiCoefficientPolynomial n a b).derivative := by
  let H := jacobiCoefficientPolynomial n a b
  let R := jacobiCoefficientRecurrenceDen n a b
  let U := jacobiCoefficientDerivativeWeight n a b
  let V := jacobiCoefficientXWeight n a b
  have hform :
      (C R + C V * X) * H + (C U * X * (1 - X)) * H.derivative =
        C R * H + C V * (X * H) + C U * (X * H.derivative) -
          C U * (X * (X * H.derivative)) := by ring
  rw [hform]
  ext k
  cases k with
  | zero =>
      simp [H, R, coeff_jacobiCoefficientPolynomial, jacobiCoefficient]
  | succ j =>
      simp only [coeff_C_mul, coeff_add, coeff_sub, coeff_X_mul]
      dsimp only [H]
      rw [coeff_derivative, Polynomial.coeff_X_mul_derivative]
      rw [coeff_jacobiCoefficientPolynomial,
        coeff_jacobiCoefficientPolynomial,
        coeff_jacobiCoefficientPolynomial]
      dsimp only [R, U, V, jacobiCoefficientRecurrenceDen,
        jacobiCoefficientDerivativeWeight, jacobiCoefficientXWeight]
      by_cases hjn : j + 1 ≤ n
      · rw [ite_eq_left (by lia : j + 1 ≤ n + 1), ite_eq_left hjn,
          ite_eq_left (by lia : j ≤ n)]
        let d : ℝ := ((n : ℝ) + 1 - (j + 1)) * (n + b + 1 - (j + 1))
        let r : ℝ := ((n : ℝ) + a + 1) * (n + a + b + 1)
        let u : ℝ := 2 * n + a + b + 2
        let v : ℝ := u * (2 * n + a + b + 1) - r
        let cnext := jacobiCoefficient (n + 1) (j + 1) a b
        let c := jacobiCoefficient n (j + 1) a b
        let cprev := jacobiCoefficient n j a b
        have hsucc := jacobiCoefficient_succ_rank_mul a b hjn
        norm_num only [Nat.cast_add, Nat.cast_one] at hsucc
        change d * cnext = ((n : ℝ) + 1) * (n + b + 1) * c at hsucc
        have hpred := jacobiCoefficient_pred_rank_mul (b := b) ha (by lia) hjn
        norm_num only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hpred
        change d * cprev = (j + 1 : ℝ) * (a + (j + 1)) * c at hpred
        have hjnReal : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
        have hDpos : 0 < d := by
          dsimp only [d]
          apply mul_pos <;> linarith
        have hscalar :
            r * (((n : ℝ) + 1) * (n + b + 1)) =
              (r + u * (j + 1)) * d +
                (v - u * j) * ((j + 1) * (a + (j + 1))) := by
          dsimp only [r, u, v, d]
          have h :=
            jacobiCoefficient_recurrence_scalar_identity (n : ℝ) (j + 1) a b
          ring_nf at h ⊢
        change r * cnext = r * c + v * cprev + u * (c * (j + 1)) -
          u * (j * cprev)
        apply mul_left_cancel₀ hDpos.ne'
        calc
          d * (r * cnext) = r * (d * cnext) := by ring
          _ = r * (((n : ℝ) + 1) * (n + b + 1) * c) := by rw [hsucc]
          _ = (r * (((n : ℝ) + 1) * (n + b + 1))) * c := by ring
          _ = ((r + u * (j + 1)) * d +
              (v - u * j) * ((j + 1) * (a + (j + 1)))) * c := by rw [hscalar]
          _ = (r + u * (j + 1)) * (d * c) + (v - u * j) * (d * cprev) := by
            rw [hpred]
            ring
          _ = d * (r * c + v * cprev + u * (c * (j + 1)) -
              u * (j * cprev)) := by ring
      · rw [ite_eq_right hjn]
        by_cases htop : j + 1 = n + 1
        · have hjn' : j = n := by lia
          subst j
          rw [ite_eq_left le_rfl, ite_eq_left le_rfl]
          have htopCoeff := jacobiCoefficient_succ_top_mul n (b := b) ha
          linear_combination (n + a + b + 1) * htopCoeff
        · have habove : ¬ j + 1 ≤ n + 1 := by lia
          have habovePred : ¬ j ≤ n := by lia
          rw [ite_eq_right habove, ite_eq_right habovePred]
          simp

/-- A polynomial family satisfying the Jacobi derivative recurrence from rank
one onward is determined by its first two rows. -/
theorem eq_jacobiCoefficientPolynomial_of_derivative_recurrence
    (P : ℕ → ℝ[X]) {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (hzero : P 0 = jacobiCoefficientPolynomial 0 a b)
    (hone : P 1 = jacobiCoefficientPolynomial 1 a b)
    (hrec : ∀ n, 1 ≤ n →
      C (jacobiCoefficientRecurrenceDen n a b) * P (n + 1) =
        (C (jacobiCoefficientRecurrenceDen n a b) +
            C (jacobiCoefficientXWeight n a b) * X) * P n +
          (C (jacobiCoefficientDerivativeWeight n a b) * X * (1 - X)) *
            (P n).derivative) :
    ∀ n, P n = jacobiCoefficientPolynomial n a b := by
  intro n
  cases n with
  | zero => exact hzero
  | succ n =>
      induction n with
      | zero => exact hone
      | succ n ih =>
          let r := jacobiCoefficientRecurrenceDen (n + 1) a b
          have hnReal : (1 : ℝ) ≤ n + 1 := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          have hrpos : 0 < r := by
            dsimp only [r, jacobiCoefficientRecurrenceDen]
            norm_num only [Nat.cast_add, Nat.cast_one]
            apply mul_pos <;> nlinarith
          have hP := hrec (n + 1) (by lia)
          have hH := jacobiCoefficientPolynomial_derivative_recurrence
            (n + 1) ha hb
          rw [ih] at hP
          apply mul_left_cancel₀ (C_ne_zero.mpr hrpos.ne')
          exact hP.trans hH.symm

private theorem jacobiCoefficientPolynomial_step
    (m : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) (hm : 1 ≤ m)
    (hsplits : (jacobiCoefficientPolynomial m a b).Splits)
    (hsimple : HasSimpleRoots (jacobiCoefficientPolynomial m a b)) :
    StrictInterl (jacobiCoefficientPolynomial m a b)
        (jacobiCoefficientPolynomial (m + 1) a b) ∧
      HasSimpleRoots (jacobiCoefficientPolynomial (m + 1) a b) ∧
      (∀ x, (jacobiCoefficientPolynomial m a b).IsRoot x →
        ¬(jacobiCoefficientPolynomial (m + 1) a b).IsRoot x) := by
  let f := jacobiCoefficientPolynomial m a b
  let F := jacobiCoefficientPolynomial (m + 1) a b
  let r := jacobiCoefficientRecurrenceDen m a b
  let u := jacobiCoefficientDerivativeWeight m a b
  let v := jacobiCoefficientXWeight m a b
  let A := C (r⁻¹) * (C r + C v * X)
  let B := C (r⁻¹) * (C u * X * (1 - X))
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrpos : 0 < r := by
    dsimp only [r, jacobiCoefficientRecurrenceDen]
    apply mul_pos <;> nlinarith
  have hupos : 0 < u := by
    dsimp only [u, jacobiCoefficientDerivativeWeight]
    nlinarith
  have hraw := jacobiCoefficientPolynomial_derivative_recurrence m ha hb
  have hrec : F = A * f + B * f.derivative := by
    calc
      F = C (r⁻¹) * (C r * F) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hrpos.ne', C_1, one_mul]
      _ = C (r⁻¹) * ((C r + C v * X) * f +
          (C u * X * (1 - X)) * f.derivative) := by
        rw [hraw]
      _ = A * f + B * f.derivative := by
        dsimp only [A, B]
        ring
  have hfpos := jacobiCoefficientPolynomial_hasPosLeadingCoeff m ha hb
  have hFpos := jacobiCoefficientPolynomial_hasPosLeadingCoeff (m + 1) ha hb
  have hBneg : ∀ x, f.IsRoot x → B.eval x < 0 := by
    intro x hx
    have hxle : x ≤ 0 := roots_nonpos_of_realrooted_of_nonneg_coeffs
      ⟨hfpos.ne_zero, hsplits⟩
      (jacobiCoefficientPolynomial_hasNonnegCoeffs m ha hb) x hx
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
        jacobiCoefficientPolynomial_coeff_zero] at hx
      exact one_ne_zero hx
    have hxneg : x < 0 := lt_of_le_of_ne hxle hxne
    dsimp only [B]
    simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
    have hone : 0 < 1 - x := by linarith
    have hrinv : 0 < r⁻¹ := inv_pos.mpr hrpos
    have hux : u * x < 0 := mul_neg_of_pos_of_neg hupos hxneg
    have huxone : u * x * (1 - x) < 0 := mul_neg_of_neg_of_pos hux hone
    exact mul_neg_of_pos_of_neg hrinv huxone
  have hpair := strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ
    hsplits hfpos hFpos (by
      rw [natDegree_jacobiCoefficientPolynomial m ha hb]
      exact hm) (by
      rw [natDegree_jacobiCoefficientPolynomial m ha hb,
        natDegree_jacobiCoefficientPolynomial (m + 1) ha hb])
    hsimple hrec hBneg
  refine ⟨hpair.1, hpair.2, ?_⟩
  apply noCommonRoot_of_auxiliary_sign hrec
  · intro x hx
    exact mul_self_pos.mpr (hsimple.eval_derivative_ne_zero hx)
  · exact hBneg

private theorem jacobiCoefficientPolynomial_succ_package
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    StrictInterl (jacobiCoefficientPolynomial n a b)
        (jacobiCoefficientPolynomial (n + 1) a b) ∧
      HasSimpleRoots (jacobiCoefficientPolynomial (n + 1) a b) ∧
      (∀ x, (jacobiCoefficientPolynomial n a b).IsRoot x →
        ¬(jacobiCoefficientPolynomial (n + 1) a b).IsRoot x) := by
  induction n with
  | zero =>
      have hzero := jacobiCoefficientPolynomial_hasPosLeadingCoeff 0 ha hb
      have hone := jacobiCoefficientPolynomial_hasPosLeadingCoeff 1 ha hb
      have hstrict :
          StrictInterl (jacobiCoefficientPolynomial 0 a b)
            (jacobiCoefficientPolynomial 1 a b) := by
        apply StrictInterl.of_natDegree_eq_zero_left hzero.ne_zero
        · rw [natDegree_jacobiCoefficientPolynomial 0 ha hb]
        · exact hone.ne_zero
        · simp [natDegree_jacobiCoefficientPolynomial 1 ha hb]
      have hsimple := hasSimpleRoots_of_natDegree_le_one hone.ne_zero
        (by rw [natDegree_jacobiCoefficientPolynomial 1 ha hb])
      have hno : ∀ x, (jacobiCoefficientPolynomial 0 a b).IsRoot x →
          ¬(jacobiCoefficientPolynomial 1 a b).IsRoot x := by
        intro x hx
        simp at hx
      exact ⟨hstrict, hsimple, hno⟩
  | succ n ih =>
      exact jacobiCoefficientPolynomial_step (n + 1) ha hb (by lia)
        ih.1.2.1.2 ih.2.1

/-- Consecutive positive-coefficient Jacobi polynomials strictly interlace. -/
theorem jacobiCoefficientPolynomial_strictInterl_succ
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    StrictInterl (jacobiCoefficientPolynomial n a b)
      (jacobiCoefficientPolynomial (n + 1) a b) :=
  (jacobiCoefficientPolynomial_succ_package n ha hb).1

/-- Consecutive positive-coefficient Jacobi polynomials have no common real
root, so their interlacing is strict in the usual root-separation sense. -/
theorem jacobiCoefficientPolynomial_noCommonRoot_succ
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    ∀ x, (jacobiCoefficientPolynomial n a b).IsRoot x →
      ¬(jacobiCoefficientPolynomial (n + 1) a b).IsRoot x :=
  (jacobiCoefficientPolynomial_succ_package n ha hb).2.2

/-- Every positive-coefficient Jacobi polynomial splits over the reals. -/
theorem jacobiCoefficientPolynomial_splits
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    (jacobiCoefficientPolynomial n a b).Splits :=
  (jacobiCoefficientPolynomial_strictInterl_succ n ha hb).1.2

/-- Every positive-coefficient Jacobi polynomial has only simple roots. -/
theorem jacobiCoefficientPolynomial_hasSimpleRoots
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    HasSimpleRoots (jacobiCoefficientPolynomial n a b) := by
  cases n with
  | zero =>
      apply hasSimpleRoots_of_natDegree_le_one
        (jacobiCoefficientPolynomial_hasPosLeadingCoeff 0 ha hb).ne_zero
      rw [natDegree_jacobiCoefficientPolynomial 0 ha hb]
      simp
  | succ n => exact (jacobiCoefficientPolynomial_succ_package n ha hb).2.1

/-- Every positive-coefficient Jacobi polynomial is a Polya-frequency
polynomial. -/
theorem jacobiCoefficientPolynomial_isPFPolynomial
    (n : ℕ) {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    IsPFPolynomial (jacobiCoefficientPolynomial n a b) :=
  IsPFPolynomial.of_realRooted_nonneg
    (jacobiCoefficientPolynomial_hasNonnegCoeffs n ha hb)
    (jacobiCoefficientPolynomial_splits n ha hb)

/-- Every root of a positive-degree positive-coefficient Jacobi polynomial is
strictly negative. -/
theorem jacobiCoefficientPolynomial_isRoot_neg
    (n : ℕ) {a b x : ℝ} (ha : -1 < a) (hb : -1 < b)
    (hx : (jacobiCoefficientPolynomial n a b).IsRoot x) :
    x < 0 := by
  have hpos := jacobiCoefficientPolynomial_hasPosLeadingCoeff n ha hb
  have hxle : x ≤ 0 := roots_nonpos_of_realrooted_of_nonneg_coeffs
    ⟨hpos.ne_zero, jacobiCoefficientPolynomial_splits n ha hb⟩
    (jacobiCoefficientPolynomial_hasNonnegCoeffs n ha hb) x hx
  have hxne : x ≠ 0 := by
    intro hx0
    subst x
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
      jacobiCoefficientPolynomial_coeff_zero] at hx
    exact one_ne_zero hx
  exact lt_of_le_of_ne hxle hxne

end RealRooted
