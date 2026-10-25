module

public import RealRooted.MultiplierSequence.TwoSidedJensen
public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.Recurrence.RowModel
public import RealRooted.CombinatorialExamples.Narayana
public import RealRooted.Hadamard
public import RealRooted.Hadamard.GarloffWagner
public import RealRooted.NarayanaTransformation

@[expose] public section

open RealRooted Polynomial

/-!
# The A056939 model

The Schur--Szegő model proves that every row splits.  The public transfer theorem
identifies any recurrence presentation with the model by lag-two uniqueness.
-/

noncomputable section

namespace RealRooted.Applications.OEIS.A056939

/-- The positive denominator in the A056939 update. -/
def denominator (n : ℕ) : ℝ :=
  (7 / 2) + (1 / 6) * (3 + (n : ℝ)) ^ 2 + (5 / 6) * (n : ℝ)

/-- The lag-two recurrence operator for A056939. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (C ((1 / denominator n) * (5 + (3 / 2) * (n : ℝ))) * X +
      C ((1 / denominator n) * (-5 + (-3 / 2) * (n : ℝ))) * X ^ 2) *
      p.derivative +
    (C ((1 / denominator n) *
        ((35 / 6) + (-1 / 6) * (3 + (n : ℝ)) ^ 2 + (11 / 6) * (n : ℝ))) +
      C ((1 / denominator n) *
        ((-8 / 3) + (-2 / 3) * (n : ℝ) + (4 / 3) * (3 + (n : ℝ)) ^ 2)) * X) *
      p +
    (C ((1 / denominator n) *
        ((-7 / 3) - (n : ℝ) + (1 / 3) * (3 + (n : ℝ)) ^ 2)) +
      C ((1 / denominator n) *
        ((-14 / 3) - 2 * (n : ℝ) + (2 / 3) * (3 + (n : ℝ)) ^ 2)) * X +
      C ((1 / denominator n) *
        ((-7 / 3) - (n : ℝ) + (1 / 3) * (3 + (n : ℝ)) ^ 2)) * X ^ 2) * q

/-- The recurrence model for A056939. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => nextRow n (polynomial (n + 1)) (polynomial n)

private noncomputable def schurModel (n : ℕ) : ℝ[X] :=
  schurSzegoComp n (narayanaPolynomial 1 n) (narayanaPolynomial 2 n)

private def modelCoeff (n k : ℕ) : ℝ :=
  (2 * (Nat.factorial n : ℝ) * (Nat.factorial (n + 1) : ℝ) *
      (Nat.factorial (n + 2) : ℝ)) /
    ((Nat.factorial k : ℝ) * (Nat.factorial (k + 1) : ℝ) *
      (Nat.factorial (k + 2) : ℝ) * (Nat.factorial (n - k) : ℝ) *
      (Nat.factorial (n + 1 - k) : ℝ) * (Nat.factorial (n + 2 - k) : ℝ))

private def commonFactor (n k : ℕ) : ℝ :=
  (2 * (Nat.factorial n : ℝ) * (Nat.factorial (n + 1) : ℝ) *
      (Nat.factorial (n + 2) : ℝ)) /
    ((Nat.factorial k : ℝ) * (Nat.factorial (k + 1) : ℝ) *
      (Nat.factorial (k + 2) : ℝ) * (Nat.factorial (n + 2 - k) : ℝ) *
      (Nat.factorial (n + 3 - k) : ℝ) * (Nat.factorial (n + 4 - k) : ℝ))

private lemma modelCoeff_succ_succ_factor {n k : ℕ} :
    modelCoeff (n + 2) k =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) ^ 2 *
        ((n : ℝ) + 4) * commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hn₂ := factorial_succ_cast (n + 1)
  have hn₃ := factorial_succ_cast (n + 2)
  have hn₄ := factorial_succ_cast (n + 3)
  rw [modelCoeff, commonFactor]
  grind

private lemma modelCoeff_succ_factor {n k : ℕ} (hk : k ≤ n) :
    modelCoeff (n + 1) k =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) *
        ((n : ℝ) + 4 - k) * ((n : ℝ) + 3 - k) * ((n : ℝ) + 2 - k) *
          commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hn₂ := factorial_succ_cast (n + 1)
  have hn₃ := factorial_succ_cast (n + 2)
  have hs₁ := factorial_succ_cast (n + 1 - k)
  have hs₂ := factorial_succ_cast (n + 1 - k + 1)
  have hs₃ := factorial_succ_cast (n + 1 - k + 1 + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hn₂ hn₃ hs₁ hs₂ hs₃ ⊢
  simp only [show n + 1 + 1 = n + 2 by lia,
    show n + 1 + 2 = n + 3 by lia]
  rw [show n + 4 - k = (n + 3 - k) + 1 by lia,
    show n + 3 - k = (n + 2 - k) + 1 by lia,
    show n + 2 - k = (n + 1 - k) + 1 by lia]
  rw [hs₃, hs₂, hs₁, hn₃, hn₂, hn₁]
  field_simp
  rw [Nat.cast_sub (by lia : k ≤ n + 1)]
  grind

private lemma modelCoeff_succ_pred_factor {n k : ℕ} (hk : 1 ≤ k) :
    modelCoeff (n + 1) (k - 1) =
      (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) *
        ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) *
          commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hn₂ := factorial_succ_cast (n + 1)
  have hn₃ := factorial_succ_cast (n + 2)
  have hk₀ := factorial_succ_cast (k - 1)
  have hk₁ := factorial_succ_cast (k - 1 + 1)
  have hk₂ := factorial_succ_cast (k - 1 + 1 + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hn₂ hn₃ hk₀ hk₁ hk₂ ⊢
  simp only [show n + 1 + 1 = n + 2 by lia,
    show n + 1 + 2 = n + 3 by lia,
    show k - 1 + 1 = k by lia,
    show k - 1 + 2 = k + 1 by lia,
    show n + 1 - (k - 1) = n + 2 - k by lia,
    show n + 1 + 1 - (k - 1) = n + 3 - k by lia,
    show n + 1 + 2 - (k - 1) = n + 4 - k by lia]
  rw [show k + 1 = (k - 1) + 1 + 1 by lia,
    show k + 2 = (k - 1) + 1 + 1 + 1 by lia]
  rw [hk₂, hk₁, hk₀, hn₃, hn₂, hn₁]
  field_simp
  rw [Nat.cast_sub (by assumption : 1 ≤ k)]
  grind

private lemma modelCoeff_factor {n k : ℕ} (hk : k ≤ n) :
    modelCoeff n k =
      ((n : ℝ) + 4 - k) * ((n : ℝ) + 3 - k) ^ 2 *
        ((n : ℝ) + 2 - k) ^ 2 * ((n : ℝ) + 1 - k) *
          commonFactor n k := by
  have h₀ := factorial_succ_cast (n - k)
  have h₁ := factorial_succ_cast (n - k + 1)
  have h₂ := factorial_succ_cast (n - k + 2)
  have h₃ := factorial_succ_cast (n - k + 3)
  rw [modelCoeff, commonFactor]
  push_cast at h₀ h₁ h₂ h₃ ⊢
  rw [show n + 1 - k = (n - k) + 1 by lia,
    show n + 2 - k = (n - k) + 1 + 1 by lia,
    show n + 3 - k = (n - k) + 1 + 1 + 1 by lia,
    show n + 4 - k = (n - k) + 1 + 1 + 1 + 1 by lia]
  rw [h₃, h₂, h₁, h₀]
  field_simp
  rw [Nat.cast_sub hk]
  ring

private lemma modelCoeff_pred_factor {n k : ℕ} (hk₀ : 1 ≤ k) (hk₁ : k ≤ n) :
    modelCoeff n (k - 1) =
      (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) *
        ((n : ℝ) + 4 - k) * ((n : ℝ) + 3 - k) * ((n : ℝ) + 2 - k) *
          commonFactor n k := by
  have hkfac₀ := factorial_succ_cast (k - 1)
  have hkfac₁ := factorial_succ_cast (k - 1 + 1)
  have hkfac₂ := factorial_succ_cast (k - 1 + 1 + 1)
  have hnfac₀ := factorial_succ_cast (n + 1 - k)
  have hnfac₁ := factorial_succ_cast (n + 1 - k + 1)
  have hnfac₂ := factorial_succ_cast (n + 1 - k + 1 + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hkfac₀ hkfac₁ hkfac₂ hnfac₀ hnfac₁ hnfac₂ ⊢
  simp only [show k - 1 + 1 = k by lia,
    show k - 1 + 2 = k + 1 by lia,
    show n - (k - 1) = n + 1 - k by lia,
    show n + 1 - (k - 1) = n + 2 - k by lia,
    show n + 2 - (k - 1) = n + 3 - k by lia]
  rw [show k + 1 = (k - 1) + 1 + 1 by lia,
    show k + 2 = (k - 1) + 1 + 1 + 1 by lia,
    show n + 2 - k = (n + 1 - k) + 1 by lia,
    show n + 3 - k = (n + 1 - k) + 1 + 1 by lia,
    show n + 4 - k = (n + 1 - k) + 1 + 1 + 1 by lia]
  rw [hkfac₂, hkfac₁, hkfac₀, hnfac₂, hnfac₁, hnfac₀]
  field_simp
  rw [Nat.cast_sub (by assumption : 1 ≤ k),
    Nat.cast_sub (by lia : k ≤ n + 1)]
  grind

private lemma modelCoeff_pred_pred_factor {n k : ℕ} (hk : 2 ≤ k) :
    modelCoeff n (k - 2) =
      (k : ℝ) ^ 2 * ((k : ℝ) - 1) * ((k : ℝ) + 1) ^ 2 *
        ((k : ℝ) + 2) * commonFactor n k := by
  have hkm₁ := factorial_cast_pred (by lia : k - 1 ≠ 0)
  rw [show k - 1 - 1 = k - 2 by lia,
    Nat.cast_sub (by lia : 1 ≤ k)] at hkm₁
  norm_num at hkm₁
  have hkfac := factorial_cast_pred (by lia : k ≠ 0)
  rw [hkm₁] at hkfac
  have hkfac₁ := factorial_succ_cast k
  have hkfac₂ := factorial_succ_cast (k + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hkfac₁ hkfac₂ ⊢
  simp only [show k - 2 + 1 = k - 1 by lia,
    show k - 2 + 2 = k by lia,
    show n - (k - 2) = n + 2 - k by lia,
    show n + 1 - (k - 2) = n + 3 - k by lia,
    show n + 2 - (k - 2) = n + 4 - k by lia]
  rw [hkfac₂, hkfac₁, hkfac, hkm₁]
  field_simp
  ring

private lemma modelCoeff_rec_interior {n k : ℕ} (hk₀ : 2 ≤ k) (hk₁ : k ≤ n) :
    (((n : ℝ) + 5) * ((n : ℝ) + 6)) * modelCoeff (n + 2) k =
      (3 * (3 * (n : ℝ) + 10) * k + (-(n : ℝ) ^ 2 + 5 * (n : ℝ) + 26)) *
          modelCoeff (n + 1) k
        + (-3 * (3 * (n : ℝ) + 10) * ((k : ℝ) - 1) +
              4 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 7)) *
            modelCoeff (n + 1) (k - 1)
        + (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) *
            (modelCoeff n k + 2 * modelCoeff n (k - 1) +
              modelCoeff n (k - 2)) := by
  rw [modelCoeff_succ_succ_factor,
    modelCoeff_succ_factor hk₁,
    modelCoeff_succ_pred_factor (by lia),
    modelCoeff_factor hk₁,
    modelCoeff_pred_factor (by lia) hk₁,
    modelCoeff_pred_pred_factor hk₀]
  ring

private lemma coeff_schurModel_eq_coeff {n k : ℕ} (hk : k ≤ n) :
    (schurModel n).coeff k = modelCoeff n k := by
  rw [schurModel, coeff_schurSzegoComp_of_le hk,
    coeff_narayanaPolynomial_of_le hk, coeff_narayanaPolynomial_of_le hk,
    narayanaTransformCoeff_eq_factorial 1 n k hk,
    narayanaTransformCoeff_eq_factorial 2 n k hk,
    Nat.cast_choose ℝ hk, modelCoeff]
  have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  have hk₁ := factorial_succ_cast k
  have hk₂ := factorial_succ_cast (k + 1)
  push_cast at hk₁ hk₂
  norm_num [Nat.factorial_succ]
  field_simp [hfac]
  grind

private lemma coeff_schurModel_eq_zero_of_lt {n k : ℕ} (hk : n < k) :
    (schurModel n).coeff k = 0 := by
  rw [schurModel, coeff_schurSzegoComp_eq_zero_of_lt hk]

private lemma modelCoeff_symm {n k : ℕ} (hk : k ≤ n) :
    modelCoeff n (n - k) = modelCoeff n k := by
  unfold modelCoeff
  simp only [show n - (n - k) = k by lia,
    show n - k + 1 = n + 1 - k by lia,
    show n - k + 2 = n + 2 - k by lia,
    show n + 1 - (n - k) = k + 1 by lia,
    show n + 2 - (n - k) = k + 2 by lia]
  ring

@[simp] private lemma coeff_zero_schurModel (n : ℕ) :
    (schurModel n).coeff 0 = 1 := by
  rw [schurModel, coeff_schurSzegoComp_of_le (Nat.zero_le n)]
  simp

private lemma coeff_schurModel_symm {n k : ℕ} (hk : k ≤ n) :
    (schurModel n).coeff (n - k) = (schurModel n).coeff k := by
  rw [coeff_schurModel_eq_coeff (Nat.sub_le n k),
    coeff_schurModel_eq_coeff hk, modelCoeff_symm hk]

@[simp] private lemma coeff_self_schurModel (n : ℕ) :
    (schurModel n).coeff n = 1 := by
  simpa using coeff_schurModel_symm (n := n) (k := 0) (Nat.zero_le n)

private lemma coeff_one_schurModel (n : ℕ) (hn : 1 ≤ n) :
    (schurModel n).coeff 1 =
      (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 6 := by
  rw [coeff_schurModel_eq_coeff hn, modelCoeff]
  have hn₀ := factorial_cast_pred (by lia : n ≠ 0)
  have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
    fun m ↦ Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  norm_num [Nat.factorial_succ]
  grind

private lemma coeff_pred_schurModel (n : ℕ) (hn : 1 ≤ n) :
    (schurModel n).coeff (n - 1) =
      (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 6 := by
  rw [coeff_schurModel_symm hn, coeff_one_schurModel n hn]

private lemma schurModel_splits (n : ℕ) : (schurModel n).Splits := by
  rw [schurModel]
  apply splits_schurSzegoComp_of_isPF n
    (narayanaPolynomial 1 n) (narayanaPolynomial 2 n)
    (narayanaPolynomialRootLocation 1 n)
  · exact narayanaPolynomial_ne_zero 1 n
  · exact natDegree_narayanaPolynomial_le 1 n
  · exact narayanaPolynomial_ne_zero 2 n
  · exact natDegree_narayanaPolynomial_le 2 n
  · exact (narayanaPolynomialRootLocation 2 n).eq_zero_or_splits.resolve_left
      (narayanaPolynomial_ne_zero 2 n)

private lemma polynomial_succ_normalized (n : ℕ) :
    polynomial (n + 2) =
      C (3 * (3 * (n : ℝ) + 10) / (((n : ℝ) + 5) * ((n : ℝ) + 6))) *
          ((X - X ^ 2) * (polynomial (n + 1)).derivative)
        + (C ((-(n : ℝ) ^ 2 + 5 * (n : ℝ) + 26) /
              (((n : ℝ) + 5) * ((n : ℝ) + 6)))
            + C (4 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 7) /
              (((n : ℝ) + 5) * ((n : ℝ) + 6))) * X) *
          polynomial (n + 1)
        + C (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) /
              (((n : ℝ) + 5) * ((n : ℝ) + 6))) *
            ((1 + 2 * X + X ^ 2) * polynomial n) := by
  rw [polynomial, nextRow, denominator]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
    eval_one, eval_ofNat]
  grind

private lemma schurModel_succ (n : ℕ) :
    schurModel (n + 2) =
      C (3 * (3 * (n : ℝ) + 10) / (((n : ℝ) + 5) * ((n : ℝ) + 6))) *
          ((X - X ^ 2) * (schurModel (n + 1)).derivative)
        + (C ((-(n : ℝ) ^ 2 + 5 * (n : ℝ) + 26) /
              (((n : ℝ) + 5) * ((n : ℝ) + 6)))
            + C (4 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 7) /
              (((n : ℝ) + 5) * ((n : ℝ) + 6))) * X) *
          schurModel (n + 1)
        + C (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) /
              (((n : ℝ) + 5) * ((n : ℝ) + 6))) *
            ((1 + 2 * X + X ^ 2) * schurModel n) := by
  simp only [sub_mul, add_mul, mul_add, pow_two, one_mul, mul_assoc]
  ext k
  rcases k with _ | _ | k
  · simp
    have h₁ : (n : ℝ) + 5 ≠ 0 := by positivity
    have h₂ : (n : ℝ) + 6 ≠ 0 := by positivity
    grind
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_X_mul_zero, coeff_derivative, coeff_ofNat_mul]
    cases n with
    | zero =>
        simp [coeff_one_schurModel, coeff_schurModel_eq_zero_of_lt]
        norm_num
    | succ n =>
        rw [coeff_one_schurModel (n + 3) (by lia),
          coeff_one_schurModel (n + 2) (by lia),
          coeff_one_schurModel (n + 1) (by lia)]
        simp only [coeff_zero_schurModel]
        have h₁ : ((n : ℝ) + 1) + 5 ≠ 0 := by positivity
        have h₂ : ((n : ℝ) + 1) + 6 ≠ 0 := by positivity
        grind
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_derivative, coeff_ofNat_mul]
    by_cases hk : k + 2 ≤ n
    · rw [coeff_schurModel_eq_coeff (by lia : k + 2 ≤ n + 2),
        coeff_schurModel_eq_coeff (by lia : k + 2 ≤ n + 1),
        coeff_schurModel_eq_coeff (by lia : k + 1 ≤ n + 1),
        coeff_schurModel_eq_coeff hk,
        coeff_schurModel_eq_coeff (by lia : k + 1 ≤ n),
        coeff_schurModel_eq_coeff (by lia : k ≤ n)]
      have hrec := modelCoeff_rec_interior
        (n := n) (k := k + 2) (by lia) hk
      have h₁ : (n : ℝ) + 5 ≠ 0 := by positivity
      have h₂ : (n : ℝ) + 6 ≠ 0 := by positivity
      field_simp [h₁, h₂]
      grind
    · have hcases :
          k + 2 = n + 1 ∨ k + 2 = n + 2 ∨ n + 2 < k + 2 := by lia
      rcases hcases with hnext | htop | habove
      · have hn : n = k + 1 := by lia
        subst n
        have ht :
            (schurModel (k + 3)).coeff (k + 2) =
              ((k + 3 : ℕ) : ℝ) * (((k + 3 : ℕ) : ℝ) + 1) *
                (((k + 3 : ℕ) : ℝ) + 2) / 6 := by
          simpa only [show k + 3 - 1 = k + 2 by lia] using
            coeff_pred_schurModel (k + 3) (by lia)
        have hq :
            (schurModel (k + 2)).coeff (k + 1) =
              ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) + 1) *
                (((k + 2 : ℕ) : ℝ) + 2) / 6 := by
          simpa only [show k + 2 - 1 = k + 1 by lia] using
            coeff_pred_schurModel (k + 2) (by lia)
        have hr :
            (schurModel (k + 1)).coeff k =
              ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) *
                (((k + 1 : ℕ) : ℝ) + 2) / 6 := by
          simpa only [show k + 1 - 1 = k by lia] using
            coeff_pred_schurModel (k + 1) (by lia)
        rw [ht, coeff_self_schurModel, hq,
          coeff_schurModel_eq_zero_of_lt (by lia : k + 1 < k + 2),
          coeff_self_schurModel, hr]
        have h₁ : ((k : ℝ) + 1) + 5 ≠ 0 := by positivity
        have h₂ : ((k : ℝ) + 1) + 6 ≠ 0 := by positivity
        grind
      · have hn : n = k := by lia
        subst n
        rw [coeff_self_schurModel,
          coeff_schurModel_eq_zero_of_lt (by lia : k + 1 < k + 2),
          coeff_self_schurModel,
          coeff_schurModel_eq_zero_of_lt (by lia : k < k + 2),
          coeff_schurModel_eq_zero_of_lt (by lia : k < k + 1),
          coeff_self_schurModel]
        have h₁ : (k : ℝ) + 5 ≠ 0 := by positivity
        have h₂ : (k : ℝ) + 6 ≠ 0 := by positivity
        grind
      · rw [coeff_schurModel_eq_zero_of_lt (by assumption : n + 2 < k + 2),
          coeff_schurModel_eq_zero_of_lt (by lia : n + 1 < k + 2),
          coeff_schurModel_eq_zero_of_lt (by lia : n + 1 < k + 1),
          coeff_schurModel_eq_zero_of_lt (by lia : n < k + 2),
          coeff_schurModel_eq_zero_of_lt (by lia : n < k + 1),
          coeff_schurModel_eq_zero_of_lt (by lia : n < k)]
        ring

private lemma schurModel_zero : schurModel 0 = 1 := by
  apply Polynomial.ext
  intro k
  rcases k with _ | k
  · simp
  · rw [coeff_schurModel_eq_zero_of_lt (by lia : 0 < k + 1), coeff_one]
    simp

private lemma schurModel_one : schurModel 1 = 1 + X := by
  apply Polynomial.ext
  intro k
  rcases k with _ | _ | k
  · simp
  · rw [coeff_self_schurModel, coeff_add, coeff_one, coeff_X]
    simp
  · rw [coeff_schurModel_eq_zero_of_lt (by lia : 1 < k + 2)]
    simp only [coeff_add, coeff_one, coeff_X]
    simp

private lemma polynomial_eq_schur : ∀ n : ℕ, polynomial n = schurModel n
  | 0 => by rw [show polynomial 0 = 1 from rfl, schurModel_zero]
  | 1 => by rw [show polynomial 1 = 1 + X from rfl, schurModel_one]
  | n + 2 => by
      rw [polynomial_succ_normalized n, polynomial_eq_schur (n + 1),
        polynomial_eq_schur n, ← schurModel_succ n]

private def jensenWeight (k : ℕ) : ℝ :=
  2 / ((Nat.factorial (k + 1) : ℝ) * (Nat.factorial (k + 2) : ℝ))

private lemma ascPochhammer_eval_two (k : ℕ) :
    (ascPochhammer ℝ k).eval 2 = ((k + 1).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (k + 1)]
      push_cast
      ring

private lemma two_mul_ascPochhammer_eval_three (k : ℕ) :
    2 * (ascPochhammer ℝ k).eval 3 = ((k + 2).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, Nat.factorial_succ (k + 2)]
      push_cast
      nlinarith

private lemma jensenWeight_eq (k : ℕ) :
    jensenWeight k =
      ((ascPochhammer ℝ k).eval 2)⁻¹ * ((ascPochhammer ℝ k).eval 3)⁻¹ := by
  rw [jensenWeight, ascPochhammer_eval_two]
  have hthree := two_mul_ascPochhammer_eval_three k
  have hfac1 : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hfac2 : ((k + 2).factorial : ℝ) ≠ 0 := by positivity
  have hthreePos : 0 < (ascPochhammer ℝ k).eval 3 :=
    ascPochhammer_pos k 3 (by norm_num)
  field_simp
  nlinarith

private lemma jensenWeight_pos (k : ℕ) : 0 < jensenWeight k := by
  rw [jensenWeight]
  positivity

private lemma jensenWeight_multiplier : IsMultiplierSequence jensenWeight := by
  have hpf := (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 2)).mul
    (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 3))
  have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
  rw [show jensenWeight = fun k =>
      ((ascPochhammer ℝ k).eval 2)⁻¹ * ((ascPochhammer ℝ k).eval 3)⁻¹ by
    funext k
    exact jensenWeight_eq k]
  exact hmult

private def jensenScale (n : ℕ) : ℝ :=
  ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial (n + 2) : ℝ)) / 2

private lemma schurModel_eq_jensenModel (n : ℕ) :
    schurModel n = C (jensenScale n) *
      twoSidedJensenPolynomial n jensenWeight jensenWeight := by
  apply Polynomial.ext
  intro k
  rw [coeff_C_mul,
    coeff_twoSidedJensenPolynomial jensenWeight_pos n jensenWeight k]
  by_cases hk : k ≤ n
  · rw [coeff_schurModel_eq_coeff hk, ite_eq_left hk, modelCoeff,
      jensenScale, jensenWeight, jensenWeight, Nat.cast_choose ℝ hk]
    simp only [show n - k + 1 = n + 1 - k by lia,
      show n - k + 2 = n + 2 - k by lia]
    have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
      fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
    field_simp [hfac]
  · rw [coeff_schurModel_eq_zero_of_lt (Nat.lt_of_not_ge hk), ite_eq_right hk,
      mul_zero]

/-- Consecutive A056939 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  rw [polynomial_eq_schur, polynomial_eq_schur, schurModel_eq_jensenModel,
    schurModel_eq_jensenModel]
  have hinter := strictInterl_twoSidedJensenPolynomial_succ
    jensenWeight_multiplier jensenWeight_multiplier jensenWeight_pos jensenWeight_pos n
  exact (hinter.C_mul_left (by rw [jensenScale]; positivity)).C_mul_right
    (by rw [jensenScale]; positivity)

/-- Consecutive A056939 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_eq_schur, polynomial_eq_schur]
    rw [schurModel_eq_jensenModel, schurModel_eq_jensenModel,
      natDegree_C_mul (by rw [jensenScale]; positivity),
      natDegree_C_mul (by rw [jensenScale]; positivity),
      natDegree_twoSidedJensenPolynomial jensenWeight_pos jensenWeight_pos,
      natDegree_twoSidedJensenPolynomial jensenWeight_pos jensenWeight_pos])

/-- Every A056939 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  rw [polynomial_eq_schur]
  exact schurModel_splits n

/-- A sequence with the A056939 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl))
    (hone.trans (show (1 + X : ℝ[X]) = polynomial 1 by rfl))
    hrec (fun _ => rfl)
  rw [heq n]
  exact polynomial_splits n

/-- A sequence with the A056939 initial rows and update has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl))
    (hone.trans (show (1 + X : ℝ[X]) = polynomial 1 by rfl))
    hrec (fun _ => rfl)
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A056939
