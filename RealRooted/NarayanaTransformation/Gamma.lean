import RealRooted.NarayanaTransformation.Recurrences

/-!
# Binomial-square Narayana gamma recurrences.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

private lemma gammaTransform_succ_of_natDegree_le
    {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 1) γ = (X + 1) * gammaTransform d γ := by
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · have hd' : d = 2 * (d / 2) := by lia
    rw [hd']
    exact gammaTransform_odd (d / 2) γ
  · have hd' : d = 2 * (d / 2) + 1 := by lia
    have hcoeff : γ.coeff (d / 2 + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hγ (by lia))
    rw [hd']
    change gammaTransform (2 * (d / 2 + 1)) γ =
      (X + 1) * gammaTransform (2 * (d / 2) + 1) γ
    rw [gammaTransform_even_succ, hcoeff]
    simp

/-- The binomial-square Narayana gamma rows satisfy the transported pure
three-term recurrence. -/
theorem narayanaZeroGammaPolynomial_pure_rec (n : ℕ) :
    C ((n : ℝ) + 2) * narayanaZeroGammaPolynomial (n + 2) =
      C ((2 * n : ℝ) + 3) * narayanaZeroGammaPolynomial (n + 1) -
        C ((n : ℝ) + 1) * (1 - C 4 * X) * narayanaZeroGammaPolynomial n := by
  let γ₂ := C ((n : ℝ) + 2) * narayanaZeroGammaPolynomial (n + 2)
  let γ₁ := C ((2 * n : ℝ) + 3) * narayanaZeroGammaPolynomial (n + 1)
  let γ₀ := C ((n : ℝ) + 1) * (1 - C 4 * X) * narayanaZeroGammaPolynomial n
  have hγ₂ : γ₂.natDegree ≤ (n + 2) / 2 := by
    dsimp [γ₂]
    rw [natDegree_C_mul (by positivity)]
    exact natDegree_narayanaZeroGammaPolynomial_le (n + 2)
  have hγ₁ : γ₁.natDegree ≤ (n + 2) / 2 := by
    dsimp [γ₁]
    rw [natDegree_C_mul (by positivity)]
    exact (natDegree_narayanaZeroGammaPolynomial_le (n + 1)).trans (by lia)
  have hγ₀ : γ₀.natDegree ≤ (n + 2) / 2 := by
    dsimp [γ₀]
    calc
      (C ((n : ℝ) + 1) * (1 - C 4 * X) *
          narayanaZeroGammaPolynomial n).natDegree ≤
          (C ((n : ℝ) + 1) * (1 - C 4 * X)).natDegree +
            (narayanaZeroGammaPolynomial n).natDegree := natDegree_mul_le
      _ ≤ 1 + n / 2 := by
        gcongr
        · compute_degree!
        · exact natDegree_narayanaZeroGammaPolynomial_le n
      _ ≤ (n + 2) / 2 := by lia
  have hγsub : (γ₁ - γ₀).natDegree ≤ (n + 2) / 2 := by
    exact (natDegree_sub_le γ₁ γ₀).trans
      (max_le hγ₁ hγ₀)
  apply gammaTransform_injective_of_natDegree_le hγ₂ hγsub
  dsimp [γ₂, γ₁, γ₀]
  rw [gammaTransform_C_mul, gammaTransform_narayanaZeroGammaPolynomial]
  rw [show C ((2 * n : ℝ) + 3) * narayanaZeroGammaPolynomial (n + 1) -
      C ((n : ℝ) + 1) * (1 - C 4 * X) * narayanaZeroGammaPolynomial n =
      C ((2 * n : ℝ) + 3) * narayanaZeroGammaPolynomial (n + 1) +
        C (-((n : ℝ) + 1)) *
          (narayanaZeroGammaPolynomial n + C (-4) *
            (X * narayanaZeroGammaPolynomial n)) by
              rw [map_neg, map_neg]
              ring]
  rw [gammaTransform_add, gammaTransform_C_mul, gammaTransform_C_mul,
    gammaTransform_add, gammaTransform_C_mul,
    gammaTransform_succ_of_natDegree_le
      (natDegree_narayanaZeroGammaPolynomial_le (n + 1)),
    gammaTransform_pad_two (natDegree_narayanaZeroGammaPolynomial_le n),
    gammaTransform_X_mul_two]
  simp only [gammaTransform_narayanaZeroGammaPolynomial]
  have hrec := narayanaPolynomial_pure_rec 0 n
  simp only [Nat.cast_zero, mul_zero] at hrec
  rw [map_neg, map_neg]
  rw [C_ofNat 4]
  convert hrec using 1 <;> ring_nf

private lemma narayanaZeroGammaCoeff_mul_factorial {n k : ℕ} (hk : 2 * k ≤ n) :
    (Nat.choose n k * Nat.choose (n - k) k) *
        (Nat.factorial k * Nat.factorial k * Nat.factorial (n - 2 * k)) =
      Nat.factorial n := by
  have hkn : k ≤ n := by lia
  have hknk : k ≤ n - k := by lia
  have h₁ : Nat.choose n k *
      (Nat.factorial k * Nat.factorial (n - k)) = Nat.factorial n := by
    simpa [mul_assoc] using Nat.choose_mul_factorial_mul_factorial hkn
  have h₂ : Nat.choose (n - k) k *
      (Nat.factorial k * Nat.factorial (n - 2 * k)) = Nat.factorial (n - k) := by
    rw [show n - 2 * k = n - k - k by lia]
    simpa [mul_assoc] using Nat.choose_mul_factorial_mul_factorial hknk
  calc
    (Nat.choose n k * Nat.choose (n - k) k) *
          (Nat.factorial k * Nat.factorial k * Nat.factorial (n - 2 * k)) =
        Nat.choose n k *
          (Nat.factorial k *
            (Nat.choose (n - k) k *
              (Nat.factorial k * Nat.factorial (n - 2 * k)))) := by ring
    _ = Nat.choose n k *
        (Nat.factorial k * Nat.factorial (n - k)) := by rw [h₂]
    _ = Nat.factorial n := h₁

private lemma coeff_narayanaZeroGammaPolynomial_eq_factorial
    {n k : ℕ} (hk : 2 * k ≤ n) :
    (narayanaZeroGammaPolynomial n).coeff k =
      (Nat.factorial n : ℝ) /
        ((Nat.factorial k : ℝ) ^ 2 * (Nat.factorial (n - 2 * k) : ℝ)) := by
  rw [coeff_narayanaZeroGammaPolynomial_of_le (by lia)]
  have h := congrArg (fun m : ℕ => (m : ℝ))
    (narayanaZeroGammaCoeff_mul_factorial hk)
  push_cast at h
  field_simp [factorial_cast_ne_zero]
  simpa [Nat.cast_mul, pow_two, mul_assoc] using h

private lemma narayanaZeroGammaCoeff_deriv_rec_core
    {n k : ℕ} (hkpos : k ≠ 0) (hk : 2 * k ≤ n) :
    ((n + 1 : ℕ) : ℝ) * (narayanaZeroGammaPolynomial (n + 1)).coeff k =
      (((n + 1 : ℕ) : ℝ) + 2 * (k : ℝ)) *
          (narayanaZeroGammaPolynomial n).coeff k +
        (4 * (n : ℝ) + 8 - 8 * (k : ℝ)) *
          (narayanaZeroGammaPolynomial n).coeff (k - 1) := by
  let F : ℝ := (Nat.factorial n : ℝ) /
    ((Nat.factorial k : ℝ) ^ 2 * Nat.factorial (n - 2 * k + 2))
  have hF₁ : (narayanaZeroGammaPolynomial (n + 1)).coeff k =
      (((n + 1 : ℕ) : ℝ) * ((n - 2 * k + 2 : ℕ) : ℝ)) * F := by
    rw [coeff_narayanaZeroGammaPolynomial_eq_factorial (by lia)]
    dsimp only [F]
    field_simp [factorial_cast_ne_zero]
    rw [factorial_succ_cast n]
    rw [show n - 2 * k + 2 = (n + 1 - 2 * k) + 1 by lia,
      factorial_succ_cast (n + 1 - 2 * k)]
    push_cast
    ring
  have hF₂ : (narayanaZeroGammaPolynomial n).coeff k =
      (((n - 2 * k + 2 : ℕ) : ℝ) *
        ((n - 2 * k + 1 : ℕ) : ℝ)) * F := by
    rw [coeff_narayanaZeroGammaPolynomial_eq_factorial hk]
    dsimp only [F]
    field_simp [factorial_cast_ne_zero]
    rw [show n - 2 * k + 2 = (n - 2 * k + 1) + 1 by lia,
      factorial_succ_cast (n - 2 * k + 1),
      show n - 2 * k + 1 = (n - 2 * k) + 1 by lia,
      factorial_succ_cast (n - 2 * k)]
    push_cast
    ring
  have hF₃ : (narayanaZeroGammaPolynomial n).coeff (k - 1) =
      ((k : ℝ) ^ 2) * F := by
    rw [coeff_narayanaZeroGammaPolynomial_eq_factorial (by lia)]
    dsimp only [F]
    have hkfac : (Nat.factorial k : ℝ) =
        (k : ℝ) * Nat.factorial (k - 1) := factorial_cast_pred hkpos
    have hgap : n - 2 * (k - 1) = n - 2 * k + 2 := by lia
    rw [hgap, hkfac]
    field_simp [factorial_cast_ne_zero]
  rw [hF₁, hF₂, hF₃]
  have hcast : ((n - 2 * k : ℕ) : ℝ) = (n : ℝ) - 2 * (k : ℝ) := by
    rw [Nat.cast_sub hk]
    norm_num
  push_cast
  rw [hcast]
  ring

theorem coeff_narayanaZeroGammaPolynomial_deriv_rec
    (n k : ℕ) (hkpos : k ≠ 0) :
    ((n + 1 : ℕ) : ℝ) * (narayanaZeroGammaPolynomial (n + 1)).coeff k =
      (((n + 1 : ℕ) : ℝ) + 2 * (k : ℝ)) *
          (narayanaZeroGammaPolynomial n).coeff k +
        (4 * (n : ℝ) + 8 - 8 * (k : ℝ)) *
          (narayanaZeroGammaPolynomial n).coeff (k - 1) := by
  by_cases hk : 2 * k ≤ n
  · exact narayanaZeroGammaCoeff_deriv_rec_core hkpos hk
  · by_cases htop : 2 * k ≤ n + 1
    · have heq : 2 * k = n + 1 := by lia
      rw [coeff_narayanaZeroGammaPolynomial_eq_factorial htop,
        coeff_narayanaZeroGammaPolynomial_of_lt (by lia),
        coeff_narayanaZeroGammaPolynomial_eq_factorial (by lia)]
      have hgap₀ : n + 1 - 2 * k = 0 := by lia
      have hgap₁ : n - 2 * (k - 1) = 1 := by lia
      rw [hgap₀, hgap₁]
      norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_zero,
        add_zero]
      field_simp [factorial_cast_ne_zero]
      rw [factorial_succ_cast n, factorial_cast_pred hkpos]
      have heqR := congrArg (fun m : ℕ ↦ (m : ℝ)) heq
      push_cast at heqR ⊢
      have hnR : (n : ℝ) = 2 * (k : ℝ) - 1 := by nlinarith
      rw [hnR]
      ring
    · rw [coeff_narayanaZeroGammaPolynomial_of_lt (by lia),
        coeff_narayanaZeroGammaPolynomial_of_lt (by lia)]
      by_cases hprev : 2 * (k - 1) ≤ n
      · have heq : 2 * k = n + 2 := by lia
        have heqR := congrArg (fun m : ℕ ↦ (m : ℝ)) heq
        push_cast at heqR
        have hfactor : 4 * (n : ℝ) + 8 - 8 * (k : ℝ) = 0 := by nlinarith
        rw [hfactor]
        ring
      · rw [coeff_narayanaZeroGammaPolynomial_of_lt (by lia)]
        ring

/-- The binomial-square Narayana gamma rows satisfy a first-order differential
recurrence. -/
theorem narayanaZeroGammaPolynomial_deriv_rec (n : ℕ) :
    C (((n + 1 : ℕ) : ℝ)) * narayanaZeroGammaPolynomial (n + 1) =
      (C (((n + 1 : ℕ) : ℝ)) + C (4 * (n : ℝ)) * X) *
          narayanaZeroGammaPolynomial n +
        C (2 : ℝ) * X * (1 - C 4 * X) *
          (narayanaZeroGammaPolynomial n).derivative := by
  rw [show C (2 : ℝ) * X * (1 - C 4 * X) =
      C (2 : ℝ) * X - C 8 * X ^ 2 by
        calc
          C (2 : ℝ) * X * (1 - C 4 * X) =
              C 2 * X - (C 2 * C 4) * (X * X) := by ring
          _ = C 2 * X - C 8 * X ^ 2 := by norm_num [← map_mul, pow_two]]
  ext k
  rw [add_mul, sub_mul, mul_assoc, mul_assoc]
  rcases k with _ | _ | k
  · simp [coeff_narayanaZeroGammaPolynomial_of_le]
  · rw [coeff_C_mul,
      coeff_narayanaZeroGammaPolynomial_deriv_rec n 1 one_ne_zero]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative,
      sq, mul_assoc, coeff_X_mul_zero]
    ring
  · rw [coeff_C_mul,
      coeff_narayanaZeroGammaPolynomial_deriv_rec n (k + 2) (by lia)]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative,
      sq, mul_assoc]
    push_cast
    ring


end RealRooted
