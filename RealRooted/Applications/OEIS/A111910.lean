module

public import RealRooted.MultiplierSequence.TwoSidedJensen
public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.Recurrence.RowModel
public import RealRooted.CombinatorialExamples.BigDescentsOddBinom
public import RealRooted.CombinatorialExamples.Narayana
public import RealRooted.Hadamard
public import RealRooted.Hadamard.GarloffWagner
public import RealRooted.NarayanaTransformation

@[expose] public section

open RealRooted Polynomial

/-!
# The A111910 model

The Schur--Szegő model proves that every row splits.  The public transfer theorem
identifies any recurrence presentation with the model by lag-two uniqueness.
-/

noncomputable section

namespace RealRooted.Applications.OEIS.A111910

/-- The positive denominator in the A111910 update. -/
def denominator (n : ℕ) : ℝ :=
  10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ)

/-- The lag-two recurrence operator for A111910. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (C ((1 / denominator n) * (42 + 18 * (n : ℝ))) * X +
      C ((1 / denominator n) * (-42 + (-18 * (n : ℝ)))) * X ^ 2) *
      p.derivative +
    (C ((1 / denominator n) *
        (40 + (-2 * (3 + (n : ℝ)) ^ 2) + 17 * (n : ℝ))) +
      C ((1 / denominator n) *
        (-80 + (-31 * (n : ℝ)) + 16 * (3 + (n : ℝ)) ^ 2)) * X) * p +
    (C ((1 / denominator n) *
        (-30 + (-14 * (n : ℝ)) + 4 * (3 + (n : ℝ)) ^ 2)) +
      C ((1 / denominator n) *
        (-60 + (-28 * (n : ℝ)) + 8 * (3 + (n : ℝ)) ^ 2)) * X +
      C ((1 / denominator n) *
        (-30 + (-14 * (n : ℝ)) + 4 * (3 + (n : ℝ)) ^ 2)) * X ^ 2) * q

/-- The recurrence model for A111910. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => nextRow n (polynomial (n + 1)) (polynomial n)

private noncomputable def schurModel (n : ℕ) : ℝ[X] :=
  C ((2 * (n : ℝ) + 2)⁻¹) *
    schurSzegoComp n
      (BigDescents.oddBinomPolyReal (2 * n + 2))
      (narayanaPolynomial 1 n)

private def modelCoeff (n k : ℕ) : ℝ :=
  ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial (2 * n + 1) : ℝ)) /
    ((Nat.factorial (k + 1) : ℝ) * (Nat.factorial (n + 1 - k) : ℝ) *
      (Nat.factorial (2 * k + 1) : ℝ) *
      (Nat.factorial (2 * n + 1 - 2 * k) : ℝ))

private def commonFactor (n k : ℕ) : ℝ :=
  ((Nat.factorial n : ℝ) * (Nat.factorial (2 * n + 1) : ℝ)) /
    ((Nat.factorial (k + 1) : ℝ) * (Nat.factorial (n + 3 - k) : ℝ) *
      (Nat.factorial (2 * k + 1) : ℝ) *
      (Nat.factorial (2 * n + 5 - 2 * k) : ℝ))

private lemma modelCoeff_succ_succ_factor {n k : ℕ} :
    modelCoeff (n + 2) k =
      4 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) *
        (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) *
          commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hn₂ := factorial_succ_cast (n + 1)
  have hn₃ := factorial_succ_cast (n + 2)
  have h2n₂ := factorial_succ_cast (2 * n + 1)
  have h2n₃ := factorial_succ_cast (2 * n + 2)
  have h2n₄ := factorial_succ_cast (2 * n + 3)
  have h2n₅ := factorial_succ_cast (2 * n + 4)
  rw [modelCoeff, commonFactor]
  grind

private lemma modelCoeff_succ_factor {n k : ℕ} (hk : k ≤ n) :
    modelCoeff (n + 1) k =
      4 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3) *
        ((n : ℝ) + 3 - k) * ((n : ℝ) + 2 - k) *
          (2 * (n : ℝ) + 5 - 2 * k) * commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hn₂ := factorial_succ_cast (n + 1)
  have h2n₂ := factorial_succ_cast (2 * n + 1)
  have h2n₃ := factorial_succ_cast (2 * n + 2)
  have hs₁ := factorial_succ_cast (n + 2 - k)
  have hs₂ := factorial_succ_cast (2 * n + 3 - 2 * k)
  have hs₃ := factorial_succ_cast (2 * n + 3 - 2 * k + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hn₂ h2n₂ h2n₃ hs₁ hs₂ hs₃ ⊢
  simp only [show n + 1 + 1 = n + 2 by lia,
    show 2 * (n + 1) + 1 = 2 * n + 3 by lia]
  rw [show n + 3 - k = (n + 2 - k) + 1 by lia,
    show 2 * n + 5 - 2 * k = (2 * n + 3 - 2 * k) + 1 + 1 by lia]
  rw [hs₁, hs₃, hs₂, hn₂, hn₁, h2n₃, h2n₂]
  field_simp
  rw [Nat.cast_sub (by lia : k ≤ n + 2),
    Nat.cast_sub (by lia : 2 * k ≤ 2 * n + 3)]
  grind

private lemma modelCoeff_succ_pred_factor {n k : ℕ} (hk : 2 ≤ k) :
    modelCoeff (n + 1) (k - 1) =
      4 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) *
        ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3) *
          commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hn₂ := factorial_succ_cast (n + 1)
  have h2n₂ := factorial_succ_cast (2 * n + 1)
  have h2n₃ := factorial_succ_cast (2 * n + 2)
  have hk₁ := factorial_succ_cast k
  have h2k₁ := factorial_succ_cast (2 * k - 1 + 1)
  have h2k₀ := factorial_succ_cast (2 * k - 1)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hn₂ h2n₂ h2n₃ hk₁ h2k₁ h2k₀ ⊢
  simp only [show n + 1 + 1 = n + 2 by lia,
    show 2 * (n + 1) + 1 = 2 * n + 3 by lia,
    show k - 1 + 1 = k by lia,
    show n + 1 + 1 - (k - 1) = n + 3 - k by lia,
    show 2 * (k - 1) + 1 = 2 * k - 1 by lia]
  rw [show 2 * n + 3 - 2 * (k - 1) = 2 * n + 5 - 2 * k by lia]
  rw [show k + 1 = k + 1 by simp,
    show 2 * k + 1 = (2 * k - 1) + 1 + 1 by lia]
  rw [hk₁, h2k₁, h2k₀, hn₂, hn₁, h2n₃, h2n₂]
  field_simp
  rw [Nat.cast_sub (by lia : 1 ≤ 2 * k)]
  grind

private lemma modelCoeff_factor {n k : ℕ} (hk : k ≤ n) :
    modelCoeff n k =
      4 * ((n : ℝ) + 1) * ((n : ℝ) + 3 - k) * ((n : ℝ) + 2 - k) ^ 2 *
        ((n : ℝ) + 1 - k) * (2 * (n : ℝ) + 5 - 2 * k) *
          (2 * (n : ℝ) + 3 - 2 * k) * commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hs₁ := factorial_succ_cast (n + 1 - k)
  have hs₂ := factorial_succ_cast (n + 1 - k + 1)
  have ht₁ := factorial_succ_cast (2 * n + 1 - 2 * k)
  have ht₂ := factorial_succ_cast (2 * n + 1 - 2 * k + 1)
  have ht₃ := factorial_succ_cast (2 * n + 1 - 2 * k + 2)
  have ht₄ := factorial_succ_cast (2 * n + 1 - 2 * k + 3)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hs₁ hs₂ ht₁ ht₂ ht₃ ht₄ ⊢
  rw [show n + 3 - k = (n + 1 - k) + 1 + 1 by lia,
    show 2 * n + 5 - 2 * k = (2 * n + 1 - 2 * k) + 1 + 1 + 1 + 1 by lia]
  rw [hs₂, hs₁, ht₄, ht₃, ht₂, ht₁, hn₁]
  field_simp
  rw [Nat.cast_sub (by lia : k ≤ n + 1),
    Nat.cast_sub (by lia : 2 * k ≤ 2 * n + 1)]
  grind

private lemma modelCoeff_pred_factor {n k : ℕ} (hk₀ : 1 ≤ k) (hk₁ : k ≤ n) :
    modelCoeff n (k - 1) =
      4 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) * ((n : ℝ) + 1) *
        ((n : ℝ) + 3 - k) * ((n : ℝ) + 2 - k) *
          (2 * (n : ℝ) + 5 - 2 * k) * commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hkfac := factorial_succ_cast k
  have h2k₁ := factorial_succ_cast (2 * k - 1)
  have h2k₂ := factorial_succ_cast (2 * k - 1 + 1)
  have hs₁ := factorial_succ_cast (n + 2 - k)
  have ht₁ := factorial_succ_cast (2 * n + 3 - 2 * k)
  have ht₂ := factorial_succ_cast (2 * n + 3 - 2 * k + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hkfac h2k₁ h2k₂ hs₁ ht₁ ht₂ ⊢
  simp only [show k - 1 + 1 = k by lia,
    show n + 1 - (k - 1) = n + 2 - k by lia,
    show 2 * (k - 1) + 1 = 2 * k - 1 by lia]
  rw [show 2 * n + 1 - 2 * (k - 1) = 2 * n + 3 - 2 * k by lia,
    show n + 3 - k = (n + 2 - k) + 1 by lia,
    show 2 * k + 1 = (2 * k - 1) + 1 + 1 by lia,
    show 2 * n + 5 - 2 * k = (2 * n + 3 - 2 * k) + 1 + 1 by lia]
  rw [hkfac, h2k₂, h2k₁, hs₁, ht₂, ht₁, hn₁]
  field_simp
  rw [Nat.cast_sub (by lia : 1 ≤ 2 * k),
    Nat.cast_sub (by lia : k ≤ n + 2),
    Nat.cast_sub (by lia : 2 * k ≤ 2 * n + 3)]
  grind

private lemma modelCoeff_pred_pred_factor {n k : ℕ} (hk : 2 ≤ k) :
    modelCoeff n (k - 2) =
      4 * (k : ℝ) ^ 2 * ((k : ℝ) - 1) * ((k : ℝ) + 1) *
        (2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1) * ((n : ℝ) + 1) *
          commonFactor n k := by
  have hn₁ := factorial_succ_cast n
  have hk₀ := factorial_succ_cast (k - 1)
  have hk₁ := factorial_succ_cast (k - 1 + 1)
  have h2k₀ := factorial_succ_cast (2 * k - 3)
  have h2k₁ := factorial_succ_cast (2 * k - 3 + 1)
  have h2k₂ := factorial_succ_cast (2 * k - 3 + 1 + 1)
  have h2k₃ := factorial_succ_cast (2 * k - 3 + 1 + 1 + 1)
  rw [modelCoeff, commonFactor]
  push_cast at hn₁ hk₀ hk₁ h2k₀ h2k₁ h2k₂ h2k₃ ⊢
  simp only [show k - 2 + 1 = k - 1 by lia,
    show n + 1 - (k - 2) = n + 3 - k by lia,
    show 2 * (k - 2) + 1 = 2 * k - 3 by lia]
  rw [show 2 * n + 1 - 2 * (k - 2) = 2 * n + 5 - 2 * k by lia,
    show k + 1 = (k - 1) + 1 + 1 by lia,
    show 2 * k + 1 = (2 * k - 3) + 1 + 1 + 1 + 1 by lia]
  rw [hk₁, hk₀, h2k₃, h2k₂, h2k₁, h2k₀, hn₁]
  field_simp
  rw [Nat.cast_sub (by lia : 1 ≤ k),
    Nat.cast_sub (by lia : 3 ≤ 2 * k)]
  grind

private lemma modelCoeff_rec_interior {n k : ℕ} (hk₀ : 2 ≤ k) (hk₁ : k ≤ n) :
    (((n : ℝ) + 4) * (2 * (n : ℝ) + 7)) * modelCoeff (n + 2) k =
      (6 * (3 * (n : ℝ) + 7) * k + (-2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) + 22)) *
          modelCoeff (n + 1) k
        + (-6 * (3 * (n : ℝ) + 7) * ((k : ℝ) - 1) +
              (16 * (n : ℝ) ^ 2 + 65 * (n : ℝ) + 64)) *
            modelCoeff (n + 1) (k - 1)
        + (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
            (modelCoeff n k + 2 * modelCoeff n (k - 1) +
              modelCoeff n (k - 2)) := by
  rw [modelCoeff_succ_succ_factor,
    modelCoeff_succ_factor hk₁,
    modelCoeff_succ_pred_factor hk₀,
    modelCoeff_factor hk₁,
    modelCoeff_pred_factor (by lia) hk₁,
    modelCoeff_pred_pred_factor hk₀]
  ring

private lemma modelCoeff_eq_choose {n k : ℕ} (hk : k ≤ n) :
    modelCoeff n k =
      (Nat.choose (n + 1) k : ℝ) * (Nat.choose (2 * n + 1) (2 * k) : ℝ) /
        (((k : ℝ) + 1) * ((2 * k : ℕ) + 1 : ℝ)) := by
  have hk₁ : k ≤ n + 1 := hk.trans (Nat.le_succ n)
  have hk₂ : 2 * k ≤ 2 * n + 1 := by lia
  rw [modelCoeff, Nat.cast_choose ℝ hk₁, Nat.cast_choose ℝ hk₂]
  have hkfac := factorial_succ_cast k
  have h2kfac := factorial_succ_cast (2 * k)
  grind

private lemma modelCoeff_symm {n k : ℕ} (hk : k ≤ n) :
    modelCoeff n (n - k) = modelCoeff n k := by
  unfold modelCoeff
  simp only [show n - k + 1 = n + 1 - k by lia,
    show n + 1 - (n - k) = k + 1 by lia,
    show 2 * (n - k) + 1 = 2 * n + 1 - 2 * k by lia,
    show 2 * n + 1 - 2 * (n - k) = 2 * k + 1 by lia]
  ring

private lemma oddBinom_nonneg (n : ℕ) :
    HasNonnegCoeffs (BigDescents.oddBinomPolyReal (2 * n + 2)) := by
  intro k
  rw [BigDescents.coeff_oddBinomPolyReal]
  positivity

private lemma oddBinom_pf (n : ℕ) :
    IsPFPolynomial (BigDescents.oddBinomPolyReal (2 * n + 2)) := by
  apply IsPFPolynomial.of_realRooted_nonneg (oddBinom_nonneg n)
  exact (BigDescents.oddBinomPolyReal_isRealRooted (2 * n + 2) (by lia)).2

private lemma schurModel_splits (n : ℕ) : (schurModel n).Splits := by
  have hcomp :
      (schurSzegoComp n
        (BigDescents.oddBinomPolyReal (2 * n + 2))
        (narayanaPolynomial 1 n)).Splits := by
    apply splits_schurSzegoComp_of_isPF n
      (BigDescents.oddBinomPolyReal (2 * n + 2))
      (narayanaPolynomial 1 n)
      (oddBinom_pf n)
    · exact BigDescents.oddBinomPolyReal_ne_zero (2 * n + 2) (by lia)
    · rw [BigDescents.oddBinomPolyReal_natDegree (2 * n + 2) (by lia)]
      lia
    · exact (narayanaPolynomialRootLocation 1 n).ne_zero_and_splits
        (by
          intro hzero
          have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
          simp at hcoeff)
        |>.1
    · exact natDegree_narayanaPolynomial_le 1 n
    · exact (narayanaPolynomialRootLocation 1 n).eq_zero_or_splits.resolve_left
        (by
          intro hzero
          have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
          simp at hcoeff)
  exact (Polynomial.Splits.C ((2 * (n : ℝ) + 2)⁻¹)).mul hcomp

private lemma coeff_schurModel_of_le {n k : ℕ} (hk : k ≤ n) :
    (schurModel n).coeff k =
      (Nat.choose (n + 1) k : ℝ) * (Nat.choose (2 * n + 1) (2 * k) : ℝ) /
        (((k : ℝ) + 1) * ((2 * k : ℕ) + 1 : ℝ)) := by
  rw [schurModel, coeff_C_mul, coeff_schurSzegoComp_of_le hk,
    BigDescents.coeff_oddBinomPolyReal,
    coeff_narayanaPolynomial_of_le hk]
  simp only [narayanaTransformCoeff]
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero (R := ℝ) hk
  have hodd := Nat.add_one_mul_choose_eq (2 * n + 1) (2 * k)
  have hodd_cast :
      ((2 * n + 2 : ℕ) : ℝ) * (Nat.choose (2 * n + 1) (2 * k) : ℝ) =
        (Nat.choose (2 * n + 2) (2 * k + 1) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hodd
  have hnpos : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2kpos : (0 : ℝ) < ((2 * k : ℕ) + 1 : ℝ) := by positivity
  rw [show 1 + k = k + 1 by lia, Nat.choose_succ_self_right]
  field_simp
  grind

private lemma coeff_schurModel_eq_coeff {n k : ℕ} (hk : k ≤ n) :
    (schurModel n).coeff k = modelCoeff n k := by
  rw [coeff_schurModel_of_le hk, modelCoeff_eq_choose hk]

private lemma coeff_schurModel_eq_zero_of_lt {n k : ℕ} (hk : n < k) :
    (schurModel n).coeff k = 0 := by
  rw [schurModel, coeff_C_mul,
    coeff_schurSzegoComp_eq_zero_of_lt hk]
  simp

@[simp] private lemma coeff_zero_schurModel (n : ℕ) :
    (schurModel n).coeff 0 = 1 := by
  rw [coeff_schurModel_of_le (Nat.zero_le n)]
  simp

@[simp] private lemma coeff_self_schurModel (n : ℕ) :
    (schurModel n).coeff n = 1 := by
  rw [coeff_schurModel_of_le le_rfl,
    show n + 1 = n + 1 by simp, Nat.choose_succ_self_right,
    show 2 * n + 1 = 2 * n + 1 by simp, Nat.choose_succ_self_right]
  have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h₂ : (0 : ℝ) < (2 * n : ℕ) + 1 := by positivity
  field_simp
  simp

private lemma coeff_one_schurModel (n : ℕ) (hn : 1 ≤ n) :
    (schurModel n).coeff 1 =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  rw [coeff_schurModel_of_le hn, Nat.choose_one_right,
    Nat.cast_choose_two]
  grind

private lemma coeff_schurModel_symm {n k : ℕ} (hk : k ≤ n) :
    (schurModel n).coeff (n - k) = (schurModel n).coeff k := by
  rw [coeff_schurModel_eq_coeff (Nat.sub_le n k),
    coeff_schurModel_eq_coeff hk, modelCoeff_symm hk]

private lemma coeff_pred_schurModel (n : ℕ) (hn : 1 ≤ n) :
    (schurModel n).coeff (n - 1) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  rw [coeff_schurModel_symm hn, coeff_one_schurModel n hn]

private lemma polynomial_succ_normalized (n : ℕ) :
    polynomial (n + 2) =
      C (6 * (3 * (n : ℝ) + 7) / (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
          ((X - X ^ 2) * (polynomial (n + 1)).derivative)
        + (C ((-2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) + 22) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7)))
            + C ((16 * (n : ℝ) ^ 2 + 65 * (n : ℝ) + 64) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) * X) *
          polynomial (n + 1)
        + C (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
            ((1 + 2 * X + X ^ 2) * polynomial n) := by
  rw [polynomial, nextRow, denominator]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
    eval_one, eval_ofNat]
  grind

private lemma schurModel_succ (n : ℕ) :
    schurModel (n + 2) =
      C (6 * (3 * (n : ℝ) + 7) / (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
          ((X - X ^ 2) * (schurModel (n + 1)).derivative)
        + (C ((-2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) + 22) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7)))
            + C ((16 * (n : ℝ) ^ 2 + 65 * (n : ℝ) + 64) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) * X) *
          schurModel (n + 1)
        + C (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
            ((1 + 2 * X + X ^ 2) * schurModel n) := by
  rw [show
      C (6 * (3 * (n : ℝ) + 7) / (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
          ((X - X ^ 2) * (schurModel (n + 1)).derivative) =
        C (6 * (3 * (n : ℝ) + 7) / (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
            (X * (schurModel (n + 1)).derivative) -
          C (6 * (3 * (n : ℝ) + 7) / (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
            (X * (X * (schurModel (n + 1)).derivative)) by ring,
    show
      (C ((-2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) + 22) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7)))
            + C ((16 * (n : ℝ) ^ 2 + 65 * (n : ℝ) + 64) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) * X) *
          schurModel (n + 1) =
        C ((-2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) + 22) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) * schurModel (n + 1) +
          C ((16 * (n : ℝ) ^ 2 + 65 * (n : ℝ) + 64) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
            (X * schurModel (n + 1)) by ring,
    show
      C (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
            ((1 + 2 * X + X ^ 2) * schurModel n) =
        C (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) /
              (((n : ℝ) + 4) * (2 * (n : ℝ) + 7))) *
          (schurModel n + 2 * (X * schurModel n) +
            X * (X * schurModel n)) by ring]
  ext k
  rcases k with _ | _ | k
  · simp only [coeff_zero_schurModel, neg_mul, coeff_add, coeff_sub,
      mul_coeff_zero, coeff_C_zero, coeff_X_zero, zero_mul, mul_zero,
      sub_self, mul_one, add_zero, zero_add, coeff_ofNat_mul]
    have h₁ : (n : ℝ) + 4 ≠ 0 := by positivity
    have h₂ : 2 * (n : ℝ) + 7 ≠ 0 := by positivity
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
        have h₁ : ((n : ℝ) + 1) + 4 ≠ 0 := by positivity
        have h₂ : 2 * ((n : ℝ) + 1) + 7 ≠ 0 := by positivity
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
      have h₁ : (n : ℝ) + 4 ≠ 0 := by positivity
      have h₂ : 2 * (n : ℝ) + 7 ≠ 0 := by positivity
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
                (2 * ((k + 3 : ℕ) : ℝ) + 1) / 6 := by
          simpa only [show k + 3 - 1 = k + 2 by lia] using
            coeff_pred_schurModel (k + 3) (by lia)
        have hq :
            (schurModel (k + 2)).coeff (k + 1) =
              ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) + 1) *
                (2 * ((k + 2 : ℕ) : ℝ) + 1) / 6 := by
          simpa only [show k + 2 - 1 = k + 1 by lia] using
            coeff_pred_schurModel (k + 2) (by lia)
        have hr :
            (schurModel (k + 1)).coeff k =
              ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) *
                (2 * ((k + 1 : ℕ) : ℝ) + 1) / 6 := by
          simpa only [show k + 1 - 1 = k by lia] using
            coeff_pred_schurModel (k + 1) (by lia)
        rw [ht, coeff_self_schurModel, hq,
          coeff_schurModel_eq_zero_of_lt (by lia : k + 1 < k + 2),
          coeff_self_schurModel, hr]
        have h₁ : ((k : ℝ) + 1) + 4 ≠ 0 := by positivity
        have h₂ : 2 * ((k : ℝ) + 1) + 7 ≠ 0 := by positivity
        grind
      · have hn : n = k := by lia
        subst n
        rw [coeff_self_schurModel,
          coeff_schurModel_eq_zero_of_lt (by lia : k + 1 < k + 2),
          coeff_self_schurModel,
          coeff_schurModel_eq_zero_of_lt (by lia : k < k + 2),
          coeff_schurModel_eq_zero_of_lt (by lia : k < k + 1),
          coeff_self_schurModel]
        have h₁ : (k : ℝ) + 4 ≠ 0 := by positivity
        have h₂ : 2 * (k : ℝ) + 7 ≠ 0 := by positivity
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
  (4 : ℝ) ^ k * (Nat.factorial k : ℝ) /
    ((Nat.factorial (k + 1) : ℝ) * (Nat.factorial (2 * k + 1) : ℝ))

private lemma ascPochhammer_eval_two (k : ℕ) :
    (ascPochhammer ℝ k).eval 2 = ((k + 1).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (k + 1)]
      push_cast
      ring

private lemma ascPochhammer_eval_three_halves (k : ℕ) :
    (4 : ℝ) ^ k * (Nat.factorial k : ℝ) *
        (ascPochhammer ℝ k).eval (3 / 2) =
      ((2 * k + 1).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, Nat.factorial_succ k,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by lia,
        Nat.factorial_succ ((2 * k + 1) + 1),
        Nat.factorial_succ (2 * k + 1), pow_succ]
      push_cast
      ring_nf at ih ⊢
      linear_combination (4 * (k : ℝ) ^ 2 + 10 * (k : ℝ) + 6) * ih

private lemma jensenWeight_eq (k : ℕ) :
    jensenWeight k =
      ((ascPochhammer ℝ k).eval 2)⁻¹ *
        ((ascPochhammer ℝ k).eval (3 / 2))⁻¹ := by
  rw [jensenWeight, ascPochhammer_eval_two]
  have hhalf := ascPochhammer_eval_three_halves k
  have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  have hhalfPos : 0 < (ascPochhammer ℝ k).eval (3 / 2) :=
    ascPochhammer_pos k (3 / 2) (by norm_num)
  field_simp [hfac]
  nlinarith

private lemma jensenWeight_pos (k : ℕ) : 0 < jensenWeight k := by
  rw [jensenWeight]
  positivity

private lemma jensenWeight_multiplier : IsMultiplierSequence jensenWeight := by
  have hpf := (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 2)).mul
    (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 3 / 2))
  have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
  rw [show jensenWeight = fun k =>
      ((ascPochhammer ℝ k).eval 2)⁻¹ *
        ((ascPochhammer ℝ k).eval (3 / 2))⁻¹ by
    funext k
    exact jensenWeight_eq k]
  exact hmult

private def jensenScale (n : ℕ) : ℝ :=
  ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial (2 * n + 1) : ℝ)) /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ))

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
      show 2 * (n - k) + 1 = 2 * n + 1 - 2 * k by lia]
    have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
      fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
    have hpow : (4 : ℝ) ^ k * 4 ^ (n - k) = 4 ^ n := by
      rw [← pow_add, show k + (n - k) = n by lia]
    field_simp [hfac]
    rw [hpow]
  · rw [coeff_schurModel_eq_zero_of_lt (Nat.lt_of_not_ge hk), ite_eq_right hk,
      mul_zero]

/-- Consecutive A111910 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  rw [polynomial_eq_schur, polynomial_eq_schur, schurModel_eq_jensenModel,
    schurModel_eq_jensenModel]
  have hinter := strictInterl_twoSidedJensenPolynomial_succ
    jensenWeight_multiplier jensenWeight_multiplier jensenWeight_pos jensenWeight_pos n
  exact (hinter.C_mul_left (by rw [jensenScale]; positivity)).C_mul_right
    (by rw [jensenScale]; positivity)

/-- Consecutive A111910 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_eq_schur, polynomial_eq_schur]
    rw [schurModel_eq_jensenModel, schurModel_eq_jensenModel,
      natDegree_C_mul (by rw [jensenScale]; positivity),
      natDegree_C_mul (by rw [jensenScale]; positivity),
      natDegree_twoSidedJensenPolynomial jensenWeight_pos jensenWeight_pos,
      natDegree_twoSidedJensenPolynomial jensenWeight_pos jensenWeight_pos])

/-- Every A111910 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  rw [polynomial_eq_schur]
  exact schurModel_splits n

/-- A sequence with the A111910 initial rows and update has split rows. -/
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

/-- A sequence with the A111910 initial rows and update has interlacing
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

end RealRooted.Applications.OEIS.A111910
