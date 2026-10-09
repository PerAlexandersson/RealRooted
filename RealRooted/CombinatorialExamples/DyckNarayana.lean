import RealRooted.Mathlib.Combinatorics.Enumerative.DyckStatistics
import RealRooted.Mathlib.Combinatorics.Enumerative.GenPoly
import RealRooted.NarayanaTransformation.Endpoints

open scoped Polynomial
open Polynomial

namespace DyckWord

noncomputable section

/-- The peak generating polynomial for Dyck words of semilength `n`. -/
def peakGeneratingPolynomial (n : ℕ) : ℝ[X] :=
  Finset.genPoly (Finset.univ : Finset {p : DyckWord // p.semilength = n})
    (fun p => p.1.peakCount)

private lemma cast_narayana_succ_eq_transform (n j : ℕ) :
    (Nat.narayana (n + 1) (j + 1) : ℝ) =
      RealRooted.narayanaTransformCoeff 1 n j := by
  have hN := Nat.narayana_mul (n + 1) (j + 1) (by positivity) (by positivity)
  have hchoose := Nat.add_one_mul_choose_eq n j
  have hchoose' : ((n + 1 : ℕ) : ℝ) * (Nat.choose n j : ℝ) =
      (Nat.choose (n + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  have hN' : ((n + 1 : ℕ) : ℝ) * (Nat.narayana (n + 1) (j + 1) : ℝ) =
      (Nat.choose (n + 1) (j + 1) : ℝ) * (Nat.choose (n + 1) j : ℝ) := by
    exact_mod_cast hN
  dsimp [RealRooted.narayanaTransformCoeff]
  have hden : Nat.choose (1 + j) j = j + 1 := by
    rw [add_comm]
    exact Nat.choose_succ_self_right j
  rw [hden]
  apply (eq_div_iff (by positivity : ((j + 1 : ℕ) : ℝ) ≠ 0)).2
  have h₁ := congrArg (fun x : ℝ => x * ((j + 1 : ℕ) : ℝ)) hN'
  have h₂ : ((n + 1 : ℕ) : ℝ) * (Nat.narayana (n + 1) (j + 1) : ℝ) *
      ((j + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * (Nat.choose n j : ℝ) *
      (Nat.choose (n + 1) j : ℝ) := by
    calc
      _ = (Nat.choose (n + 1) (j + 1) : ℝ) *
          (Nat.choose (n + 1) j : ℝ) * ((j + 1 : ℕ) : ℝ) := h₁
      _ = ((Nat.choose (n + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
          (Nat.choose (n + 1) j : ℝ) := by ring
      _ = (((n + 1 : ℕ) : ℝ) * (Nat.choose n j : ℝ)) *
          (Nat.choose (n + 1) j : ℝ) := by rw [← hchoose']
      _ = _ := by ring
  have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  nlinarith [h₂]

/-- Dyck peak enumeration is the shifted ordinary Narayana polynomial. -/
theorem peakGeneratingPolynomial_eq_narayanaPolynomial (n : ℕ) :
    peakGeneratingPolynomial (n + 1) =
      X * RealRooted.narayanaPolynomial 1 n := by
  ext k
  cases k with
  | zero =>
      rw [peakGeneratingPolynomial, Finset.coeff_genPoly]
      rw [← Fintype.card_subtype]
      have hrhs : (X * RealRooted.narayanaPolynomial 1 n).coeff 0 = (0 : ℝ) := by
        exact Polynomial.coeff_X_mul_zero _
      rw [hrhs]
      cases n with
      | zero =>
          rw [card_semilength_one_peakCount_zero]
          norm_num
      | succ n =>
          rw [card_semilength_peakCount (n + 2) 0 (by lia)]
          have hnara : Nat.narayana (n + 2) 0 = 0 := by
            have hn0 : n + 2 ≠ 0 := by lia
            simp only [Nat.narayana, ite_eq_right hn0]
            simp only [Nat.choose_zero_right, zero_tsub, mul_one]
            exact Nat.div_eq_of_lt (by lia)
          rw [hnara]
          norm_num
  | succ k =>
      rw [peakGeneratingPolynomial, Finset.coeff_genPoly]
      rw [← Fintype.card_subtype]
      rw [card_semilength_peakCount (n + 1) (k + 1) (by lia)]
      rw [Polynomial.coeff_X_mul]
      by_cases hkn : k ≤ n
      · rw [RealRooted.coeff_narayanaPolynomial_of_le (m := 1) (n := n) (k := k) hkn]
        exact_mod_cast cast_narayana_succ_eq_transform n k
      · rw [RealRooted.coeff_narayanaPolynomial_of_lt (m := 1) (n := n) (k := k)
          (Nat.lt_of_not_ge hkn)]
        have hzero : Nat.narayana (n + 1) (k + 1) = 0 := by
          simp [Nat.narayana, Nat.choose_eq_zero_of_lt (by lia : n + 1 < k + 1)]
        simp [hzero]

/-- The Dyck peak generating polynomial is real-rooted for every semilength. -/
theorem isRealRooted_peakGeneratingPolynomial (n : ℕ) :
    peakGeneratingPolynomial (n + 1) ≠ 0 ∧
      (peakGeneratingPolynomial (n + 1)).Splits := by
  rw [peakGeneratingPolynomial_eq_narayanaPolynomial]
  exact RealRooted.isRealRooted_X_mul_of_isRealRooted
    ⟨RealRooted.narayanaPolynomial_ne_zero 1 n,
      RealRooted.splits_narayanaPolynomial 1 n⟩

end

end DyckWord
