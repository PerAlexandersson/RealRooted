import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence

/-!
# Modified-Narayana PF and base interlacing facts

This module contains the low-rank base cases, the shifted/unshifted Lemma 3.4
wrappers, and the PF-polynomial consequences used by explicit certificates.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The concrete `G_2` auxiliary polynomial is twice `P_1`. -/
theorem auxiliaryG_two_eq_C_mul_modifiedNarayanaPolynomial_one :
    FiniteSkewBoard.auxiliaryG 2 =
      C (2 : ℝ) * modifiedNarayanaPolynomial 1 := by
  rw [FiniteSkewBoard.auxiliaryG_two, modifiedNarayanaPolynomial_one]
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  rw [hC2]
  ring_nf

/-- The `n = 2` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_two :
    Prec (FiniteSkewBoard.auxiliaryG 2) (modifiedNarayanaPolynomial 2) := by
  rw [auxiliaryG_two_eq_C_mul_modifiedNarayanaPolynomial_one]
  exact (modifiedNarayanaPolynomial_prec_succ 1).C_mul_left (by norm_num)

/-- The checked initial cases `n = 1, 2` of Braun--Jal Lemma 3.3, for the
concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_two
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 2) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two

/-- The `λ = ν = 0` specialization of Braun--Jal Lemma 3.4 for the concrete
modified Narayana family.  This exposes the Lemma 3.4 target shape while using
the checked consecutive proper-position theorem. -/
theorem lemma34ModifiedNarayanaInterlacing_modified_zero_zero
    {m : ℕ} (_hm : 2 ≤ m) :
    Prec ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) := by
  simpa using modifiedNarayanaPolynomial_prec_succ m

/-- The shifted `λ = 0, μ = 1` specialization of Braun--Jal Lemma 3.4 for the
concrete modified Narayana family. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_modified_zero_one
    {m : ℕ} (hm : 2 ≤ m) :
    Prec ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)) := by
  have hbase := lemma34ModifiedNarayanaInterlacing_modified_zero_zero hm
  have hleft :
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
          narayanaDifference modifiedNarayanaPolynomial m) =
        ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
          modifiedNarayanaPolynomial m) := by
    rw [narayanaDifference]
    simp
  have hright :
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial m +
          narayanaDifference modifiedNarayanaPolynomial (m + 1)) =
        ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial m +
          modifiedNarayanaPolynomial (m + 1)) := by
    rw [narayanaDifference]
    simp only [Nat.add_sub_cancel]
    simp
  rwa [hleft, hright]

/-- Concrete modified-Narayana wrapper: the shifted Lemma 3.4 target implies
the paper-shaped Lemma 3.4 target. -/
theorem lemma34ModifiedNarayanaInterlacing_modified_of_shifted
    (h :
      Lemma34ModifiedNarayanaShiftedInterlacingStatement
        modifiedNarayanaPolynomial) :
    Lemma34ModifiedNarayanaInterlacingStatement modifiedNarayanaPolynomial :=
  lemma34ModifiedNarayanaInterlacing_of_shifted h

/-- Concrete modified-Narayana wrapper: the paper-shaped Lemma 3.4 target
implies the shifted nonnegative-parameter target. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_modified_of_lemma34
    (h : Lemma34ModifiedNarayanaInterlacingStatement modifiedNarayanaPolynomial) :
    Lemma34ModifiedNarayanaShiftedInterlacingStatement
      modifiedNarayanaPolynomial :=
  lemma34ModifiedNarayanaShiftedInterlacing_of_lemma34 h

/-- The coefficient-side modified Narayana family also satisfies the
Braun--Jal modified-family interface. -/
theorem modifiedNarayanaFamily_coeff :
    ModifiedNarayanaFamilyStatement narayana modifiedNarayanaCoeffPolynomial := by
  constructor
  · simp
  · intro n
    rw [← modifiedNarayanaPolynomial_eq_coeffPolynomial]
    exact modifiedNarayanaFamily_narayana.2 n

/-- Coefficient-side modified Narayana polynomials are PF polynomials. -/
theorem modifiedNarayanaCoeffPolynomial_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (modifiedNarayanaCoeffPolynomial n) := by
  simpa [modifiedNarayanaCoeffPolynomial] using
    narayanaPolynomialRootLocation 1 n

/-- Modified Narayana polynomials are PF polynomials. -/
theorem modifiedNarayanaPolynomial_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (modifiedNarayanaPolynomial n) := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial n]
  exact modifiedNarayanaCoeffPolynomial_isPFPolynomial n

/-- Modified Narayana polynomials split over the reals. -/
theorem modifiedNarayanaPolynomial_splits (n : ℕ) :
    (modifiedNarayanaPolynomial n).Splits :=
  (modifiedNarayanaPolynomial_isPFPolynomial n).ne_zero_and_splits
    (modifiedNarayanaPolynomial_ne_zero n) |>.2

/-- The `P_6` modified Narayana polynomial splits over `ℝ`. -/
theorem modifiedNarayanaPolynomial_six_splits : (modifiedNarayanaPolynomial 6).Splits :=
  modifiedNarayanaPolynomial_splits 6

/-- The `P_6` modified Narayana polynomial has a sorted six-root list. -/
theorem modifiedNarayanaPolynomial_six_exists_ordered_roots :
    ∃ a b c d e r : ℝ,
      (modifiedNarayanaPolynomial 6).roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ) ∧
        a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ r := by
  obtain ⟨rs, hrs_eq, hrs_sorted⟩ :
      ∃ rs : List ℝ,
        (↑rs : Multiset ℝ) = (modifiedNarayanaPolynomial 6).roots ∧
          rs.Pairwise (· ≤ ·) :=
    ⟨(modifiedNarayanaPolynomial 6).roots.sort (· ≤ ·),
      Multiset.sort_eq .., Multiset.pairwise_sort ..⟩
  have hlen : rs.length = 6 := by
    rw [← Multiset.coe_card, hrs_eq,
      card_roots_of_splits modifiedNarayanaPolynomial_six_splits]
    exact modifiedNarayanaPolynomial_six_natDegree
  match rs, hlen, hrs_eq, hrs_sorted with
  | [a, b, c, d, e, r], _, hrs_eq, hrs_sorted =>
    exact ⟨a, b, c, d, e, r, hrs_eq.symm, by simp_all⟩

/-- Modified Narayana polynomials are nonzero and split over the reals. -/
theorem modifiedNarayanaPolynomial_ne_zero_and_splits (n : ℕ) :
    modifiedNarayanaPolynomial n ≠ 0 ∧
      (modifiedNarayanaPolynomial n).Splits :=
  (modifiedNarayanaPolynomial_isPFPolynomial n).ne_zero_and_splits
    (modifiedNarayanaPolynomial_ne_zero n)

/-- All real roots of a modified Narayana polynomial are nonpositive. -/
theorem modifiedNarayanaPolynomial_roots_nonpos (n : ℕ) :
    ∀ r ∈ (modifiedNarayanaPolynomial n).roots, r ≤ 0 :=
  (modifiedNarayanaPolynomial_isPFPolynomial n).roots_nonpos

end GeneralizedSnakePosets
end RealRooted
