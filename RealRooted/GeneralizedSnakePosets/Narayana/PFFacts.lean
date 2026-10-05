import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence

/-!
# Modified-Narayana PF and base interlacing facts

This module contains the shifted/unshifted affine-Narayana wrappers and the
PF-polynomial consequences used by explicit certificates.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The `λ = ν = 0` specialization of the affine Narayana interlacing lemma for the concrete
modified Narayana family.  This exposes the affine-Narayana target shape while using
the checked consecutive interlacing theorem. -/
theorem affineModifiedNarayanaInterlacing_modified_zero_zero
    {m : ℕ} :
    StrictInterl ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) := by
  simpa using modifiedNarayanaPolynomial_strictInterl_succ m

/-- The shifted `λ = 0, μ = 1` specialization of the affine Narayana interlacing lemma for the
concrete modified Narayana family. -/
theorem affineModifiedNarayanaShiftedInterlacing_modified_zero_one
    {m : ℕ} :
    StrictInterl ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)) := by
  have hbase := affineModifiedNarayanaInterlacing_modified_zero_zero (m := m)
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

/-- The coefficient-side modified Narayana family also satisfies
`P_0 = 1` and `N_{n+1} = X * P_n`. -/
theorem modifiedNarayanaFamily_coeff :
    modifiedNarayanaCoeffPolynomial 0 = 1 ∧
      ∀ n : ℕ, narayana (n + 1) = X * modifiedNarayanaCoeffPolynomial n := by
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
