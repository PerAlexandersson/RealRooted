import RealRooted.ParkingFunctions.ToricContribution.ExceptionalOffset

/-!
# Common interlacer for the A390883 toric-contribution family

This file packages the all-offset Jacobi comparison as a finite-family
common-left-interlacer theorem. It also closes splitness for arbitrary
strictly positive weighted sums of the parity-normalized `R_d` family.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- The parity normalization that gives `R_d` positive leading coefficient. -/
def normalizedRPolynomial (m ε d : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ m) * rPolynomial m ε d

/-- The finite normalized family over all offsets `0 ≤ d ≤ m`. -/
def normalizedRPolynomialFamily (m ε : ℕ) : List ℝ[X] :=
  (Finset.range (m + 1)).toList.map (normalizedRPolynomial m ε)

theorem normalizedRPolynomial_hasPosLeadingCoeff (m ε d : ℕ) :
    HasPosLeadingCoeff (normalizedRPolynomial m ε d) := by
  exact negOnePow_mul_rPolynomial_hasPosLeadingCoeff m ε d

/-- The terminating Jacobi polynomial is a common left interlacer of every
parity-normalized toric-contribution polynomial. -/
theorem normalizedRPolynomialFamily_hasCommonLeftInterleaver
    (m ε : ℕ) (hm : 0 < m) :
    HasCommonLeftInterleaver (normalizedRPolynomialFamily m ε) := by
  refine ⟨jPolynomial m ε, ?_⟩
  intro p hp
  simp only [normalizedRPolynomialFamily, Finset.mem_toList,
    List.mem_map] at hp
  obtain ⟨d, hd, rfl⟩ := hp
  have hdm : d ≤ m := by simpa using hd
  exact prec_C_mul_right
    (jPolynomial_interlaces_rPolynomial m ε d hm hdm).toPrec
    (pow_ne_zero m (by norm_num))

/-- The sum of all parity-normalized toric contributions is split. -/
theorem normalizedRPolynomialFamily_sum_splits
    (m ε : ℕ) (hm : 0 < m) :
    (normalizedRPolynomialFamily m ε).sum.Splits := by
  have hcommon :=
    normalizedRPolynomialFamily_hasCommonLeftInterleaver m ε hm
  have hpositive : ∀ p ∈ normalizedRPolynomialFamily m ε,
      HasPosLeadingCoeff p := by
    intro p hp
    simp only [normalizedRPolynomialFamily, Finset.mem_toList,
      List.mem_map] at hp
    obtain ⟨d, _, rfl⟩ := hp
    exact normalizedRPolynomial_hasPosLeadingCoeff m ε d
  exact (isRealRooted_sum_of_commonLeftInterleaver hcommon hpositive
    (by simp [normalizedRPolynomialFamily])).2

/-- The normalized family with a scalar weight attached to each offset. -/
def weightedNormalizedRPolynomialFamily
    (m ε : ℕ) (w : ℕ → ℝ) : List ℝ[X] :=
  (Finset.range (m + 1)).toList.map
    (fun d => C (w d) * normalizedRPolynomial m ε d)

/-- A strictly positive weight preserves the common-left-interlacer package
for every member of the normalized family. -/
theorem normalizedRPolynomialFamily_weighted_sum_splits
    (m ε : ℕ) (hm : 0 < m) (w : ℕ → ℝ)
    (hw : ∀ d, d ≤ m → 0 < w d) :
    (weightedNormalizedRPolynomialFamily m ε w).sum.Splits := by
  let fs := weightedNormalizedRPolynomialFamily m ε w
  have hcommon : HasCommonLeftInterleaver fs := by
    refine ⟨jPolynomial m ε, ?_⟩
    intro p hp
    simp only [fs, weightedNormalizedRPolynomialFamily,
      Finset.mem_toList, List.mem_map] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    have hdm : d ≤ m := by simpa using hd
    exact prec_C_mul_right
      (prec_C_mul_right
        (jPolynomial_interlaces_rPolynomial m ε d hm hdm).toPrec
        (pow_ne_zero m (by norm_num)))
      (hw d hdm).ne'
  have hpositive : ∀ p ∈ fs, HasPosLeadingCoeff p := by
    intro p hp
    simp only [fs, weightedNormalizedRPolynomialFamily,
      Finset.mem_toList, List.mem_map] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    exact hasPosLeadingCoeff_C_mul (hw d (by simpa using hd))
      (normalizedRPolynomial_hasPosLeadingCoeff m ε d)
  exact (isRealRooted_sum_of_commonLeftInterleaver hcommon hpositive
    (by simp [fs, weightedNormalizedRPolynomialFamily])).2

end ToricContribution
end ParkingFunctions
end RealRooted
