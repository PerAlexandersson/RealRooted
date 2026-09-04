import RealRooted.ParkingFunctions.ToricContribution.ExceptionalOffset.NodeInterlacing

/-!
# Common interlacer for the A390883 toric-contribution family

This file packages the all-offset Jacobi comparison as both a fixed-row
interlacing-sequence theorem and a finite-family common-left-interlacer
theorem. It also closes splitness for arbitrary strictly positive weighted
sums of the parity-normalized `R_d` family.

The pairwise orientation is the normalized reciprocal form of Conjecture 4.2
in Qiqi Xiao, *The real-rootedness of the toric g-contribution polynomials*,
arXiv:2609.01086v1. The common-interlacer theorem is distinct and is what
controls arbitrary nonnegative row sums.
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

/-- The normalized reverse-offset polynomials inherit the fixed-row proper
position orientation. -/
theorem normalizedRPolynomial_prec_of_lt
    (m ε d e : ℕ) (hm : 0 < m) (hde : d < e) (he : e ≤ m) :
    Prec (normalizedRPolynomial m ε e) (normalizedRPolynomial m ε d) := by
  exact prec_C_mul_right
    (prec_C_mul_left
      (rPolynomial_prec_rPolynomial_of_lt m ε d e hm hde he)
      (pow_ne_zero m (by norm_num)))
    (pow_ne_zero m (by norm_num))

/-- The normalized `R`-polynomials in the order corresponding to
`g_(n,0), ..., g_(n,floor (n/2))`. -/
def normalizedRPolynomialRow (m ε : ℕ) : List ℝ[X] :=
  (List.range (m + 1)).map fun j => normalizedRPolynomial m ε (m - j)

@[simp]
theorem length_normalizedRPolynomialRow (m ε : ℕ) :
    (normalizedRPolynomialRow m ε).length = m + 1 := by
  simp [normalizedRPolynomialRow]

/-- The fixed-row toric-contribution family is pairwise interlacing in its
natural contribution-index order. This is the normalized reciprocal form of
Xiao's Conjecture 4.2. -/
theorem normalizedRPolynomialRow_isInterlacingSeq (m ε : ℕ) :
    IsInterlacingSeq (normalizedRPolynomialRow m ε) := by
  apply isInterlacingSeq_reverseOffsetRow
  intro d e hde he
  exact normalizedRPolynomial_prec_of_lt m ε d e (by lia) hde he

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
