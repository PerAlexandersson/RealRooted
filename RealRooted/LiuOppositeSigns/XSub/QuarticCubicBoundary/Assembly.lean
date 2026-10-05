import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.EndpointZero

/-!
# Quartic/cubic boundary assembly

Assembly of the repeated-root and endpoint-zero boundary cases into the
normalized quartic/cubic x-subtraction splitting theorem.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The repeated-right quartic/cubic boundary follows from the repeated-left
and endpoint-zero packages, because the remaining branch has strict left roots
and a strictly negative right endpoint. -/
theorem xSubQuarticCubicRepeatedRightBoundaryCases {a b c d u v w μ : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hbv : b ≤ v)
    (hcw : c ≤ w) (huc : u ≤ c) (hvd : v ≤ d) (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ)
    (h : u = v ∨ v = w) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  by_cases hab_eq : a = b
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inl hab_eq)
  by_cases hbc_eq : b = c
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  by_cases hcd_eq : c = d
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr (Or.inr hcd_eq))
  by_cases hw_eq : w = 0
  · exact xSubQuarticCubicEndpointZeroBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr hw_eq)
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  exact xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases
    hab_lt hbc_lt hcd_lt huv hvw hau hbv hcw huc hvd hd0 hw0_lt hμ h

/-- The combined quartic/cubic side-boundary package follows from the three
independent repeated-left, repeated-right, and endpoint-zero subpackages. -/
theorem xSubQuarticCubicSideBoundaryCases {a b c d u v w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hbv : b ≤ v) (hcw : c ≤ w)
    (huc : u ≤ c) (hvd : v ≤ d) (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ)
    (h : a = b ∨ b = c ∨ c = d ∨ u = v ∨ v = w ∨ d = 0 ∨ w = 0) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  rcases h with hab_eq | hbc_eq | hcd_eq | huv_eq | hvw_eq | hd_eq | hw_eq
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inl hab_eq)
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr (Or.inr hcd_eq))
  · exact xSubQuarticCubicRepeatedRightBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inl huv_eq)
  · exact xSubQuarticCubicRepeatedRightBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr hvw_eq)
  · exact xSubQuarticCubicEndpointZeroBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inl hd_eq)
  · exact xSubQuarticCubicEndpointZeroBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0
      hw0 hμ
      (Or.inr hw_eq)

/-- The normalized monic quartic/cubic x-subtraction pencil splits.  Shared-root
cases are handled by `xSubQuarticCubicSplits_of_common_root_cases`, same-side
repeated roots and zero endpoints by `xSubQuarticCubicSideBoundaryCases`, and
the remaining strict case by `xSubQuarticCubicSplits_of_strict_side_roots`. -/
theorem xSubQuarticCubicSplits {a b c d u v w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hbv : b ≤ v) (hcw : c ≤ w) (huc : u ≤ c)
    (hvd : v ≤ d) (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  by_cases hua : u = a
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hua])
  by_cases hub : u = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hub])
  by_cases huc_eq : u = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [huc_eq])
  by_cases hvb : v = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hvb])
  by_cases hvc : v = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hvc])
  by_cases hvd_eq : v = d
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hvd_eq])
  by_cases hwc : w = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hwc])
  by_cases hwd : w = d
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hwd])
  by_cases hab_eq : a = b
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hab_eq])
  by_cases hbc_eq : b = c
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hbc_eq])
  by_cases hcd_eq : c = d
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hcd_eq])
  by_cases huv_eq : u = v
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [huv_eq])
  by_cases hvw_eq : v = w
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hvw_eq])
  by_cases hd_eq : d = 0
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hd_eq])
  by_cases hw_eq : w = 0
  · exact xSubQuarticCubicSideBoundaryCases hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hw_eq])
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
  have hvw_lt : v < w := lt_of_le_of_ne hvw hvw_eq
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua h.symm)
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb h.symm)
  have hcw_lt : c < w := lt_of_le_of_ne hcw (by intro h; exact hwc h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hd0_lt : d < 0 := lt_of_le_of_ne hd0 hd_eq
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  exact xSubQuarticCubicSplits_of_strict_side_roots
    hab_lt hbc_lt hcd_lt huv_lt hvw_lt hau_lt hbv_lt hcw_lt huc_lt hvd_lt
    hd0_lt hw0_lt hμ

end LiuOppositeSigns
end RealRooted
