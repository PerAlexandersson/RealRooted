import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.EndpointZero

/-!
# Quartic/cubic boundary assembly

Assembly of repeated-root and endpoint packages into the normalized quartic/cubic leaf.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The repeated-right quartic/cubic boundary follows from the repeated-left
and endpoint-zero packages, because the remaining branch has strict left roots
and a strictly negative right endpoint. -/
theorem xSubQuarticCubicRepeatedRightBoundaryCases_of_left_endpoint_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicRepeatedRightBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  by_cases hab_eq : a = b
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl hab_eq)
  by_cases hbc_eq : b = c
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  by_cases hcd_eq : c = d
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inr hcd_eq))
  by_cases hw_eq : w = 0
  · exact hend hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr hw_eq)
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  exact xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases
    hab_lt hbc_lt hcd_lt huv hvw hau hbv hcw huc hvd hd0 hw0_lt hμ h

/-- The combined quartic/cubic side-boundary package follows from the three
independent repeated-left, repeated-right, and endpoint-zero subpackages. -/
theorem xSubQuarticCubicSideBoundaryCases_of_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hright : xSubQuarticCubicRepeatedRightBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSideBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  rcases h with hab_eq | hbc_eq | hcd_eq | huv_eq | hvw_eq | hd_eq | hw_eq
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl hab_eq)
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inr hcd_eq))
  · exact hright hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl huv_eq)
  · exact hright hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr hvw_eq)
  · exact hend hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl hd_eq)
  · exact hend hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr hw_eq)

/-- The full normalized quartic/cubic terminal follows once the same-side
repeated-root and endpoint-zero boundary package is proved.  Shared-root cases
are handled by `xSubQuarticCubicSplits_of_common_root_cases`; the remaining
strict case is `xSubQuarticCubicSplits_of_strict_side_roots`. -/
theorem xSubQuarticCubicSplits_of_side_boundary_cases
    (hboundary : xSubQuarticCubicSideBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
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
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hab_eq])
  by_cases hbc_eq : b = c
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hbc_eq])
  by_cases hcd_eq : c = d
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hcd_eq])
  by_cases huv_eq : u = v
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [huv_eq])
  by_cases hvw_eq : v = w
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hvw_eq])
  by_cases hd_eq : d = 0
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hd_eq])
  by_cases hw_eq : w = 0
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
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

/-- The full normalized quartic/cubic terminal follows from the three focused
boundary subpackages. -/
theorem xSubQuarticCubicSplits_of_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hright : xSubQuarticCubicRepeatedRightBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_side_boundary_cases
    (xSubQuarticCubicSideBoundaryCases_of_packages hleft hright hend)

/-- The full normalized quartic/cubic terminal follows once the repeated-left
and endpoint-zero boundary packages are proved.  The repeated-right package is
derived from them using the strict-left repeated-right core. -/
theorem xSubQuarticCubicSplits_of_left_endpoint_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_boundary_packages hleft
    (xSubQuarticCubicRepeatedRightBoundaryCases_of_left_endpoint_packages
      hleft hend)
    hend

/-- The full normalized quartic/cubic terminal follows from the repeated-left
boundary package and the two disjoint single-endpoint zero packages. -/
theorem xSubQuarticCubicSplits_of_left_single_endpoint_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hleftZero :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement)
    (hrightZero :
      xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_left_endpoint_boundary_packages hleft
    (xSubQuarticCubicEndpointZeroBoundaryCases_of_single_endpoint_packages
      hleftZero hrightZero)

/-- The full normalized quartic/cubic terminal follows from repeated-left and
left-only endpoint packages, plus the quartic-minus-quadratic right endpoint
factor. -/
theorem xSubQuarticCubicSplits_of_left_endpoint_quarticSubQuadratic_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hleftZero :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement)
    (hquad : quarticSubQuadraticSplitsStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_left_endpoint_boundary_packages hleft
    (xSubQuarticCubicEndpointZeroBoundaryCases_of_left_endpoint_quarticSubQuadratic
      hleftZero hquad)

/-- The full normalized quartic/cubic terminal now follows from the two
remaining left-boundary packages. -/
theorem xSubQuarticCubicSplits_of_remaining_left_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hleftZero :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_left_endpoint_quarticSubQuadratic_packages hleft
    hleftZero quarticSubQuadraticSplits

/-- The normalized monic quartic/cubic x-subtraction leaf. -/
theorem xSubQuarticCubicSplits : xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_remaining_left_boundary_packages
    xSubQuarticCubicRepeatedLeftBoundaryCases
    xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCases


end LiuOppositeSigns
end RealRooted
