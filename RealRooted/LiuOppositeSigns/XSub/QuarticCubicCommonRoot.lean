import RealRooted.LiuOppositeSigns.XSub.CubicQuadratic
import RealRooted.LiuOppositeSigns.XSub.QuarticCubic

/-!
# Liu quartic/cubic x-subtraction common-root package

This module contains the common-root and strict-side dispatch cases for the
normalized quartic/cubic x-subtraction leaf.  Repeated and endpoint boundary
packages live downstream.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Common-root boundary for the normalized quartic/cubic terminal.  Factoring
out the shared linear term leaves the already proved cubic/quadratic leaf. -/
lemma xSubQuarticCubicSplits_of_common_root
    {r a b c u v μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hbv : b ≤ v) (huc : u ≤ c)
    (hc0 : c ≤ 0) (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial r a b c r u v μ).Splits := by
  have hsmall :
      (X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits :=
    xSubCubicQuadraticSplits hab hbc huv hau hbv huc hc0 hv0 hμ
  have hfactor :
      xSubQuarticCubicPolynomial r a b c r u v μ =
        (X - C r) *
          (X * ((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v))) := by
    unfold xSubQuarticCubicPolynomial
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hsmall

/-- Boundary case of the quartic/cubic terminal where the lower right root is
the lower left root. -/
lemma xSubQuarticCubicSplits_of_lower_common_root
    {a b c d v w μ : ℝ} (hbc : b ≤ c) (hcd : c ≤ d) (hvw : v ≤ w)
    (hbv : b ≤ v) (hcw : c ≤ w) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d a v w μ).Splits :=
  xSubQuarticCubicSplits_of_common_root
    (r := a) (a := b) (b := c) (c := d) (u := v) (v := w)
    hbc hcd hvw hbv hcw hvd hd0 hw0 hμ

/-- Boundary case of the quartic/cubic terminal where the lower right root is
the second left root. -/
lemma xSubQuarticCubicSplits_of_right_first_eq_second_left_root
    {a b c d v w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hvw : v ≤ w) (hbv : b ≤ v) (hcw : c ≤ w) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d b v w μ).Splits := by
  have hac : a ≤ c := hab.trans hbc
  have hav : a ≤ v := hab.trans hbv
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := b) (a := a) (b := c) (c := d) (u := v) (v := w)
    hac hcd hvw hav hcw hvd hd0 hw0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case of the quartic/cubic terminal where the middle right root is
the second left root. -/
lemma xSubQuarticCubicSplits_of_middle_common_root
    {a b c d u w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hub : u ≤ b) (hbw : b ≤ w) (hau : a ≤ u) (hcw : c ≤ w)
    (huc : u ≤ c) (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u b w μ).Splits := by
  have hac : a ≤ c := hab.trans hbc
  have huw : u ≤ w := hub.trans hbw
  have hud : u ≤ d := huc.trans hcd
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := b) (a := a) (b := c) (c := d) (u := u) (v := w)
    hac hcd huw hau hcw hud hd0 hw0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case of the quartic/cubic terminal where the lower right root is
the third left root. -/
lemma xSubQuarticCubicSplits_of_right_first_eq_third_left_root
    {a b c d v w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hcv : c ≤ v) (hvw : v ≤ w) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d c v w μ).Splits := by
  have hbd : b ≤ d := hbc.trans hcd
  have hav : a ≤ v := (hab.trans hbc).trans hcv
  have hbw : b ≤ w := hbc.trans (hcv.trans hvw)
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := c) (a := a) (b := b) (c := d) (u := v) (v := w)
    hab hbd hvw hav hbw hvd hd0 hw0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case of the quartic/cubic terminal where the middle right root is
the third left root. -/
lemma xSubQuarticCubicSplits_of_right_second_eq_third_left_root
    {a b c d u w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huc : u ≤ c) (hcw : c ≤ w) (hau : a ≤ u)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u c w μ).Splits := by
  have hbd : b ≤ d := hbc.trans hcd
  have huw : u ≤ w := huc.trans hcw
  have hbw : b ≤ w := hbc.trans hcw
  have hud : u ≤ d := huc.trans hcd
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := c) (a := a) (b := b) (c := d) (u := u) (v := w)
    hab hbd huw hau hbw hud hd0 hw0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case of the quartic/cubic terminal where the upper right root is
the third left root. -/
lemma xSubQuarticCubicSplits_of_upper_common_root
    {a b c d u v μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hau : a ≤ u) (hbv : b ≤ v) (huc : u ≤ c)
    (hvc : v ≤ c) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v c μ).Splits := by
  have hbd : b ≤ d := hbc.trans hcd
  have hud : u ≤ d := huc.trans hcd
  have hv0 : v ≤ 0 := hvc.trans (hcd.trans hd0)
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := c) (a := a) (b := b) (c := d) (u := u) (v := v)
    hab hbd huv hau hbv hud hd0 hv0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case of the quartic/cubic terminal where the middle right root is
the fourth left root. -/
lemma xSubQuarticCubicSplits_of_right_second_eq_fourth_left_root
    {a b c d u w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huc : u ≤ c) (hdw : d ≤ w) (hau : a ≤ u)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u d w μ).Splits := by
  have hbw : b ≤ w := (hbc.trans hcd).trans hdw
  have huw : u ≤ w := (huc.trans hcd).trans hdw
  have hc0 : c ≤ 0 := hcd.trans hd0
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := d) (a := a) (b := b) (c := c) (u := u) (v := w)
    hab hbc huw hau hbw huc hc0 hw0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case of the quartic/cubic terminal where the upper right root is
the fourth left root. -/
lemma xSubQuarticCubicSplits_of_top_common_root
    {a b c d u v μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hau : a ≤ u) (hbv : b ≤ v) (huc : u ≤ c)
    (hvd : v ≤ d) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v d μ).Splits := by
  have hc0 : c ≤ 0 := hcd.trans hd0
  have hv0 : v ≤ 0 := hvd.trans hd0
  have hsplits := xSubQuarticCubicSplits_of_common_root
    (r := d) (a := a) (b := b) (c := c) (u := u) (v := v)
    hab hbc huv hau hbv huc hc0 hv0 hμ
  simpa [xSubQuarticCubicPolynomial, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Dispatcher for the quartic/cubic terminal cases where a right root equals
one of the allowed neighboring left roots. -/
lemma xSubQuarticCubicSplits_of_common_root_cases
    {a b c d u v w μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hbv : b ≤ v)
    (hcw : c ≤ w) (huc : u ≤ c) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ)
    (hcommon :
      u = a ∨ u = b ∨ u = c ∨ v = b ∨ v = c ∨ v = d ∨ w = c ∨ w = d) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  rcases hcommon with h | h | h | h | h | h | h | h
  · subst u
    exact xSubQuarticCubicSplits_of_lower_common_root
      hbc hcd hvw hbv hcw hvd hd0 hw0 hμ
  · subst u
    exact xSubQuarticCubicSplits_of_right_first_eq_second_left_root
      hab hbc hcd hvw hbv hcw hvd hd0 hw0 hμ
  · subst u
    exact xSubQuarticCubicSplits_of_right_first_eq_third_left_root
      hab hbc hcd huv hvw hvd hd0 hw0 hμ
  · subst v
    exact xSubQuarticCubicSplits_of_middle_common_root
      hab hbc hcd huv hvw hau hcw huc hd0 hw0 hμ
  · subst v
    exact xSubQuarticCubicSplits_of_right_second_eq_third_left_root
      hab hbc hcd huc hcw hau hd0 hw0 hμ
  · subst v
    exact xSubQuarticCubicSplits_of_right_second_eq_fourth_left_root
      hab hbc hcd huc hvw hau hd0 hw0 hμ
  · subst w
    exact xSubQuarticCubicSplits_of_upper_common_root
      hab hbc hcd huv hau hbv huc hvw hd0 hμ
  · subst w
    exact xSubQuarticCubicSplits_of_top_common_root
      hab hbc hcd huv hau hbv huc hvd hd0 hμ

/-- Dispatcher for the quartic/cubic terminal when the left roots, right roots,
and endpoint signs are strict.  This packages the common-root cases
`u = b`, `v = c`, and `w = d` together with the fully strict dispatcher. -/
lemma xSubQuarticCubicSplits_of_strict_side_roots
    {a b c d u v w μ : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u < v) (hvw : v < w) (hau : a < u) (hbv : b < v)
    (hcw : c < w) (huc : u < c) (hvd : v < d)
    (hd0 : d < 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  by_cases hub : u = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) (le_of_lt huv)
      (le_of_lt hvw) (le_of_lt hau) (le_of_lt hbv) (le_of_lt hcw)
      (le_of_lt huc) (le_of_lt hvd) (le_of_lt hd0) (le_of_lt hw0) hμ
      (by simp [hub])
  · by_cases hvc : v = c
    · exact xSubQuarticCubicSplits_of_common_root_cases
        (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) (le_of_lt huv)
        (le_of_lt hvw) (le_of_lt hau) (le_of_lt hbv) (le_of_lt hcw)
        (le_of_lt huc) (le_of_lt hvd) (le_of_lt hd0) (le_of_lt hw0) hμ
        (by simp [hvc])
    · by_cases hwd : w = d
      · exact xSubQuarticCubicSplits_of_common_root_cases
          (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) (le_of_lt huv)
          (le_of_lt hvw) (le_of_lt hau) (le_of_lt hbv) (le_of_lt hcw)
          (le_of_lt huc) (le_of_lt hvd) (le_of_lt hd0) (le_of_lt hw0) hμ
          (by simp [hwd])
      · exact xSubQuarticCubicSplits_of_strict_roots
          hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ hub hvc hwd


end LiuOppositeSigns
end RealRooted
