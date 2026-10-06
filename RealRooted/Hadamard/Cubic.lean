import RealRooted.Hadamard.Newton

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Cubic Schur--Szego reductions

Degree-three PF-factor reductions of the Schur--Szegő composition to cubic
discriminant inequalities.
-/

/-- Cubic-discriminant splitting route for the fixed-degree Schur--Szegő
composition with a degree-`≤ 3` factor.

Once the fixed-degree Schur--Szegő composition's cubic coefficient discriminant
`cubicDiscr (schurSzegoComp n f p)` is known to be nonnegative, the composition
is either zero or splits over `ℝ`.  The composition inherits the degree bound of
the degree-`≤ 3` factor `f` via `natDegree_schurSzegoComp_le_left`, so the
result is the degree-`≤ 3` cubic discriminant criterion applied to it. -/
theorem finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  Or.inr (splits_of_natDegree_le_three_cubicDiscr_nonneg
    (le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg) hdisc)

/-- Schur--Szegő composition with a degree-`≤ 3` factor reduced to the
denominator-cleared cubic-discriminant numerator at levels `n ≥ 3`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg hfdeg
    ((cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).2 hnum)

end RealRooted
