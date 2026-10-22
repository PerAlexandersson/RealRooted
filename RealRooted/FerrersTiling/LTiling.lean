import RealRooted.FerrersTiling.Rigid

/-!
# Algebraic L-tile polynomials

This file defines the unrefined polynomial family from
Ahlberg--Alexandersson, *Polynomials from tilings of rectangles*, Section 3,
by its closed form.  Its later appearance as the rigid family with `ell = 1`
gives real-rootedness without using the layer-2 tiling model.
-/

open Polynomial

namespace RealRooted
namespace FerrersTiling

noncomputable section

/-- The algebraic L-tile polynomial `P_(d,n)`. -/
def lTilingPolynomial (d n : ℕ) : ℝ[X] :=
  rigidPolynomial d 1 n

/-- The anchor-word polynomial `Q_(d,n)`, algebraically defined by the same
closed form in layer 1. -/
def anchorPolynomial (d n : ℕ) : ℝ[X] :=
  rigidPolynomial d 1 n

/-- The paper's polynomials `P_(d,n)` and `Q_(d,n)` agree. -/
theorem lTilingPolynomial_eq_anchorPolynomial (d n : ℕ) :
    lTilingPolynomial d n = anchorPolynomial d n := rfl

/-- Closed coefficients of the L-tile polynomial. -/
@[simp]
theorem coeff_lTilingPolynomial (d n j : ℕ) :
    (lTilingPolynomial d n).coeff j =
      (Nat.choose (d * (n - j)) j : ℝ) := by
  simp [lTilingPolynomial]

/-- L-tile polynomials are Pólya-frequency. -/
theorem lTilingPolynomial_isPFPolynomial (d n : ℕ) :
    IsPFPolynomial (lTilingPolynomial d n) :=
  rigidPolynomial_isPFPolynomial d 1 n

/-- L-tile polynomials are real-rooted. -/
theorem lTilingPolynomial_splits (d n : ℕ) :
    (lTilingPolynomial d n).Splits :=
  rigidPolynomial_splits d 1 n

/-- Every zero of an L-tile polynomial is nonpositive. -/
theorem lTilingPolynomial_roots_nonpos (d n : ℕ) {r : ℝ}
    (hr : r ∈ (lTilingPolynomial d n).roots) : r ≤ 0 :=
  (lTilingPolynomial_isPFPolynomial d n).roots_nonpos r hr

/-- Consecutive L-tile polynomials interlace. -/
theorem lTilingPolynomial_interl_succ (d n : ℕ) :
    Interl (lTilingPolynomial d n) (lTilingPolynomial d (n + 1)) := by
  by_cases hd : d = 0
  · subst d
    have hzero (m : ℕ) : lTilingPolynomial 0 m = 1 := by
      ext j
      rw [coeff_lTilingPolynomial]
      cases j with
      | zero => simp
      | succ j => rw [coeff_one]; simp
    rw [hzero, hzero]
    exact Interl.refl fun _ => Polynomial.Splits.one
  · have h := strictInterl_pathPowerCliquePolynomial_add
      (d + 1) (d * n) d (by lia) (Nat.pos_of_ne_zero hd) (by lia)
    simpa [lTilingPolynomial, rigidPolynomial, Nat.mul_succ] using h.toInterl

end

end FerrersTiling
end RealRooted
