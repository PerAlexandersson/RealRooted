import RealRooted.HermiteBiehler.Converse.RootGeometry
import RealRooted.ObreschkoffConverse.Forward

/-!
# The Wang--Yeh affine real-rootedness criterion

This module proves Wang and Yeh's affine combination theorem. If `g` is in
proper position to the left of `f`, both leading coefficients are positive,
and `b * c ≤ a * d`, then

`(bX + a) f + (dX + c) g`

is real-rooted, with the zero polynomial allowed at degenerate parameters.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The complex affine factor in the Wang--Yeh factorization is stable when
its real coefficient determinant has the correct sign. -/
private theorem wangYehAffineFactor_stable
    (a b c d : ℝ) (hdet : b * c ≤ a * d) (hbd : b ≠ 0 ∨ d ≠ 0) :
    IsUpperHalfPlaneStable
      (C ((b : ℂ) - Complex.I * d) * X + C ((a : ℂ) - Complex.I * c)) := by
  intro z hz hzero
  have hre : b * z.re + d * z.im + a = 0 := by
    have hre' := congrArg Complex.re hzero
    norm_num [Complex.mul_re, Complex.mul_im] at hre' ⊢
    linarith
  have him : b * z.im - d * z.re - c = 0 := by
    have him' := congrArg Complex.im hzero
    norm_num [Complex.mul_re, Complex.mul_im] at him' ⊢
    linarith
  have hcombined : (b ^ 2 + d ^ 2) * z.im + a * d - b * c = 0 := by
    linear_combination b * him + d * hre
  rcases hbd with hb | hd
  · have hb_sq : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg d]
  · have hd_sq : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    nlinarith [sq_nonneg b]

/-- **Wang--Yeh affine criterion.** Let `g` precede `f`, with both leading
coefficients positive. If `b * c ≤ a * d`, then
`(bX + a) f + (dX + c) g` is real-rooted, allowing the zero polynomial.

The four affine coefficients have no sign assumptions. -/
theorem wangYehAffine_eq_zero_or_splits
    {f g : ℝ[X]} {a b c d : ℝ}
    (hgf : Prec g f)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdet : b * c ≤ a * d) :
    (C b * X + C a) * f + (C d * X + C c) * g = 0 ∨
      ((C b * X + C a) * f + (C d * X + C c) * g).Splits := by
  let A : ℝ[X] := C b * X + C a
  let D : ℝ[X] := C d * X + C c
  let H : ℝ[X] := A * f + D * g
  let K : ℝ[X] := A * g - D * f
  by_cases hbd : b = 0 ∧ d = 0
  · have hall := allComboRealRooted_of_prec hgf
    right
    simpa [A, D, H, hbd.1, hbd.2, add_comm] using hall c a
  have hfactor :
      hermiteBiehlerPolynomial H K =
        (C ((b : ℂ) - Complex.I * d) * X +
            C ((a : ℂ) - Complex.I * c)) *
          hermiteBiehlerPolynomial f g := by
    simp [H, K, A, D, hermiteBiehlerPolynomial, complexify]
    ring_nf
    rw [← C_pow, Complex.I_sq]
    simp
  have hbd' : b ≠ 0 ∨ d ≠ 0 := by
    by_cases hb : b = 0
    · right
      intro hd
      exact hbd ⟨hb, hd⟩
    · exact Or.inl hb
  have hlinear :
      IsUpperHalfPlaneStable
        (C ((b : ℂ) - Complex.I * d) * X +
          C ((a : ℂ) - Complex.I * c)) :=
    wangYehAffineFactor_stable a b c d hdet hbd'
  have hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial H K) := by
    rw [hfactor]
    exact hlinear.mul (hermiteBiehlerForwardPos hf_pos hg_pos hgf)
  simpa [H] using hstable.left_eq_zero_or_splits

end RealRooted
