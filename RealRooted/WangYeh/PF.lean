import RealRooted.EulerOperator.Pencil
import RealRooted.MultiplierSequence.Bidiagonal
import RealRooted.WangYeh.Affine

/-!
# The Wang--Yeh coefficient-bidiagonal PF criterion

This module derives Wang and Yeh's polynomial Pólya-frequency corollary from
the affine real-rootedness criterion. The affine determinant condition is
paired with nonnegativity of the output coefficients; no global sign condition
is imposed on the two coefficient-weight sequences.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- **Wang--Yeh coefficient-bidiagonal PF criterion.** An affine
coefficient-bidiagonal transform of a PF polynomial is again PF when the
affine determinant has the correct sign and the output coefficients are
nonnegative. -/
theorem IsPFPolynomial.wangYeh_bidiagonal
    {p : ℝ[X]} {a b c d : ℝ} (hp : IsPFPolynomial p)
    (hdet : b * c ≤ a * d)
    (hout : HasNonnegCoeffs
      (bidiagonalOperator (fun k => b + d * (k : ℝ))
        (fun k => a + c * (k : ℝ)) p)) :
    IsPFPolynomial
      (bidiagonalOperator (fun k => b + d * (k : ℝ))
        (fun k => a + c * (k : ℝ)) p) := by
  by_cases hdeg : p.natDegree = 0
  · apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hout
    right
    apply Polynomial.Splits.of_natDegree_le_one
    have hbound := natDegree_bidiagonalOperator_le
      (fun k => b + d * (k : ℝ)) (fun k => a + c * (k : ℝ)) p
    simpa [hdeg] using hbound
  · have hp_ne : p ≠ 0 := by
      intro hzero
      simp [hzero] at hdeg
    have hprec : Prec p (theta p) :=
      prec_self_theta_of_natDegree_ne_zero hp hdeg
    have hp_pos : HasPosLeadingCoeff p :=
      hp.hasNonnegCoeffs.pos_leadingCoeff hp_ne
    have htheta_pf : IsPFPolynomial (theta p) := theta_preserves_pf hp
    have htheta_pos : HasPosLeadingCoeff (theta p) :=
      htheta_pf.hasNonnegCoeffs.pos_leadingCoeff hprec.2.1.1
    have hdet' : c * b ≤ d * a := by
      simpa [mul_comm] using hdet
    have hsplit := wangYehAffine_eq_zero_or_splits
      (f := theta p) (g := p) (a := d) (b := c) (c := b) (d := a)
      hprec htheta_pos hp_pos hdet'
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hout
    rw [bidiagonalOperator_affine_weights]
    simpa [theta, add_comm] using hsplit

end RealRooted
