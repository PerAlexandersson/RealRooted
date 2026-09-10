import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJOutput.Stability
import RealRooted.PFPolynomial

/-!
# PF certificates for the BFJ output

This file combines the coefficient-sign and stability interfaces for the
dehomogenized BFJ coefficient into a polynomial PF certificate.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Stable homogeneous inputs with nonnegative coefficients have PF BFJ
output. -/
theorem MvRealStable.bfjOutput_isPF
    {P Q : MvPolynomial (Fin 2) ℝ} {b : ℕ}
    (hPstable : MvRealStable P) (hQstable : MvRealStable Q)
    (hQhom : Q.IsHomogeneous b)
    (hPnn : MvPolynomial.HasNonnegCoeffs P)
    (hQnn : MvPolynomial.HasNonnegCoeffs Q) :
    IsPFPolynomial (MvPolynomial.bfjOutput P Q b) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hPnn.bfjOutput hQnn b)
  change MvUpperHalfPlaneStable (MvPolynomial.map Complex.ofRealHom P) at hPstable
  change MvUpperHalfPlaneStable (MvPolynomial.map Complex.ofRealHom Q) at hQstable
  have hout := hPstable.bfjOutput_zero_or hQstable
    (hQhom.map Complex.ofRealHom)
  rw [← MvPolynomial.map_bfjOutput] at hout
  rcases hout with hzero | hstable
  · exact Or.inl ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hzero)
  · exact Or.inr hstable.splits_complexify

end

end RealRooted
