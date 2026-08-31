import RealRooted.VeroneseSectionPair

/-!
# Hermite--Biehler certificates from normalized Veronese residues

This packages the unconditional parity route suggested by Fisk's
Hermite--Biehler discussion and Brändén's Veronese interlacing machinery.
Two nonzero normalized residue sections of one nonnegative real-rooted
polynomial are in proper position.  They therefore form an upper-half-plane
stable Hermite--Biehler polynomial, and their odd/even recombination is
Hurwitz stable.

The normalization hypotheses `j < k < r` are essential: this theorem does
not cover a shifted coefficient tail represented by an index at least `r`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Two ordered, nonzero normalized Veronese residues form a stable
Hermite--Biehler pair. -/
theorem isUpperHalfPlaneStable_hermiteBiehler_veroneseSections
    {r j k : ℕ} (hr : 0 < r) (hjk : j < k) (hk : k < r)
    {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hp0 : p ≠ 0)
    (hps : p.Splits)
    (hj0 : veroneseSectionPolynomial r j p ≠ 0)
    (hk0 : veroneseSectionPolynomial r k p ≠ 0) :
    IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial
        (veroneseSectionPolynomial r j p)
        (veroneseSectionPolynomial r k p)) := by
  have hprec := prec_veroneseSectionPolynomial_of_residue_lt
    hr hjk hk hpnn hp0 hps hj0 hk0
  have hjnn : HasNonnegCoeffs (veroneseSectionPolynomial r j p) :=
    hasNonnegCoeffs_veroneseSectionPolynomial hr hpnn
  have hknn : HasNonnegCoeffs (veroneseSectionPolynomial r k p) :=
    hasNonnegCoeffs_veroneseSectionPolynomial hr hpnn
  exact hermiteBiehlerForwardPos
    (hjnn.pos_leadingCoeff hj0) (hknn.pos_leadingCoeff hk0) hprec

/-- The odd/even recombination of two ordered normalized Veronese residues is
Hurwitz stable.  The higher residue supplies the odd component and the lower
residue supplies the even component. -/
theorem isHurwitzStable_oddEvenPolynomial_veroneseSections
    {r j k : ℕ} (hr : 0 < r) (hjk : j < k) (hk : k < r)
    {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hp0 : p ≠ 0)
    (hps : p.Splits)
    (hj0 : veroneseSectionPolynomial r j p ≠ 0)
    (hk0 : veroneseSectionPolynomial r k p ≠ 0) :
    IsHurwitzStable
      (oddEvenPolynomial
        (veroneseSectionPolynomial r k p)
        (veroneseSectionPolynomial r j p)) := by
  refine ⟨hasNonnegCoeffs_oddEvenPolynomial
      (hasNonnegCoeffs_veroneseSectionPolynomial hr hpnn)
      (hasNonnegCoeffs_veroneseSectionPolynomial hr hpnn), ?_⟩
  exact hermiteBiehlerStableToHurwitzOddEven
    (hasNonnegCoeffs_veroneseSectionPolynomial hr hpnn)
    (hasNonnegCoeffs_veroneseSectionPolynomial hr hpnn)
    (isUpperHalfPlaneStable_hermiteBiehler_veroneseSections
      hr hjk hk hpnn hp0 hps hj0 hk0)

end RealRooted
