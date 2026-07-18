import RealRooted.Tactic.HermiteBiehler

open Polynomial

namespace RealRooted
namespace Tactic

example :
    hermiteBiehlerForwardPosStatement := by
  rr_hermite_biehler_forward_pos_statement

example :
    hermiteBiehlerConverseStatement := by
  rr_hermite_biehler_converse_statement

example :
    HermiteBiehlerStableToHurwitzOddEvenStatement := by
  rr_hermite_biehler_odd_even_hurwitz_statement

example {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hprec : Prec g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  rr_hermite_biehler_forward_pos using
    real_pos_lc := hf,
    imag_pos_lc := hg,
    prec_imag_real := hprec

example {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g := by
  rr_hermite_biehler_converse using
    real_pos_lc := hf,
    imag_pos_lc := hg,
    stable := hstable

example {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) := by
  rr_hermite_biehler_odd_even_hurwitz using
    odd_nonneg := hp,
    even_nonneg := hq,
    stable := hstable

example {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) := by
  rr_hermite_biehler_odd_even_hurwitz_stable using
    odd_nonneg := hp,
    even_nonneg := hq,
    stable := hstable

end Tactic
end RealRooted
