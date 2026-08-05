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

example {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  rr_hermite_biehler_splits using
    real_pos_lc := hf,
    imag_pos_lc := hg,
    stable := hstable

example {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hdegree : 1 ≤ f.natDegree) :
    Prec g f := by
  rr_hermite_biehler_prec using
    real_pos_lc := hf,
    imag_pos_lc := hg,
    stable := hstable,
    real_degree_pos := hdegree

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

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hprec : ∀ n : Nat, Prec (G n) (F n)) :
    ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n)) := by
  rr_hermite_biehler_forward_pos_sequence using
    real_pos_lc := hF,
    imag_pos_lc := hG,
    prec_imag_real := hprec

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n))) :
    ∀ n : Nat, Prec (G n) (F n) ∨ Prec (F n) (G n) := by
  rr_hermite_biehler_converse_sequence using
    real_pos_lc := hF,
    imag_pos_lc := hG,
    stable := hstable

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n))) :
    ∀ n : Nat, (F n).Splits ∧ (G n).Splits := by
  rr_hermite_biehler_splits_sequence using
    real_pos_lc := hF,
    imag_pos_lc := hG,
    stable := hstable

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n)))
    (hdegree : ∀ n : Nat, 1 ≤ (F n).natDegree) :
    ∀ n : Nat, Prec (G n) (F n) := by
  rr_hermite_biehler_prec_sequence using
    real_pos_lc := hF,
    imag_pos_lc := hG,
    stable := hstable,
    real_degree_pos := hdegree

example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat,
      IsRightHalfPlaneStable (complexify (oddEvenPolynomial (P n) (Q n))) := by
  rr_hermite_biehler_odd_even_hurwitz_sequence using
    odd_nonneg := hP,
    even_nonneg := hQ,
    stable := hstable

example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat, IsHurwitzStable (oddEvenPolynomial (P n) (Q n)) := by
  rr_hermite_biehler_odd_even_hurwitz_stable_sequence using
    odd_nonneg := hP,
    even_nonneg := hQ,
    stable := hstable

end Tactic
end RealRooted
