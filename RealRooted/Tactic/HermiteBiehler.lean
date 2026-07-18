import RealRooted.HermiteBiehler

/-!
# Hermite--Biehler tactic frontends

Thin wrappers around the checked Hermite--Biehler forward, converse, and
odd/even Hurwitz bridges.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem hermiteBiehlerOddEven_isHurwitzStable {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq,
    hermiteBiehlerStableToHurwitzOddEven hp hq hstable⟩

syntax (name := rr_hermite_biehler_forward_pos_statement_named)
  "rr_hermite_biehler_forward_pos_statement" : tactic

syntax (name := rr_hermite_biehler_converse_statement_named)
  "rr_hermite_biehler_converse_statement" : tactic

syntax (name := rr_hermite_biehler_odd_even_hurwitz_statement_named)
  "rr_hermite_biehler_odd_even_hurwitz_statement" : tactic

syntax (name := rr_hermite_biehler_forward_pos_named)
  "rr_hermite_biehler_forward_pos" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "prec_imag_real" ":=" term :
  tactic

syntax (name := rr_hermite_biehler_converse_named)
  "rr_hermite_biehler_converse" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term :
  tactic

syntax (name := rr_hermite_biehler_odd_even_hurwitz_named)
  "rr_hermite_biehler_odd_even_hurwitz" " using "
    "odd_nonneg" ":=" term ","
    "even_nonneg" ":=" term ","
    "stable" ":=" term :
  tactic

syntax (name := rr_hermite_biehler_odd_even_hurwitz_stable_named)
  "rr_hermite_biehler_odd_even_hurwitz_stable" " using "
    "odd_nonneg" ":=" term ","
    "even_nonneg" ":=" term ","
    "stable" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_hermite_biehler_forward_pos_statement) =>
      `(tactic|
        exact fun {f g} hf hg hprec =>
          RealRooted.hermiteBiehlerForwardPos (f := f) (g := g) hf hg hprec)
  | `(tactic| rr_hermite_biehler_converse_statement) =>
      `(tactic|
        exact fun {f g} hf hg hstable =>
          RealRooted.hermiteBiehlerConverse (f := f) (g := g) hf hg hstable)
  | `(tactic| rr_hermite_biehler_odd_even_hurwitz_statement) =>
      `(tactic|
        exact fun {p q} hp hq hstable =>
          RealRooted.hermiteBiehlerStableToHurwitzOddEven
            (p := p) (q := q) hp hq hstable)
  | `(tactic|
      rr_hermite_biehler_forward_pos using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        prec_imag_real := $hprec:term) =>
      `(tactic|
        exact RealRooted.hermiteBiehlerForwardPos $hf $hg $hprec)
  | `(tactic|
      rr_hermite_biehler_converse using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.hermiteBiehlerConverse $hf $hg $hstable)
  | `(tactic|
      rr_hermite_biehler_odd_even_hurwitz using
        odd_nonneg := $hp:term,
        even_nonneg := $hq:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.hermiteBiehlerStableToHurwitzOddEven $hp $hq $hstable)
  | `(tactic|
      rr_hermite_biehler_odd_even_hurwitz_stable using
        odd_nonneg := $hp:term,
        even_nonneg := $hq:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerOddEven_isHurwitzStable
          $hp $hq $hstable)

end Tactic
end RealRooted
