module

public import RealRooted.HermiteBiehler
public import RealRooted.HermiteBiehler.Converse.RootGeometry
public import RealRooted.HermiteBiehler.Forward

/-!
# Hermite--Biehler tactic frontends

Thin wrappers around the checked Hermite--Biehler forward, converse, and
odd/even Hurwitz bridges.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

theorem hermiteBiehlerOddEven_isHurwitzStable {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq,
    hermiteBiehlerStableToHurwitzOddEven hp hq hstable⟩

theorem hermiteBiehlerForwardPos_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstrictInterl : ∀ n : Nat, StrictInterl (G n) (F n)) :
    ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n)) :=
  fun n => RealRooted.hermiteBiehlerForwardPos (hF n) (hG n) (hstrictInterl n)

theorem hermiteBiehlerConverse_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n))) :
    ∀ n : Nat, StrictInterl (G n) (F n) ∨ StrictInterl (F n) (G n) :=
  fun n => RealRooted.hermiteBiehlerConverse (hF n) (hG n) (hstable n)

theorem hermiteBiehlerSplits_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n))) :
    ∀ n : Nat, (F n).Splits ∧ (G n).Splits :=
  fun n => RealRooted.splits_of_stable (hF n) (hG n) (hstable n)

theorem hermiteBiehlerStrictInterl_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n)))
    (hdegree : ∀ n : Nat, 1 ≤ (F n).natDegree) :
    ∀ n : Nat, StrictInterl (G n) (F n) :=
  fun n => RealRooted.strictInterl_of_stable_general (hF n) (hG n) (hstable n) (hdegree n)

theorem hermiteBiehlerOddEven_rightHalfPlaneStable_sequence {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat,
      IsRightHalfPlaneStable (complexify (oddEvenPolynomial (P n) (Q n))) :=
  fun n => RealRooted.hermiteBiehlerStableToHurwitzOddEven (hP n) (hQ n) (hstable n)

theorem hermiteBiehlerOddEven_isHurwitzStable_sequence {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat, IsHurwitzStable (oddEvenPolynomial (P n) (Q n)) :=
  fun n => hermiteBiehlerOddEven_isHurwitzStable (hP n) (hQ n) (hstable n)

/-- Closes `IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)` from
`real_pos_lc` and `imag_pos_lc` (positive leading coefficients of `f` and `g`) and
`strictInterl_imag_real : StrictInterl g f`. -/
syntax (name := rr_hermite_biehler_forward_pos_named)
  "rr_hermite_biehler_forward_pos" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "strictInterl_imag_real" ":=" term :
  tactic

/-- Closes `StrictInterl g f ∨ StrictInterl f g` from `real_pos_lc` and `imag_pos_lc` (positive
leading coefficients of `f` and `g`) and
`stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)`. -/
syntax (name := rr_hermite_biehler_converse_named)
  "rr_hermite_biehler_converse" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Closes `f.Splits ∧ g.Splits` from `real_pos_lc` and `imag_pos_lc` (positive leading
coefficients of `f` and `g`) and
`stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)`. -/
syntax (name := rr_hermite_biehler_splits_named)
  "rr_hermite_biehler_splits" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Closes `StrictInterl g f` from `real_pos_lc` and `imag_pos_lc` (positive leading
coefficients of `f` and `g`), `stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)`
and `real_degree_pos : 1 ≤ f.natDegree`. -/
syntax (name := rr_hermite_biehler_strict_interl_named)
  "rr_hermite_biehler_strict_interl" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term ","
    "real_degree_pos" ":=" term :
  tactic

/-- Closes `IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q))` from
`odd_nonneg : HasNonnegCoeffs p`, `even_nonneg : HasNonnegCoeffs q` and
`stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)`. -/
syntax (name := rr_hermite_biehler_odd_even_hurwitz_named)
  "rr_hermite_biehler_odd_even_hurwitz" " using "
    "odd_nonneg" ":=" term ","
    "even_nonneg" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Closes `IsHurwitzStable (oddEvenPolynomial p q)` from `odd_nonneg : HasNonnegCoeffs p`,
`even_nonneg : HasNonnegCoeffs q` and
`stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)`. -/
syntax (name := rr_hermite_biehler_odd_even_hurwitz_stable_named)
  "rr_hermite_biehler_odd_even_hurwitz_stable" " using "
    "odd_nonneg" ":=" term ","
    "even_nonneg" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Sequence form of `rr_hermite_biehler_forward_pos`: the same certificate for every index `n`. -/
syntax (name := rr_hermite_biehler_forward_pos_sequence_named)
  "rr_hermite_biehler_forward_pos_sequence" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "strictInterl_imag_real" ":=" term :
  tactic

/-- Sequence form of `rr_hermite_biehler_converse`: the same certificate for every index `n`. -/
syntax (name := rr_hermite_biehler_converse_sequence_named)
  "rr_hermite_biehler_converse_sequence" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Sequence form of `rr_hermite_biehler_splits`: the same certificate for every index `n`. -/
syntax (name := rr_hermite_biehler_splits_sequence_named)
  "rr_hermite_biehler_splits_sequence" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Sequence form of
`rr_hermite_biehler_strict_interl`: the same certificate for every index `n`. -/
syntax (name := rr_hermite_biehler_strict_interl_sequence_named)
  "rr_hermite_biehler_strict_interl_sequence" " using "
    "real_pos_lc" ":=" term ","
    "imag_pos_lc" ":=" term ","
    "stable" ":=" term ","
    "real_degree_pos" ":=" term :
  tactic

/-- Sequence form of
`rr_hermite_biehler_odd_even_hurwitz`: the same certificate for every index `n`. -/
syntax (name := rr_hermite_biehler_odd_even_hurwitz_sequence_named)
  "rr_hermite_biehler_odd_even_hurwitz_sequence" " using "
    "odd_nonneg" ":=" term ","
    "even_nonneg" ":=" term ","
    "stable" ":=" term :
  tactic

/-- Sequence form of `rr_hermite_biehler_odd_even_hurwitz_stable`: the same certificate for
every index `n`. -/
syntax (name := rr_hermite_biehler_odd_even_hurwitz_stable_sequence_named)
  "rr_hermite_biehler_odd_even_hurwitz_stable_sequence" " using "
    "odd_nonneg" ":=" term ","
    "even_nonneg" ":=" term ","
    "stable" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_hermite_biehler_forward_pos using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        strictInterl_imag_real := $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.hermiteBiehlerForwardPos $hf $hg $hstrictInterl)
  | `(tactic|
      rr_hermite_biehler_converse using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.hermiteBiehlerConverse $hf $hg $hstable)
  | `(tactic|
      rr_hermite_biehler_splits using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.splits_of_stable $hf $hg $hstable)
  | `(tactic|
      rr_hermite_biehler_strict_interl using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term,
        real_degree_pos := $hdegree:term) =>
      `(tactic|
        exact RealRooted.strictInterl_of_stable_general $hf $hg $hstable $hdegree)
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
  | `(tactic|
      rr_hermite_biehler_forward_pos_sequence using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        strictInterl_imag_real := $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerForwardPos_sequence
          $hf $hg $hstrictInterl)
  | `(tactic|
      rr_hermite_biehler_converse_sequence using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerConverse_sequence
          $hf $hg $hstable)
  | `(tactic|
      rr_hermite_biehler_splits_sequence using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerSplits_sequence
          $hf $hg $hstable)
  | `(tactic|
      rr_hermite_biehler_strict_interl_sequence using
        real_pos_lc := $hf:term,
        imag_pos_lc := $hg:term,
        stable := $hstable:term,
        real_degree_pos := $hdegree:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerStrictInterl_sequence
          $hf $hg $hstable $hdegree)
  | `(tactic|
      rr_hermite_biehler_odd_even_hurwitz_sequence using
        odd_nonneg := $hp:term,
        even_nonneg := $hq:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerOddEven_rightHalfPlaneStable_sequence
          $hp $hq $hstable)
  | `(tactic|
      rr_hermite_biehler_odd_even_hurwitz_stable_sequence using
        odd_nonneg := $hp:term,
        even_nonneg := $hq:term,
        stable := $hstable:term) =>
      `(tactic|
        exact RealRooted.Tactic.hermiteBiehlerOddEven_isHurwitzStable_sequence
          $hp $hq $hstable)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
