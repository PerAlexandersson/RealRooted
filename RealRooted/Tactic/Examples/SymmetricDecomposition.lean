import RealRooted.Tactic.SymmetricDecomposition

/-!
# `fPolynomial` transport tactic examples

Abstract smoke tests for the Branden--Solus symmetric-decomposition frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {d : Nat} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d)
    (hp : p ≠ 0 ∧ p.Splits)
    (hpnn : HasNonnegCoeffs p) :
    (fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits := by
  rr_fPolynomial_realrooted using
    degree := hpdeg,
    realrooted := hp,
    nonneg := hpnn

example {d : Nat} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d)
    (hfp : (fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits)
    (hpnn : HasNonnegCoeffs p) :
    p ≠ 0 ∧ p.Splits := by
  rr_of_fPolynomial_realrooted using
    degree := hpdeg,
    transformed_realrooted := hfp,
    nonneg := hpnn

example {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hp : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, fPolynomial (d n) (P n) ≠ 0 ∧
      (fPolynomial (d n) (P n)).Splits := by
  rr_fPolynomial_sequence_realrooted using
    degree := hpdeg,
    realrooted := hp,
    nonneg := hpnn

example {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hfp : ∀ n : Nat, fPolynomial (d n) (P n) ≠ 0 ∧
      (fPolynomial (d n) (P n)).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_of_fPolynomial_sequence_realrooted using
    degree := hpdeg,
    transformed_realrooted := hfp,
    nonneg := hpnn

example {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (hprec : Prec u v) :
    Prec (fPolynomial d u) (fPolynomial d v) := by
  rr_fPolynomial_prec using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg,
    prec := hprec

example {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ n : Nat, (U n).natDegree ≤ d n)
    (hvd : ∀ n : Nat, (V n).natDegree ≤ d n)
    (hu_nonneg : ∀ n : Nat, HasNonnegCoeffs (U n))
    (hv_nonneg : ∀ n : Nat, HasNonnegCoeffs (V n))
    (hprec : ∀ n : Nat, Prec (U n) (V n)) :
    ∀ n : Nat, Prec (fPolynomial (d n) (U n)) (fPolynomial (d n) (V n)) := by
  rr_fPolynomial_sequence_prec using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg,
    prec := hprec

example {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (hprec : Prec (fPolynomial d u) (fPolynomial d v)) :
    Prec u v := by
  rr_of_fPolynomial_prec using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg,
    transformed_prec := hprec

example {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ n : Nat, (U n).natDegree ≤ d n)
    (hvd : ∀ n : Nat, (V n).natDegree ≤ d n)
    (hu_nonneg : ∀ n : Nat, HasNonnegCoeffs (U n))
    (hv_nonneg : ∀ n : Nat, HasNonnegCoeffs (V n))
    (hprec : ∀ n : Nat, Prec (fPolynomial (d n) (U n)) (fPolynomial (d n) (V n))) :
    ∀ n : Nat, Prec (U n) (V n) := by
  rr_of_fPolynomial_sequence_prec using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg,
    transformed_prec := hprec

example {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v) :
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v) := by
  rr_fPolynomial_prec_iff using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg

example {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ n : Nat, (U n).natDegree ≤ d n)
    (hvd : ∀ n : Nat, (V n).natDegree ≤ d n)
    (hu_nonneg : ∀ n : Nat, HasNonnegCoeffs (U n))
    (hv_nonneg : ∀ n : Nat, HasNonnegCoeffs (V n))
    (hprec : ∀ n : Nat, Prec (U n) (V n)) :
    ∀ n : Nat, PosComboRealRooted (fPolynomial (d n) (U n))
      (fPolynomial (d n) (V n)) := by
  rr_fPolynomial_sequence_pos_combo using
    prec := hprec,
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg

example {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (hprec : Prec u v) :
    PosComboRealRooted (fPolynomial d u) (fPolynomial d v) := by
  rr_fPolynomial_pos_combo using
    prec := hprec,
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg

end Tactic
end RealRooted
