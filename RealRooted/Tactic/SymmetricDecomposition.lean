import RealRooted.SymmetricDecomposition

/-!
# Symmetric-decomposition tactic frontends

Thin wrappers for the Branden--Solus `fPolynomial` transport API in
`RealRooted.SymmetricDecomposition`.
-/

open Polynomial

namespace RealRooted

/-- Certificate-shaped frontend for real-rootedness preservation under `fPolynomial`. -/
theorem isRealRooted_fPolynomial_of_isRealRooted_cert
    {d : Nat} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d)
    (hp : p ≠ 0 ∧ p.Splits)
    (hpnn : HasNonnegCoeffs p) :
    (fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits :=
  isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hpdeg hp.1 hp.2 hpnn

/-- Certificate-shaped frontend for pulling real-rootedness back through `fPolynomial`. -/
theorem isRealRooted_of_fPolynomial_isRealRooted_cert
    {d : Nat} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d)
    (hfp : (fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits)
    (hpnn : HasNonnegCoeffs p) :
    p ≠ 0 ∧ p.Splits :=
  isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hpdeg hfp.1 hfp.2 hpnn

/-- Forward `Prec` transport through `fPolynomial` in any ambient degree. -/
theorem prec_fPolynomial_of_prec
    {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (h : Prec u v) :
    Prec (fPolynomial d u) (fPolynomial d v) :=
  (precFPolynomialTransport hud hvd hu_nonneg hv_nonneg).mpr h

/-- Backward `Prec` transport through `fPolynomial` in any ambient degree. -/
theorem prec_of_prec_fPolynomial
    {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (h : Prec (fPolynomial d u) (fPolynomial d v)) :
    Prec u v :=
  (precFPolynomialTransport hud hvd hu_nonneg hv_nonneg).mp h

theorem isRealRooted_fPolynomial_sequence_of_isRealRooted_cert
    {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, fPolynomial (d i) (P i) ≠ 0 ∧
      (fPolynomial (d i) (P i)).Splits := fun i =>
  isRealRooted_fPolynomial_of_isRealRooted_cert (hdeg i) (hrr i) (hnn i)

theorem isRealRooted_of_fPolynomial_sequence_isRealRooted_cert
    {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hfPrr : ∀ i : Nat, fPolynomial (d i) (P i) ≠ 0 ∧
      (fPolynomial (d i) (P i)).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits := fun i =>
  isRealRooted_of_fPolynomial_isRealRooted_cert (hdeg i) (hfPrr i) (hnn i)

theorem prec_fPolynomial_sequence_of_prec
    {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ i : Nat, (U i).natDegree ≤ d i)
    (hvd : ∀ i : Nat, (V i).natDegree ≤ d i)
    (hu_nonneg : ∀ i : Nat, HasNonnegCoeffs (U i))
    (hv_nonneg : ∀ i : Nat, HasNonnegCoeffs (V i))
    (hprec : ∀ i : Nat, Prec (U i) (V i)) :
    ∀ i : Nat, Prec (fPolynomial (d i) (U i)) (fPolynomial (d i) (V i)) :=
  fun i => prec_fPolynomial_of_prec (hud i) (hvd i)
    (hu_nonneg i) (hv_nonneg i) (hprec i)

theorem prec_of_prec_fPolynomial_sequence
    {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ i : Nat, (U i).natDegree ≤ d i)
    (hvd : ∀ i : Nat, (V i).natDegree ≤ d i)
    (hu_nonneg : ∀ i : Nat, HasNonnegCoeffs (U i))
    (hv_nonneg : ∀ i : Nat, HasNonnegCoeffs (V i))
    (hprec : ∀ i : Nat, Prec (fPolynomial (d i) (U i)) (fPolynomial (d i) (V i))) :
    ∀ i : Nat, Prec (U i) (V i) := fun i =>
  prec_of_prec_fPolynomial (hud i) (hvd i)
    (hu_nonneg i) (hv_nonneg i) (hprec i)

theorem posComboRealRooted_fPolynomial_sequence_of_prec
    {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hprec : ∀ i : Nat, Prec (U i) (V i))
    (hud : ∀ i : Nat, (U i).natDegree ≤ d i)
    (hvd : ∀ i : Nat, (V i).natDegree ≤ d i)
    (hu_nonneg : ∀ i : Nat, HasNonnegCoeffs (U i))
    (hv_nonneg : ∀ i : Nat, HasNonnegCoeffs (V i)) :
    ∀ i : Nat, PosComboRealRooted (fPolynomial (d i) (U i))
      (fPolynomial (d i) (V i)) := fun i =>
  posComboRealRooted_fPolynomial_of_prec (hprec i) (hud i) (hvd i)
    (hu_nonneg i) (hv_nonneg i)

namespace Tactic

syntax (name := rr_fPolynomial_realrooted_named)
  "rr_fPolynomial_realrooted" " using "
    "degree" ":=" term ","
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_of_fPolynomial_realrooted_named)
  "rr_of_fPolynomial_realrooted" " using "
    "degree" ":=" term ","
    "transformed_realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_fPolynomial_sequence_realrooted_named)
  "rr_fPolynomial_sequence_realrooted" " using "
    "degree" ":=" term ","
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_of_fPolynomial_sequence_realrooted_named)
  "rr_of_fPolynomial_sequence_realrooted" " using "
    "degree" ":=" term ","
    "transformed_realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_fPolynomial_prec_named)
  "rr_fPolynomial_prec" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "prec" ":=" term :
  tactic

syntax (name := rr_of_fPolynomial_prec_named)
  "rr_of_fPolynomial_prec" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "transformed_prec" ":=" term :
  tactic

syntax (name := rr_fPolynomial_prec_iff_named)
  "rr_fPolynomial_prec_iff" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_fPolynomial_pos_combo_named)
  "rr_fPolynomial_pos_combo" " using "
    "prec" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_fPolynomial_sequence_prec_named)
  "rr_fPolynomial_sequence_prec" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "prec" ":=" term :
  tactic

syntax (name := rr_of_fPolynomial_sequence_prec_named)
  "rr_of_fPolynomial_sequence_prec" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "transformed_prec" ":=" term :
  tactic

syntax (name := rr_fPolynomial_sequence_pos_combo_named)
  "rr_fPolynomial_sequence_pos_combo" " using "
    "prec" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_fPolynomial_realrooted using
        degree := $hdeg:term,
        realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_fPolynomial_of_isRealRooted_cert
          $hdeg $hrr $hnn)
  | `(tactic|
      rr_of_fPolynomial_realrooted using
        degree := $hdeg:term,
        transformed_realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_fPolynomial_isRealRooted_cert
          $hdeg $hrr $hnn)
  | `(tactic|
      rr_fPolynomial_sequence_realrooted using
        degree := $hdeg:term,
        realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_fPolynomial_sequence_of_isRealRooted_cert
          $hdeg $hrr $hnn)
  | `(tactic|
      rr_of_fPolynomial_sequence_realrooted using
        degree := $hdeg:term,
        transformed_realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_fPolynomial_sequence_isRealRooted_cert
          $hdeg $hrr $hnn)
  | `(tactic|
      rr_fPolynomial_prec using
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term,
        prec := $hprec:term) =>
      `(tactic|
        exact RealRooted.prec_fPolynomial_of_prec $hud $hvd $hu $hv $hprec)
  | `(tactic|
      rr_of_fPolynomial_prec using
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term,
        transformed_prec := $hprec:term) =>
      `(tactic|
        exact RealRooted.prec_of_prec_fPolynomial $hud $hvd $hu $hv $hprec)
  | `(tactic|
      rr_fPolynomial_prec_iff using
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term) =>
      `(tactic|
        exact RealRooted.precFPolynomialTransport $hud $hvd $hu $hv)
  | `(tactic|
      rr_fPolynomial_pos_combo using
        prec := $hprec:term,
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term) =>
      `(tactic|
        exact RealRooted.posComboRealRooted_fPolynomial_of_prec
          $hprec $hud $hvd $hu $hv)
  | `(tactic|
      rr_fPolynomial_sequence_prec using
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term,
        prec := $hprec:term) =>
      `(tactic|
        exact RealRooted.prec_fPolynomial_sequence_of_prec
          $hud $hvd $hu $hv $hprec)
  | `(tactic|
      rr_of_fPolynomial_sequence_prec using
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term,
        transformed_prec := $hprec:term) =>
      `(tactic|
        exact RealRooted.prec_of_prec_fPolynomial_sequence
          $hud $hvd $hu $hv $hprec)
  | `(tactic|
      rr_fPolynomial_sequence_pos_combo using
        prec := $hprec:term,
        left_degree := $hud:term,
        right_degree := $hvd:term,
        left_nonneg := $hu:term,
        right_nonneg := $hv:term) =>
      `(tactic|
        exact RealRooted.posComboRealRooted_fPolynomial_sequence_of_prec
          $hprec $hud $hvd $hu $hv)

end Tactic
end RealRooted
