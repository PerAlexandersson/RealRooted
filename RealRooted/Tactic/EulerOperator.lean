import RealRooted.EulerOperator

/-!
# Euler-operator tactic frontends

Thin wrappers for the proved `theta + 1`, polar-theta, and iterate APIs in
`RealRooted.EulerOperator`.
-/

open Polynomial

namespace RealRooted

/-- Default proved PF preservation for the `l`-fold iterate of `theta + 1`. -/
theorem isPFPolynomial_iterateThetaPlusOne
    (l : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (iterateThetaPlusOne l p) :=
  iterateThetaPlusOne_preserves_pf thetaPlusOne_preserves_pf l hp

/-- Default proved `Prec0` preservation for the `l`-fold iterate of `theta + 1`. -/
theorem prec0_iterateThetaPlusOne
    (l : ℕ) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Prec0 p q) :
    Prec0 (iterateThetaPlusOne l p) (iterateThetaPlusOne l q) :=
  iterateThetaPlusOne_preserves_prec0
    thetaPlusOne_preserves_pf thetaPlusOnePreservesPrec0 l hp hq hpq

namespace Tactic

theorem theta_sequence_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (theta (P i)) := fun i =>
  RealRooted.HasNonnegCoeffs.theta (hP i)

theorem thetaPlusOne_sequence_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (thetaPlusOne (P i)) := fun i =>
  RealRooted.HasNonnegCoeffs.thetaPlusOne (hP i)

theorem polarTheta_sequence_nonneg
    {N : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ N i) :
    ∀ i : Nat, HasNonnegCoeffs (polarTheta (N i) (P i)) := fun i =>
  RealRooted.HasNonnegCoeffs.polarTheta (hP i) (hdeg i)

theorem thetaPlusOne_sequence_pf
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (thetaPlusOne (P i)) := fun i =>
  RealRooted.thetaPlusOne_preserves_pf (hP i)

theorem polarTheta_sequence_pf
    {N : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ N i) :
    ∀ i : Nat, IsPFPolynomial (polarTheta (N i) (P i)) := fun i =>
  RealRooted.polarTheta_preserves_pf (hP i) (hdeg i)

theorem iterateThetaPlusOne_sequence_pf
    {l : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (iterateThetaPlusOne (l i) (P i)) := fun i =>
  RealRooted.isPFPolynomial_iterateThetaPlusOne (l i) (hP i)

theorem thetaPlusOne_sequence_prec0
    {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hPQ : ∀ i : Nat, Prec0 (P i) (Q i)) :
    ∀ i : Nat, Prec0 (thetaPlusOne (P i)) (thetaPlusOne (Q i)) := fun i =>
  RealRooted.thetaPlusOnePreservesPrec0 (hP i) (hQ i) (hPQ i)

theorem iterateThetaPlusOne_sequence_prec0
    {l : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hPQ : ∀ i : Nat, Prec0 (P i) (Q i)) :
    ∀ i : Nat,
      Prec0 (iterateThetaPlusOne (l i) (P i)) (iterateThetaPlusOne (l i) (Q i)) :=
    fun i =>
  RealRooted.prec0_iterateThetaPlusOne (l i) (hP i) (hQ i) (hPQ i)

syntax (name := rr_theta_nonneg_named)
  "rr_theta_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_theta_sequence_nonneg_named)
  "rr_theta_sequence_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_nonneg_named)
  "rr_thetaPlusOne_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_sequence_nonneg_named)
  "rr_thetaPlusOne_sequence_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_polarTheta_nonneg_named)
  "rr_polarTheta_nonneg" " using "
    "nonneg" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_polarTheta_sequence_nonneg_named)
  "rr_polarTheta_sequence_nonneg" " using "
    "nonneg" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_pf_named)
  "rr_thetaPlusOne_pf" " using " "pf" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_sequence_pf_named)
  "rr_thetaPlusOne_sequence_pf" " using " "pf" ":=" term :
  tactic

syntax (name := rr_polarTheta_pf_named)
  "rr_polarTheta_pf" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_polarTheta_sequence_pf_named)
  "rr_polarTheta_sequence_pf" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_iterateThetaPlusOne_pf_named)
  "rr_iterateThetaPlusOne_pf" " using "
    "index" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_iterateThetaPlusOne_sequence_pf_named)
  "rr_iterateThetaPlusOne_sequence_pf" " using "
    "index" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_prec0_named)
  "rr_thetaPlusOne_prec0" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_sequence_prec0_named)
  "rr_thetaPlusOne_sequence_prec0" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

syntax (name := rr_iterateThetaPlusOne_prec0_named)
  "rr_iterateThetaPlusOne_prec0" " using "
    "index" ":=" term ","
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

syntax (name := rr_iterateThetaPlusOne_sequence_prec0_named)
  "rr_iterateThetaPlusOne_sequence_prec0" " using "
    "index" ":=" term ","
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_theta_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.theta $hp)
  | `(tactic| rr_theta_sequence_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.theta_sequence_nonneg $hp)
  | `(tactic| rr_thetaPlusOne_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.thetaPlusOne $hp)
  | `(tactic| rr_thetaPlusOne_sequence_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.thetaPlusOne_sequence_nonneg $hp)
  | `(tactic|
      rr_polarTheta_nonneg using
        nonneg := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.polarTheta $hp $hdeg)
  | `(tactic|
      rr_polarTheta_sequence_nonneg using
        nonneg := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.polarTheta_sequence_nonneg $hp $hdeg)
  | `(tactic| rr_thetaPlusOne_pf using pf := $hp:term) =>
      `(tactic| exact RealRooted.thetaPlusOne_preserves_pf $hp)
  | `(tactic| rr_thetaPlusOne_sequence_pf using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.thetaPlusOne_sequence_pf $hp)
  | `(tactic|
      rr_polarTheta_pf using
        pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.polarTheta_preserves_pf $hp $hdeg)
  | `(tactic|
      rr_polarTheta_sequence_pf using
        pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.polarTheta_sequence_pf $hp $hdeg)
  | `(tactic|
      rr_iterateThetaPlusOne_pf using
        index := $l:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_iterateThetaPlusOne $l $hp)
  | `(tactic|
      rr_iterateThetaPlusOne_sequence_pf using
        index := $l:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.iterateThetaPlusOne_sequence_pf (l := $l) $hp)
  | `(tactic|
      rr_thetaPlusOne_prec0 using
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.thetaPlusOnePreservesPrec0 $hp $hq $hpq)
  | `(tactic|
      rr_thetaPlusOne_sequence_prec0 using
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.Tactic.thetaPlusOne_sequence_prec0 $hp $hq $hpq)
  | `(tactic|
      rr_iterateThetaPlusOne_prec0 using
        index := $l:term,
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.prec0_iterateThetaPlusOne $l $hp $hq $hpq)
  | `(tactic|
      rr_iterateThetaPlusOne_sequence_prec0 using
        index := $l:term,
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic|
        exact RealRooted.Tactic.iterateThetaPlusOne_sequence_prec0
          (l := $l) $hp $hq $hpq)

end Tactic
end RealRooted
