import RealRooted.AffineFamily
import RealRooted.EulerOperator
import RealRooted.WagnerRightSum

/-!
# Euler-operator tactic frontends

Thin wrappers for the proved `theta + 1`, polar-theta, and iterate APIs in
`RealRooted.EulerOperator`.
-/

open Polynomial

namespace RealRooted

/-- Positive Euler-lag induction for a polynomial sequence.

If consecutive terms begin in proper position and
`P (n + 2) = (X * P (n + 1))' + c n * X * P n` with `c n > 0`, then
nonnegative coefficients and positive leading coefficients propagate proper
position through the whole sequence. -/
theorem prec_positive_euler_lag_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n, HasNonnegCoeffs (P n))
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hc : ∀ n, 0 < c n)
    (hrec : ∀ n,
      P (n + 2) = (X * P (n + 1)).derivative + C (c n) * (X * P n)) :
    ∀ n, Prec (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hnext_ne : P (n + 1) ≠ 0 := (hpos (n + 1)).ne_zero
      have hXnext : (X * P (n + 1) ≠ 0) ∧ (X * P (n + 1)).Splits :=
        isRealRooted_X_mul hnext_ne ih.2.1.2
      have hXnext_pos : HasPosLeadingCoeff (X * P (n + 1)) :=
        (hpos (n + 1)).X_mul
      have hXnext_degree :
          (X * P (n + 1)).natDegree = 1 + (P (n + 1)).natDegree := by
        rw [natDegree_mul X_ne_zero hnext_ne, natDegree_X]
      have hderivative : Prec (X * P (n + 1)).derivative (X * P (n + 1)) :=
        (interlaces_derivative_of_pos_natDegree
          hXnext.1 hXnext.2 hXnext_pos (by lia)).toPrec
      have hderivative_pos : HasPosLeadingCoeff (X * P (n + 1)).derivative :=
        hXnext_pos.derivative (by lia)
      have hlag : Prec (C (c n) * (X * P n)) (X * P (n + 1)) :=
        (prec_mul_common_factor isRealRooted_X.1 isRealRooted_X.2 ih).C_mul_left
          (hc n).ne'
      have hlag_pos : HasPosLeadingCoeff (C (c n) * (X * P n)) :=
        hasPosLeadingCoeff_C_mul (hc n) (hpos n).X_mul
      have hsum : Prec (P (n + 2)) (X * P (n + 1)) := by
        rw [hrec n]
        exact
          prec_add_of_prec_right_of_posLeadingCoeff
            hderivative hlag hderivative_pos hlag_pos
      exact
        prec_of_prec_mul_X_of_nonneg hsum (hnonneg (n + 1)) (hnonneg (n + 2))

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

theorem theta_sequence_pf
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (theta (P i)) := fun i =>
  RealRooted.theta_preserves_pf (hP i)

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

syntax (name := rr_theta_pf_named)
  "rr_theta_pf" " using " "pf" ":=" term :
  tactic

syntax (name := rr_theta_sequence_pf_named)
  "rr_theta_sequence_pf" " using " "pf" ":=" term :
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

syntax (name := rr_prec_positive_euler_lag_sequence_named)
  "rr_prec_positive_euler_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg" ":=" term ","
    "positive_lc" ":=" term ","
    "lag_positive" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_prec_positive_euler_lag_sequence using
        base := $hbase:term,
        nonneg := $hnonneg:term,
        positive_lc := $hpos:term,
        lag_positive := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_positive_euler_lag_sequence
          $hbase $hnonneg $hpos $hc $hrec)
  | `(tactic| rr_theta_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.theta $hp)
  | `(tactic| rr_theta_sequence_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.theta_sequence_nonneg $hp)
  | `(tactic| rr_thetaPlusOne_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.thetaPlusOne $hp)
  | `(tactic| rr_thetaPlusOne_sequence_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.thetaPlusOne_sequence_nonneg $hp)
  | `(tactic| rr_theta_pf using pf := $hp:term) =>
      `(tactic| exact RealRooted.theta_preserves_pf $hp)
  | `(tactic| rr_theta_sequence_pf using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.theta_sequence_pf $hp)
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
