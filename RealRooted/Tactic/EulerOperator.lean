module

public import RealRooted.AffineFamily
public import RealRooted.EulerOperator
public import RealRooted.WagnerRightSum

/-!
# Euler-operator tactic frontends

Thin wrappers for the proved `theta + 1`, polar-theta, and iterate APIs in
`RealRooted.EulerOperator`.
-/

public section

open Polynomial

namespace RealRooted

/-- Positive Euler-lag induction for a polynomial sequence.

If consecutive terms begin in proper position and
`P (n + 2) = (X * P (n + 1))' + c n * X * P n` with `c n > 0`, then
nonnegative coefficients and positive leading coefficients propagate proper
position through the whole sequence. -/
theorem strictInterl_positive_euler_lag_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hnonneg : ∀ n, HasNonnegCoeffs (P n))
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hc : ∀ n, 0 < c n)
    (hrec : ∀ n,
      P (n + 2) = (X * P (n + 1)).derivative + C (c n) * (X * P n)) :
    ∀ n, StrictInterl (P n) (P (n + 1)) := by
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
      have hderivative : StrictInterl (X * P (n + 1)).derivative (X * P (n + 1)) :=
        (interlaces_derivative_of_pos_natDegree
          hXnext.1 hXnext.2 hXnext_pos (by lia)).toStrictInterl
      have hderivative_pos : HasPosLeadingCoeff (X * P (n + 1)).derivative :=
        hXnext_pos.derivative (by lia)
      have hlag : StrictInterl (C (c n) * (X * P n)) (X * P (n + 1)) :=
        (ih.mul_common_factor isRealRooted_X.1 isRealRooted_X.2).C_mul_left
          (hc n).ne'
      have hlag_pos : HasPosLeadingCoeff (C (c n) * (X * P n)) :=
        hasPosLeadingCoeff_C_mul (hc n) (hpos n).X_mul
      have hsum : StrictInterl (P (n + 2)) (X * P (n + 1)) := by
        rw [hrec n]
        exact
          StrictInterl.add_of_right_of_posLeadingCoeff
            hderivative hlag hderivative_pos hlag_pos
      exact
        strictInterl_of_strictInterl_X_mul_of_nonneg hsum (hnonneg (n + 1)) (hnonneg (n + 2))

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
  RealRooted.iterateThetaPlusOne_preserves_pf (l i) (hP i)

theorem thetaPlusOne_sequence_interl
    {P Q : Nat → ℝ[X]} (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ i : Nat, Interl (thetaPlusOne (P i)) (thetaPlusOne (Q i)) := fun i =>
  (hPQ i).thetaPlusOne

theorem iterateThetaPlusOne_sequence_interl
    {l : Nat → Nat} {P Q : Nat → ℝ[X]} (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ i : Nat,
      Interl (iterateThetaPlusOne (l i) (P i)) (iterateThetaPlusOne (l i) (Q i)) :=
    fun i =>
  (hPQ i).iterateThetaPlusOne (l i)

/-- Closes `HasNonnegCoeffs (theta p)` from `nonneg : HasNonnegCoeffs p`. -/
syntax (name := rr_theta_nonneg_named)
  "rr_theta_nonneg" " using " "nonneg" ":=" term :
  tactic

/-- Sequence form of `rr_theta_nonneg`: the same certificate for every index `i`. -/
syntax (name := rr_theta_sequence_nonneg_named)
  "rr_theta_sequence_nonneg" " using " "nonneg" ":=" term :
  tactic

/-- Closes `HasNonnegCoeffs (thetaPlusOne p)` from `nonneg : HasNonnegCoeffs p`. -/
syntax (name := rr_thetaPlusOne_nonneg_named)
  "rr_thetaPlusOne_nonneg" " using " "nonneg" ":=" term :
  tactic

/-- Sequence form of `rr_thetaPlusOne_nonneg`: the same certificate for every index `i`. -/
syntax (name := rr_thetaPlusOne_sequence_nonneg_named)
  "rr_thetaPlusOne_sequence_nonneg" " using " "nonneg" ":=" term :
  tactic

/-- Closes `HasNonnegCoeffs (polarTheta N p)` from `nonneg : HasNonnegCoeffs p` and
`degree : p.natDegree ≤ N`. -/
syntax (name := rr_polarTheta_nonneg_named)
  "rr_polarTheta_nonneg" " using "
    "nonneg" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Sequence form of `rr_polarTheta_nonneg`: the same certificate for every index `i`, with
`N i` in place of `N`. -/
syntax (name := rr_polarTheta_sequence_nonneg_named)
  "rr_polarTheta_sequence_nonneg" " using "
    "nonneg" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (theta p)` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_theta_pf_named)
  "rr_theta_pf" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_theta_pf`: the same certificate for every index `i`. -/
syntax (name := rr_theta_sequence_pf_named)
  "rr_theta_sequence_pf" " using " "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (thetaPlusOne p)` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_thetaPlusOne_pf_named)
  "rr_thetaPlusOne_pf" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_thetaPlusOne_pf`: the same certificate for every index `i`. -/
syntax (name := rr_thetaPlusOne_sequence_pf_named)
  "rr_thetaPlusOne_sequence_pf" " using " "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (polarTheta N p)` from `pf : IsPFPolynomial p` and
`degree : p.natDegree ≤ N`. -/
syntax (name := rr_polarTheta_pf_named)
  "rr_polarTheta_pf" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Sequence form of `rr_polarTheta_pf`: the same certificate for every index `i`, with `N i` in
place of `N`. -/
syntax (name := rr_polarTheta_sequence_pf_named)
  "rr_polarTheta_sequence_pf" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (iterateThetaPlusOne l p)` from `index : l` and
`pf : IsPFPolynomial p`. -/
syntax (name := rr_iterateThetaPlusOne_pf_named)
  "rr_iterateThetaPlusOne_pf" " using "
    "index" ":=" term ","
    "pf" ":=" term :
  tactic

/-- Sequence form of `rr_iterateThetaPlusOne_pf`: the same certificate for every index `i`, with
`l i` in place of `l`. -/
syntax (name := rr_iterateThetaPlusOne_sequence_pf_named)
  "rr_iterateThetaPlusOne_sequence_pf" " using "
    "index" ":=" term ","
    "pf" ":=" term :
  tactic

/-- Closes `Interl (thetaPlusOne p) (thetaPlusOne q)` from `interl : Interl p q`.
The former PF-certificate fields remain accepted for compatibility. -/
syntax (name := rr_thetaPlusOne_interl_named)
  "rr_thetaPlusOne_interl" " using " "interl" ":=" term :
  tactic

@[tactic_alt rr_thetaPlusOne_interl_named]
syntax (name := rrThetaPlusOneInterlCompat)
  "rr_thetaPlusOne_interl" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "interl" ":=" term :
  tactic

/-- Sequence form of `rr_thetaPlusOne_interl`: the same certificate for every
index `i`. The former PF-certificate fields remain accepted. -/
syntax (name := rr_thetaPlusOne_sequence_interl_named)
  "rr_thetaPlusOne_sequence_interl" " using " "interl" ":=" term :
  tactic

@[tactic_alt rr_thetaPlusOne_sequence_interl_named]
syntax (name := rrThetaPlusOneSequenceInterlCompat)
  "rr_thetaPlusOne_sequence_interl" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "interl" ":=" term :
  tactic

/-- Closes `Interl (iterateThetaPlusOne l p) (iterateThetaPlusOne l q)` from
`index : l` and `interl : Interl p q`. The former PF-certificate fields remain accepted. -/
syntax (name := rr_iterateThetaPlusOne_interl_named)
  "rr_iterateThetaPlusOne_interl" " using "
    "index" ":=" term ","
    "interl" ":=" term :
  tactic

@[tactic_alt rr_iterateThetaPlusOne_interl_named]
syntax (name := rrIterateThetaPlusOneInterlCompat)
  "rr_iterateThetaPlusOne_interl" " using "
    "index" ":=" term ","
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "interl" ":=" term :
  tactic

/-- Sequence form of `rr_iterateThetaPlusOne_interl`: the same certificate for
every index `i`, with `l i` in place of `l`. The former PF fields remain accepted. -/
syntax (name := rr_iterateThetaPlusOne_sequence_interl_named)
  "rr_iterateThetaPlusOne_sequence_interl" " using "
    "index" ":=" term ","
    "interl" ":=" term :
  tactic

@[tactic_alt rr_iterateThetaPlusOne_sequence_interl_named]
syntax (name := rrIterateThetaPlusOneSequenceInterlCompat)
  "rr_iterateThetaPlusOne_sequence_interl" " using "
    "index" ":=" term ","
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "interl" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = (X * P (n + 1))' + C (c n) * (X * P n)`; the arguments are
`base : StrictInterl (P 0) (P 1)`, `nonneg` and `positive_lc` for every `P n`,
`lag_positive : ∀ n, 0 < c n` and `recurrence`. -/
syntax (name := rr_strict_interl_positive_euler_lag_sequence_named)
  "rr_strict_interl_positive_euler_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg" ":=" term ","
    "positive_lc" ":=" term ","
    "lag_positive" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_strict_interl_positive_euler_lag_sequence using
        base := $hbase:term,
        nonneg := $hnonneg:term,
        positive_lc := $hpos:term,
        lag_positive := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.strictInterl_positive_euler_lag_sequence
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
      `(tactic| exact RealRooted.iterateThetaPlusOne_preserves_pf $l $hp)
  | `(tactic|
      rr_iterateThetaPlusOne_sequence_pf using
        index := $l:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.iterateThetaPlusOne_sequence_pf (l := $l) $hp)
  | `(tactic|
      rr_thetaPlusOne_interl using interl := $hpq:term) =>
      `(tactic| exact RealRooted.Interl.thetaPlusOne $hpq)
  | `(tactic|
      rr_thetaPlusOne_interl using
        left_pf := $_hp:term,
        right_pf := $_hq:term,
        interl := $hpq:term) =>
      `(tactic| exact RealRooted.Interl.thetaPlusOne $hpq)
  | `(tactic|
      rr_thetaPlusOne_sequence_interl using interl := $hpq:term) =>
      `(tactic| exact RealRooted.Tactic.thetaPlusOne_sequence_interl $hpq)
  | `(tactic|
      rr_thetaPlusOne_sequence_interl using
        left_pf := $_hp:term,
        right_pf := $_hq:term,
        interl := $hpq:term) =>
      `(tactic| exact RealRooted.Tactic.thetaPlusOne_sequence_interl $hpq)
  | `(tactic|
      rr_iterateThetaPlusOne_interl using
        index := $l:term,
        interl := $hpq:term) =>
      `(tactic| exact RealRooted.Interl.iterateThetaPlusOne $hpq $l)
  | `(tactic|
      rr_iterateThetaPlusOne_interl using
        index := $l:term,
        left_pf := $_hp:term,
        right_pf := $_hq:term,
        interl := $hpq:term) =>
      `(tactic| exact RealRooted.Interl.iterateThetaPlusOne $hpq $l)
  | `(tactic|
      rr_iterateThetaPlusOne_sequence_interl using
        index := $l:term,
        interl := $hpq:term) =>
      `(tactic|
        exact RealRooted.Tactic.iterateThetaPlusOne_sequence_interl
          (l := $l) $hpq)
  | `(tactic|
      rr_iterateThetaPlusOne_sequence_interl using
        index := $l:term,
        left_pf := $_hp:term,
        right_pf := $_hq:term,
        interl := $hpq:term) =>
      `(tactic|
        exact RealRooted.Tactic.iterateThetaPlusOne_sequence_interl
          (l := $l) $hpq)

end Tactic
end RealRooted
namespace RealRooted

end RealRooted

namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
