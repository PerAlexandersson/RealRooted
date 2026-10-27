module

public import RealRooted.AffineFamily
public import RealRooted.EulerOperator
import RealRooted.WagnerRightSum
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
import RealRooted.WagnerX.AffineFactors
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Linear

/-!
# Euler-operator family lemmas

Pointwise lifts of the proved `theta + 1`, polar-theta, and iterate APIs in
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

/-- The Euler operator preserves coefficientwise nonnegativity pointwise. -/
theorem theta_sequence_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (theta (P i)) := fun i =>
  RealRooted.HasNonnegCoeffs.theta (hP i)

/-- The operator `theta + 1` preserves coefficientwise nonnegativity
pointwise. -/
theorem thetaPlusOne_sequence_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (thetaPlusOne (P i)) := fun i =>
  RealRooted.HasNonnegCoeffs.thetaPlusOne (hP i)

/-- The Euler operator preserves the PF cone pointwise. -/
theorem theta_sequence_pf
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (theta (P i)) := fun i =>
  RealRooted.theta_preserves_pf (hP i)

/-- The polar-theta operator preserves coefficientwise nonnegativity pointwise
under the corresponding degree bounds. -/
theorem polarTheta_sequence_nonneg
    {N : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ N i) :
    ∀ i : Nat, HasNonnegCoeffs (polarTheta (N i) (P i)) := fun i =>
  RealRooted.HasNonnegCoeffs.polarTheta (hP i) (hdeg i)

/-- The operator `theta + 1` preserves the PF cone pointwise. -/
theorem thetaPlusOne_sequence_pf
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (thetaPlusOne (P i)) := fun i =>
  RealRooted.thetaPlusOne_preserves_pf (hP i)

/-- The polar-theta operator preserves the PF cone pointwise under the
corresponding degree bounds. -/
theorem polarTheta_sequence_pf
    {N : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ N i) :
    ∀ i : Nat, IsPFPolynomial (polarTheta (N i) (P i)) := fun i =>
  RealRooted.polarTheta_preserves_pf (hP i) (hdeg i)

/-- Pointwise iterates of `theta + 1` preserve the PF cone. -/
theorem iterateThetaPlusOne_sequence_pf
    {l : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (iterateThetaPlusOne (l i) (P i)) := fun i =>
  RealRooted.iterateThetaPlusOne_preserves_pf (l i) (hP i)

/-- The operator `theta + 1` preserves interlacing pointwise. -/
theorem thetaPlusOne_sequence_interl
    {P Q : Nat → ℝ[X]} (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ i : Nat, Interl (thetaPlusOne (P i)) (thetaPlusOne (Q i)) := fun i =>
  (hPQ i).thetaPlusOne

/-- Pointwise iterates of `theta + 1` preserve interlacing. -/
theorem iterateThetaPlusOne_sequence_interl
    {l : Nat → Nat} {P Q : Nat → ℝ[X]} (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ i : Nat,
      Interl (iterateThetaPlusOne (l i) (P i)) (iterateThetaPlusOne (l i) (Q i)) :=
    fun i =>
  (hPQ i).iterateThetaPlusOne (l i)

end Tactic
end RealRooted

