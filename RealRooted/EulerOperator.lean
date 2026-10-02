import RealRooted.Derivative
import RealRooted.PFPolynomial
import RealRooted.ObreschkoffConverse

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Euler operator and polar derivative interfaces

This file records the standard one-variable operators used in normalized
Eulerian-row arguments:

* `theta p = X * p.derivative`;
* `thetaPlusOne p = theta p + p = (X * p).derivative`;
* `polarTheta N p = C N * p - theta p`.

The coefficient, nonnegative-coefficient, PF-preservation, and interlacing
preservation lemmas below reduce to the existing derivative/PF API.  The
bounded-degree polar-theta interlacing theorem is
`polarTheta_preserves_interl` in `RealRooted.EulerOperator.Polar.ProperPosition`.
-/

/-- Euler operator `theta = X d/dX`. -/
def theta (p : ℝ[X]) : ℝ[X] :=
  X * p.derivative

/-- The operator `theta + 1`; equivalently, `p ↦ (X * p)'`. -/
def thetaPlusOne (p : ℝ[X]) : ℝ[X] :=
  theta p + p

/-- The `l`-fold iterate of `theta + 1`. -/
def iterateThetaPlusOne (l : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (thetaPlusOne^[l]) p

/-- Polar theta operator `N - theta`. -/
def polarTheta (N : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (N : ℝ) * p - theta p

/-- The Euler operator is additive. -/
theorem theta_add (p q : ℝ[X]) : theta (p + q) = theta p + theta q := by
  simp [theta, derivative_add, mul_add]

/-- The Euler operator commutes with scalar multiplication. -/
theorem theta_C_mul (a : ℝ) (p : ℝ[X]) : theta (C a * p) = C a * theta p := by
  simp [theta, derivative_mul]
  ring

@[simp] theorem coeff_theta (p : ℝ[X]) (n : ℕ) :
    (theta p).coeff n = (n : ℝ) * p.coeff n := by
  cases n with
  | zero =>
      simp [theta]
  | succ n =>
      rw [theta, coeff_X_mul, coeff_derivative]
      grind

@[simp] theorem coeff_thetaPlusOne (p : ℝ[X]) (n : ℕ) :
    (thetaPlusOne p).coeff n = ((n : ℝ) + 1) * p.coeff n := by
  simp [thetaPlusOne]
  ring

theorem thetaPlusOne_eq_derivative_X_mul (p : ℝ[X]) :
    thetaPlusOne p = (X * p).derivative := by
  ext n
  rw [coeff_thetaPlusOne, coeff_derivative]
  cases n with
  | zero =>
      simp
  | succ n =>
      simp [Nat.cast_add, Nat.cast_one]
      ring

@[simp] theorem iterateThetaPlusOne_zero (p : ℝ[X]) :
    iterateThetaPlusOne 0 p = p :=
  rfl

@[simp] theorem iterateThetaPlusOne_succ (l : ℕ) (p : ℝ[X]) :
    iterateThetaPlusOne (l + 1) p = thetaPlusOne (iterateThetaPlusOne l p) :=
  by simpa [iterateThetaPlusOne] using Function.iterate_succ_apply' thetaPlusOne l p

@[simp] theorem coeff_polarTheta (N : ℕ) (p : ℝ[X]) (n : ℕ) :
    (polarTheta N p).coeff n = ((N : ℝ) - n) * p.coeff n := by
  simp [polarTheta]
  ring

/-- The polar theta operator commutes with `theta + 1`. -/
theorem polarTheta_thetaPlusOne_comm (N : ℕ) (p : ℝ[X]) :
    polarTheta N (thetaPlusOne p) = thetaPlusOne (polarTheta N p) := by
  ext k
  rw [coeff_polarTheta, coeff_thetaPlusOne, coeff_thetaPlusOne,
    coeff_polarTheta]
  ring

theorem HasNonnegCoeffs.thetaPlusOne {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (thetaPlusOne p) := by
  intro n
  simpa [coeff_thetaPlusOne] using mul_nonneg (by positivity) (hp n)

theorem HasNonnegCoeffs.theta {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (theta p) := by
  intro n
  simpa [coeff_theta] using mul_nonneg (by positivity) (hp n)

theorem HasNonnegCoeffs.polarTheta {N : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hdeg : p.natDegree ≤ N) :
    HasNonnegCoeffs (polarTheta N p) := by
  intro n
  by_cases hn : n ≤ N
  · have hn' : (n : ℝ) ≤ N := Nat.cast_le.mpr hn
    simpa [coeff_polarTheta] using mul_nonneg (sub_nonneg.mpr hn') (hp n)
  · have hNn : N < n := Nat.lt_of_not_ge hn
    have hpcoeff : p.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hNn)
    simp [hpcoeff]

/-- `theta` preserves the polynomial PF cone. -/
theorem theta_preserves_pf {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (theta p) := by
  dsimp [theta]
  exact hp.derivative.X_mul

/-- `theta` preserves real-rootedness and nonpositive roots on the polynomial
PF cone. -/
theorem thetaPreservesRealRootedOrZero {p : ℝ[X]} (hp : IsPFPolynomial p) :
    (theta p = 0 ∨ (theta p).Splits) ∧ ∀ r ∈ (theta p).roots, r ≤ 0 :=
  ⟨(theta_preserves_pf hp).eq_zero_or_splits, (theta_preserves_pf hp).roots_nonpos⟩

/-- `theta` preserves weak interlacing on the polynomial PF cone.  This
proposition is proved by `thetaPreservesInterl`; the name is kept for
downstream users. -/
def thetaPreservesInterlStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    Interl p q →
    Interl (theta p) (theta q)

/-- `theta` preserves weak interlacing on the polynomial PF cone, obtained
from the derivative preservation theorem and multiplication by `X`. -/
theorem thetaPreservesInterl {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    Interl (theta p) (theta q) := by
  simpa [theta] using
    interl_X_mul_both_of_pf hp.derivative hq.derivative (derivativePreservesInterl hpq)

/-- `theta + 1` preserves the polynomial PF cone. -/
theorem thetaPlusOne_preserves_pf {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (thetaPlusOne p) := by
  simpa [thetaPlusOne_eq_derivative_X_mul] using hp.X_mul.derivative

/-- `theta + 1` preserves weak interlacing on the polynomial PF cone, obtained
from the derivative preservation theorem. -/
theorem thetaPlusOnePreservesInterl {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    Interl (thetaPlusOne p) (thetaPlusOne q) := by
  simpa [thetaPlusOne_eq_derivative_X_mul] using
    derivativePreservesInterl (interl_X_mul_both_of_pf hp hq hpq)

/-- Unproved target: a PF polynomial is in weak interlacing with each of its
iterates under `theta + 1`. -/
def iterateThetaPlusOneSelfInterlStatement : Prop :=
  ∀ {p : ℝ[X]} (l : ℕ),
    IsPFPolynomial p →
    Interl p (iterateThetaPlusOne l p)

theorem polarTheta_eq_reciprocalShift_derivative_reciprocalShift
    (N : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ N) :
    polarTheta N p =
      reciprocalShift (N - 1) ((reciprocalShift N p).derivative) := by
  ext k
  rw [coeff_polarTheta, coeff_reciprocalShift, coeff_derivative,
    coeff_reciprocalShift]
  by_cases hk : k < N
  · have hk_le : k ≤ N := le_of_lt hk
    have hk_pred : k ≤ N - 1 := Nat.le_pred_of_lt hk
    rw [Polynomial.revAt_le hk_pred]
    have hsum : N - 1 - k + 1 = N - k := by grind
    have hcast : ((N - 1 - k : ℕ) : ℝ) + 1 = ((N - k : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using congrArg (fun m : ℕ => (m : ℝ)) hsum
    rw [hcast]
    rw [hsum]
    rw [Polynomial.revAt_le (Nat.sub_le N k)]
    rw [Nat.sub_sub_self hk_le]
    rw [Nat.cast_sub hk_le]
    ring
  · have hNk : N ≤ k := le_of_not_gt hk
    have hidx : N < Polynomial.revAt (N - 1) k + 1 := by
      cases N with
      | zero =>
          simp
      | succ N =>
          have hNk' : N < k := by grind
          rw [show N + 1 - 1 = N by simp]
          rw [Polynomial.revAt_eq_self_of_lt hNk']
          simp_all
    have hrhs_coeff :
        p.coeff (Polynomial.revAt N (Polynomial.revAt (N - 1) k + 1)) = 0 := by
      rw [Polynomial.revAt_eq_self_of_lt hidx]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hidx)
    rw [hrhs_coeff]
    simp
    by_cases hkN : k = N
    · simp_all
    · have hNklt : N < k := lt_of_le_of_ne hNk (Ne.symm hkN)
      have hpcoeff : p.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hNklt)
      simp [hpcoeff]

/-- The polar-theta operator `N - theta` preserves the polynomial PF cone for
polynomials of degree at most `N`. -/
theorem polarTheta_preserves_pf {N : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ N) :
    IsPFPolynomial (polarTheta N p) := by
  rw [polarTheta_eq_reciprocalShift_derivative_reciprocalShift N p hdeg]
  have hshift : IsPFPolynomial (reciprocalShift N p) :=
    reciprocalShift_preserves_pf hp hdeg
  have hdeg_shift : (reciprocalShift N p).natDegree ≤ N := by
    unfold reciprocalShift
    exact (Polynomial.natDegree_reflect_le (N := N) (p := p)).trans
      (max_le le_rfl hdeg)
  have hder_deg : (reciprocalShift N p).derivative.natDegree ≤ N - 1 := by
    rw [(reciprocalShift N p).natDegree_derivative]
    exact Nat.sub_le_sub_right hdeg_shift 1
  exact reciprocalShift_preserves_pf hshift.derivative hder_deg

/-- Polar-theta interlacing preservation on the bounded-degree PF cone.  This
proposition is proved by `RealRooted.polarTheta_preserves_interl` in
`EulerOperator.Polar.ProperPosition`; the name is kept for downstream users. -/
def polarThetaPreservesInterlStatement : Prop :=
  ∀ {N : ℕ} {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    p.natDegree ≤ N →
    q.natDegree ≤ N →
    Interl p q →
    Interl (polarTheta N p) (polarTheta N q)

/-- PF preservation for the `l`-fold iterate of `theta + 1`. -/
theorem iterateThetaPlusOne_preserves_pf
    (l : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (iterateThetaPlusOne l p) := by
  induction l generalizing p with
  | zero =>
      simpa using hp
  | succ l ih =>
      simpa [iterateThetaPlusOne_succ] using thetaPlusOne_preserves_pf (ih hp)

/-- `Interl` preservation for the `l`-fold iterate of `theta + 1`. -/
theorem iterateThetaPlusOne_preserves_interl
    (l : ℕ) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    Interl (iterateThetaPlusOne l p) (iterateThetaPlusOne l q) := by
  induction l generalizing p q with
  | zero =>
      simpa using hpq
  | succ l ih =>
      simpa [iterateThetaPlusOne_succ] using thetaPlusOnePreservesInterl
        (iterateThetaPlusOne_preserves_pf l hp)
        (iterateThetaPlusOne_preserves_pf l hq)
        (ih hp hq hpq)

end RealRooted
