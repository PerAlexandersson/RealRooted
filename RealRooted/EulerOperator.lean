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

The coefficient and nonnegative-coefficient lemmas below are proved directly.
The real-rootedness and proper-position preservation results are stated inline
on each theorem, since their proofs are the classical Rolle/polar derivative
input for the later formalization.
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

@[simp] theorem coeff_theta (p : ℝ[X]) (n : ℕ) :
    (theta p).coeff n = (n : ℝ) * p.coeff n := by
  cases n with
  | zero =>
      simp [theta]
  | succ n =>
      rw [theta, coeff_X_mul, coeff_derivative]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

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

/-- Classical Rolle input: `theta` preserves the polynomial PF cone, obtained
from the real-rootedness and nonpositive-root preservation hypothesis. -/
theorem thetaPreservesPF_of_realRootedOrZero
    (hθ : ∀ {p : ℝ[X]},
      IsPFPolynomial p →
      (theta p = 0 ∨ (theta p).Splits) ∧ ∀ r ∈ (theta p).roots, r ≤ 0) :
    ∀ {p : ℝ[X]}, IsPFPolynomial p → IsPFPolynomial (theta p) :=
  fun {_} hp => ⟨hp.hasNonnegCoeffs.theta, (hθ hp).1, (hθ hp).2⟩

theorem thetaPlusOnePreservesPF_of_realRootedOrZero
    (hθ : ∀ {p : ℝ[X]},
      IsPFPolynomial p →
      (thetaPlusOne p = 0 ∨ (thetaPlusOne p).Splits) ∧
        ∀ r ∈ (thetaPlusOne p).roots, r ≤ 0) :
    ∀ {p : ℝ[X]}, IsPFPolynomial p → IsPFPolynomial (thetaPlusOne p) :=
  fun {_} hp => ⟨hp.hasNonnegCoeffs.thetaPlusOne, (hθ hp).1, (hθ hp).2⟩

/-- `theta + 1` preserves the polynomial PF cone. -/
theorem thetaPlusOne_preserves_pf {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (thetaPlusOne p) := by
  simpa [thetaPlusOne_eq_derivative_X_mul] using hp.X_mul.derivative

theorem thetaPlusOnePreservesPrec0_of_derivative {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Prec0 p q) :
    Prec0 (thetaPlusOne p) (thetaPlusOne q) := by
  simpa [thetaPlusOne_eq_derivative_X_mul] using
    derivativePreservesPrec0 (prec0_X_mul_both_of_pf hp hq hpq)

/-- `theta + 1` preserves weak proper position on the polynomial PF cone,
obtained from the derivative preservation theorem via
`thetaPlusOnePreservesPrec0_of_derivative`. -/
theorem thetaPlusOnePreservesPrec0 {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Prec0 p q) :
    Prec0 (thetaPlusOne p) (thetaPlusOne q) :=
  thetaPlusOnePreservesPrec0_of_derivative hp hq hpq

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
          exact Nat.lt_succ_of_le hNk
    have hrhs_coeff :
        p.coeff (Polynomial.revAt N (Polynomial.revAt (N - 1) k + 1)) = 0 := by
      rw [Polynomial.revAt_eq_self_of_lt hidx]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hidx)
    rw [hrhs_coeff]
    simp
    by_cases hkN : k = N
    · subst k
      simp
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
  have hder_deg : (reciprocalShift N p).derivative.natDegree ≤ N - 1 :=
    (Polynomial.natDegree_derivative_le (reciprocalShift N p)).trans
      (Nat.sub_le_sub_right hdeg_shift 1)
  exact reciprocalShift_preserves_pf hshift.derivative hder_deg

theorem polarThetaPreservesPF_of_realRootedOrZero
    (hNθ : ∀ {N : ℕ} {p : ℝ[X]},
      IsPFPolynomial p →
      p.natDegree ≤ N →
      (polarTheta N p = 0 ∨ (polarTheta N p).Splits) ∧
        ∀ r ∈ (polarTheta N p).roots, r ≤ 0) :
    ∀ {N : ℕ} {p : ℝ[X]},
      IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (polarTheta N p) :=
  fun {_ _} hp hdeg =>
    ⟨hp.hasNonnegCoeffs.polarTheta hdeg, (hNθ hp hdeg).1, (hNθ hp hdeg).2⟩

theorem iterateThetaPlusOne_preserves_pf
    (l : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (iterateThetaPlusOne l p) := by
  induction l generalizing p with
  | zero =>
      simpa using hp
  | succ l ih =>
      simpa [iterateThetaPlusOne_succ] using thetaPlusOne_preserves_pf (ih hp)

theorem iterateThetaPlusOne_preserves_prec0
    (l : ℕ) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Prec0 p q) :
    Prec0 (iterateThetaPlusOne l p) (iterateThetaPlusOne l q) := by
  induction l generalizing p q with
  | zero =>
      simpa using hpq
  | succ l ih =>
      simpa [iterateThetaPlusOne_succ] using thetaPlusOnePreservesPrec0
        (iterateThetaPlusOne_preserves_pf l hp)
        (iterateThetaPlusOne_preserves_pf l hq)
        (ih hp hq hpq)

end RealRooted
