module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Derivation.Basic

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-!
# The Euler operator on formal power series

This file develops the formal-power-series operator `X d/dX`.  Its coefficient
formula and its iterates provide the general coefficient-extraction step from
Euler differential equations to polynomial recurrences.
-/

public section

noncomputable section

namespace RealRooted

/-- A derivation shifted by a scalar from its base ring. -/
def derivationShift {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (c : R) (f : A) : A :=
  D f - algebraMap R A c * f

/-- Differentiating `M * F = N` shifts the derivative on `N` when `M` is an
eigenvector of the derivation. -/
theorem mul_derivation_eq_derivationShift_of_mul_eq
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (c : R) {M F N : A}
    (hM : D M = algebraMap R A c * M) (hN : M * F = N) :
    M * D F = derivationShift D c N := by
  have hDN := congrArg D hN
  rw [D.leibniz, hM] at hDN
  simp only [smul_eq_mul] at hDN
  rw [derivationShift, ← hDN]
  rw [← hN]
  ring

/-- Repeated differentiation across an eigenvector denominator becomes
repeated shifted differentiation of the numerator. -/
theorem mul_iterate_derivation_eq_iterate_derivationShift_of_mul_eq
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (c : R) {M F N : A}
    (hM : D M = algebraMap R A c * M) (hN : M * F = N) (k : ℕ) :
    M * (D^[k]) F = ((derivationShift D c)^[k]) N := by
  induction k with
  | zero => simpa using hN
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact mul_derivation_eq_derivationShift_of_mul_eq D c hM ih

/-- A second-order differential equation follows from its shifted numerator
identity after clearing a nonzero eigenvector denominator. -/
theorem secondOrder_differential_eq_of_shifted_numerator_eq
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsDomain A]
    (D : Derivation R A A) (c : R) {M F N : A} (hM0 : M ≠ 0)
    (hM : D M = algebraMap R A c * M) (hN : M * F = N)
    (a b w q : A)
    (hnum :
      a * ((derivationShift D c)^[2]) N +
          b * derivationShift D c N + w * N = q * M) :
    a * (D^[2]) F + b * D F + w * F = q := by
  apply mul_left_cancel₀ hM0
  calc
    M * (a * (D^[2]) F + b * D F + w * F) =
        a * (M * (D^[2]) F) + b * (M * D F) + w * (M * F) := by ring
    _ = a * ((derivationShift D c)^[2]) N +
        b * derivationShift D c N + w * N := by
      rw [mul_iterate_derivation_eq_iterate_derivationShift_of_mul_eq D c hM hN,
        mul_derivation_eq_derivationShift_of_mul_eq D c hM hN, hN]
    _ = q * M := hnum
    _ = M * q := mul_comm _ _

/-- A square-root numerator satisfies a homogeneous second-order equation when
its two polynomial certificate identities hold.  This is the abstract
algebraic-extension step behind reducing a quadratic generating function to an
Euler differential equation. -/
theorem secondOrder_derivation_eq_zero_of_square
    {A : Type*} [Field A] [CharZero A] [Algebra ℚ A] (D : Derivation ℚ A A)
    {s delta K V W R : A} (hsq : s * s = delta)
    (hV : 2 * V = 6 * delta + D delta)
    (hR : R = 2 * delta * derivationShift D 4 K + K * D delta)
    (hhom : D R - R + 2 * W * K = 0) :
    delta * ((derivationShift D 4)^[2]) (K * s) +
        V * derivationShift D 4 (K * s) + W * (K * s) = 0 := by
  let Q := derivationShift D 4 (K * s)
  have hDs : 2 * s * D s = D delta := by
    have h := congrArg D hsq
    rw [D.leibniz] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have hQ : 2 * s * Q = R := by
    rw [hR]
    dsimp only [Q, derivationShift]
    simp only [D.leibniz, smul_eq_mul, map_ofNat]
    rw [← hDs, ← hsq]
    ring
  have hDQ : 2 * s * D Q + 2 * Q * D s = D R := by
    have h := congrArg D hQ
    simp only [D.leibniz, smul_eq_mul] at h
    have hD2 : D (2 : A) = 0 := D.map_natCast 2
    simp only [hD2, mul_zero, add_zero] at h
    linear_combination h
  have hhom' : 2 * s * D Q + 2 * Q * D s - 2 * s * Q + 2 * W * K = 0 := by
    rw [hDQ, hQ]
    exact hhom
  change delta * derivationShift D 4 Q + V * Q + W * (K * s) = 0
  rw [derivationShift]
  norm_num
  have htwo :
      2 * (delta * (D Q - 4 * Q) + V * Q + W * (K * s)) = 0 := by
    linear_combination s * hhom' + Q * hV - Q * hDs -
      2 * (D Q - Q) * hsq
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- Shifted derivation commutes with subtraction. -/
private theorem derivationShift_sub
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (c : R) (f g : A) :
    derivationShift D c (f - g) = derivationShift D c f - derivationShift D c g := by
  simp only [derivationShift, D.map_sub]
  ring

/-- Every iterate of a shifted derivation commutes with subtraction. -/
private theorem iterate_derivationShift_sub
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (c : R) (k : ℕ) (f g : A) :
    ((derivationShift D c)^[k]) (f - g) =
      ((derivationShift D c)^[k]) f - ((derivationShift D c)^[k]) g := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, derivationShift_sub]

/-- The square-root and rational polynomial certificates imply the
second-order differential equation for a quotient with an Euler eigenvector
denominator. -/
theorem secondOrder_differential_eq_of_square_numerator
    {A : Type*} [Field A] [CharZero A] [Algebra ℚ A]
    (D : Derivation ℚ A A) {F H K M s delta V W R q : A}
    (hM0 : M ≠ 0) (hM : D M = 4 * M) (hF : M * F = H - K * s)
    (hsq : s * s = delta) (hV : 2 * V = 6 * delta + D delta)
    (hR : R = 2 * delta * derivationShift D 4 K + K * D delta)
    (hH : delta * ((derivationShift D 4)^[2]) H +
      V * derivationShift D 4 H + W * H + q * M = 0)
    (hhom : D R - R + 2 * W * K = 0) :
    delta * (D^[2]) F + V * D F + W * F = -q := by
  have hKs := secondOrder_derivation_eq_zero_of_square D hsq hV hR hhom
  have hnum :
      delta * ((derivationShift D 4)^[2]) (H - K * s) +
          V * derivationShift D 4 (H - K * s) + W * (H - K * s) =
        -q * M := by
    rw [iterate_derivationShift_sub, derivationShift_sub]
    linear_combination hH - hKs
  apply secondOrder_differential_eq_of_shifted_numerator_eq
    D 4 hM0 (by simpa using hM) hF delta V W (-q)
  exact hnum

/-- The Euler operator `X d/dX` on formal power series. -/
def powerSeriesEuler {R : Type*} [CommSemiring R]
    (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.X * PowerSeries.derivative f

/-- The Euler operator multiplies the coefficient of degree `n` by `n`. -/
@[simp] theorem coeff_powerSeriesEuler {R : Type*} [CommSemiring R]
    (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesEuler f) = (n : R) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [powerSeriesEuler]
  | succ n =>
      rw [powerSeriesEuler, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative]
      push_cast
      ring

/-- Iterating the Euler operator multiplies the coefficient of degree `n` by
`n ^ k`. -/
@[simp] theorem coeff_powerSeriesEuler_iterate {R : Type*} [CommSemiring R]
    (f : PowerSeries R) (k n : ℕ) :
    PowerSeries.coeff n ((powerSeriesEuler^[k]) f) =
      (n : R) ^ k * PowerSeries.coeff n f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', coeff_powerSeriesEuler, ih, pow_succ]
      ring

/-- Multiplying an iterated Euler derivative by a polynomial gives the
coefficient convolution used to extract recurrences from Euler differential
equations. -/
theorem coeff_coe_mul_powerSeriesEuler_iterate
    {R : Type*} [CommSemiring R] (p : Polynomial R)
    (f : PowerSeries R) (k n : ℕ) :
    PowerSeries.coeff n
        ((p : PowerSeries R) * (powerSeriesEuler^[k]) f) =
      ∑ ij ∈ Finset.antidiagonal n,
        p.coeff ij.1 * (ij.2 : R) ^ k * PowerSeries.coeff ij.2 f := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [mul_assoc]

end RealRooted
