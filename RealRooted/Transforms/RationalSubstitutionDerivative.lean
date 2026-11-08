module

public import RealRooted.Transforms.RationalSubstitution
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.QuadraticRoot

/-!
# Derivative transport for homogeneous substitution

This file develops fixed-ambient-degree linearity and derivative identities
for `RealRooted.homogenizedSubstitution`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Homogeneous substitution is additive when the ambient degree is fixed. -/
theorem homogenizedSubstitution_add {R : Type*} [CommSemiring R]
    {N : ℕ} {A B p q : R[X]} (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    homogenizedSubstitution N A B (p + q) =
      homogenizedSubstitution N A B p + homogenizedSubstitution N A B q := by
  have hpq : (p + q).natDegree ≤ N :=
    (natDegree_add_le p q).trans (max_le hp hq)
  rw [homogenizedSubstitution_eq_sum hpq,
    homogenizedSubstitution_eq_sum hp, homogenizedSubstitution_eq_sum hq]
  simp only [coeff_add, map_add, add_mul, Finset.sum_add_distrib]

/-- Homogeneous substitution commutes with coefficient scaling at a fixed
ambient degree. -/
theorem homogenizedSubstitution_C_mul {R : Type*} [CommSemiring R]
    {N : ℕ} {A B p : R[X]} (c : R) (hp : p.natDegree ≤ N) :
    homogenizedSubstitution N A B (C c * p) =
      C c * homogenizedSubstitution N A B p := by
  have hcp : (C c * p).natDegree ≤ N :=
    (natDegree_C_mul_le c p).trans hp
  rw [homogenizedSubstitution_eq_sum hcp, homogenizedSubstitution_eq_sum hp]
  simp only [coeff_C_mul, map_mul, Finset.mul_sum]
  simp [mul_assoc]

/-- Homogeneous substitution commutes with finite sums whose summands all
fit in the fixed ambient degree. -/
theorem homogenizedSubstitution_sum {R ι : Type*} [CommSemiring R]
    {N : ℕ} {A B : R[X]} {s : Finset ι} {p : ι → R[X]}
    (hdeg : ∀ i ∈ s, (p i).natDegree ≤ N) :
    homogenizedSubstitution N A B (∑ i ∈ s, p i) =
      ∑ i ∈ s, homogenizedSubstitution N A B (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [homogenizedSubstitution_eq_sum (by simp)]
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        homogenizedSubstitution_add (hdeg i (Finset.mem_insert_self i s))]
      · exact congrArg (homogenizedSubstitution N A B (p i) + ·)
          (ih fun j hj ↦ hdeg j (Finset.mem_insert_of_mem hj))
      · exact natDegree_sum_le_of_forall_le s p fun j hj ↦
          hdeg j (Finset.mem_insert_of_mem hj)

/-- Raising the ambient degree pads homogeneous substitution by a power of
the denominator polynomial. -/
theorem homogenizedSubstitution_eq_pow_mul {R : Type*} [CommSemiring R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) :
    homogenizedSubstitution N A B p =
      B ^ (N - p.natDegree) * rationalSubstitution A B p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdeg
  induction m with
  | zero =>
      rw [Nat.add_zero, Nat.sub_self, pow_zero, one_mul,
        rationalSubstitution_eq_sum, homogenizedSubstitution_eq_sum le_rfl]
  | succ m ih =>
      rw [Nat.add_succ, homogenizedSubstitution_succ]
      · rw [ih (Nat.le_add_right p.natDegree m)]
        simp only [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_sub_cancel_left, pow_succ]
        ac_rfl
      · exact Nat.le_add_right p.natDegree m

/-- The polynomial `A' B - A B'` governing derivative transport. -/
def substitutionWronskian {R : Type*} [CommRing R] (A B : R[X]) : R[X] :=
  A.derivative * B - A * B.derivative

/-- Homogeneous substitution sends zero to zero. -/
@[simp]
theorem homogenizedSubstitution_zero {R : Type*} [CommSemiring R]
    (N : ℕ) (A B : R[X]) :
    homogenizedSubstitution N A B 0 = 0 := by
  rw [homogenizedSubstitution_eq_sum (by simp)]
  simp

/-- Homogeneous substitution sends a source monomial to the corresponding
homogeneous monomial. -/
theorem homogenizedSubstitution_C_mul_X_pow {R : Type*} [CommSemiring R]
    {N k : ℕ} (A B : R[X]) (c : R) (hk : k ≤ N) :
    homogenizedSubstitution N A B (C c * X ^ k) =
      C c * A ^ k * B ^ (N - k) := by
  rw [homogenizedSubstitution_eq_sum
    ((natDegree_C_mul_le c (X ^ k)).trans (natDegree_X_pow_le k |>.trans hk))]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [coeff_C_mul, coeff_X_pow, hjk]
  · exact fun hk' ↦ (hk' (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim

private theorem homogenizedSubstitution_firstDerivative_monomial
    {R : Type*} [CommRing R] {N k : ℕ} (A B : R[X]) (c : R)
    (hk : k ≤ N) :
    B ^ 2 * (homogenizedSubstitution N A B (C c * X ^ k)).derivative =
      C (N : R) * B * B.derivative *
          homogenizedSubstitution N A B (C c * X ^ k) +
        substitutionWronskian A B *
          homogenizedSubstitution N A B (C c * X ^ k).derivative := by
  cases k with
  | zero =>
      rw [homogenizedSubstitution_C_mul_X_pow A B c hk,
        derivative_C_mul_X_pow]
      simp only [pow_zero, mul_one, Nat.sub_zero, Nat.cast_zero, mul_zero,
        C_0, zero_mul, homogenizedSubstitution_zero, add_zero]
      cases N with
      | zero => simp
      | succ N =>
          rw [derivative_mul, derivative_C, derivative_pow]
          simp only [zero_mul, zero_add, Nat.succ_sub_one, Nat.cast_succ]
          rw [pow_succ]
          ring
  | succ k =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [homogenizedSubstitution_C_mul_X_pow A B c
          (Nat.le_add_right (k + 1) m),
        derivative_C_mul_X_pow]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [homogenizedSubstitution_C_mul_X_pow A B (c * (k + 1))]
      · rw [Nat.add_sub_cancel_left]
        have hsub : k + 1 + m - k = m + 1 := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm]
        rw [hsub]
        cases m with
        | zero =>
            simp [substitutionWronskian, derivative_mul, derivative_pow]
            ring
        | succ m =>
            simp only [derivative_mul, derivative_C, zero_mul, zero_add,
              derivative_pow, Nat.cast_add, Nat.cast_one,
              Nat.succ_sub_one]
            simp only [pow_succ]
            simp [substitutionWronskian]
            ring
      · rw [Nat.add_assoc]
        exact Nat.le_add_right k (1 + m)

/-- First derivatives pass through homogeneous substitution according to the
polynomial chain rule, without division by the denominator. -/
theorem homogenizedSubstitution_firstDerivative {R : Type*} [CommRing R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) :
    B ^ 2 * (homogenizedSubstitution N A B p).derivative =
      C (N : R) * B * B.derivative * homogenizedSubstitution N A B p +
        substitutionWronskian A B *
          homogenizedSubstitution N A B p.derivative := by
  let f : ℕ → R[X] := fun k ↦ C (p.coeff k) * X ^ k
  have hfdeg : ∀ k ∈ Finset.range (N + 1), (f k).natDegree ≤ N := by
    intro k hk
    exact (natDegree_C_mul_le _ _).trans <|
      (natDegree_X_pow_le k).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hdfdeg : ∀ k ∈ Finset.range (N + 1), (f k).derivative.natDegree ≤ N := by
    intro k hk
    exact (natDegree_derivative_le _).trans <|
      (Nat.sub_le _ _).trans (hfdeg k hk)
  have hp_sum : p = ∑ k ∈ Finset.range (N + 1), f k := by
    dsimp only [f]
    exact p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hdeg)
  rw [hp_sum]
  rw [homogenizedSubstitution_sum hfdeg, derivative_sum, derivative_sum,
    homogenizedSubstitution_sum hdfdeg]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k hk ↦
    homogenizedSubstitution_firstDerivative_monomial A B (p.coeff k)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- The coefficient triangle for higher derivative transport. Coefficients
outside the triangle are represented by zero. -/
def derivativeTransportCoeff {R : Type*} [CommRing R]
    (N : ℕ) (A B : R[X]) : ℕ → ℕ → R[X]
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | r + 1, 0 =>
      B ^ 2 * (derivativeTransportCoeff N A B r 0).derivative +
        C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
          derivativeTransportCoeff N A B r 0
  | r + 1, j + 1 =>
      B ^ 2 * (derivativeTransportCoeff N A B r (j + 1)).derivative +
        C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
          derivativeTransportCoeff N A B r (j + 1) +
        substitutionWronskian A B * derivativeTransportCoeff N A B r j

/-- The initial row of the derivative-transport triangle. -/
@[simp]
theorem derivativeTransportCoeff_zero {R : Type*} [CommRing R]
    (N : ℕ) (A B : R[X]) (j : ℕ) :
    derivativeTransportCoeff N A B 0 j = if j = 0 then 1 else 0 := by
  cases j <;> simp [derivativeTransportCoeff]

/-- The left-edge instance of the coefficient-triangle recursion. -/
theorem derivativeTransportCoeff_succ_zero {R : Type*} [CommRing R]
    (N r : ℕ) (A B : R[X]) :
    derivativeTransportCoeff N A B (r + 1) 0 =
      B ^ 2 * (derivativeTransportCoeff N A B r 0).derivative +
        C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
          derivativeTransportCoeff N A B r 0 := by
  rfl

/-- The positive-index instance of the coefficient-triangle recursion. -/
theorem derivativeTransportCoeff_succ_succ {R : Type*} [CommRing R]
    (N r j : ℕ) (A B : R[X]) :
    derivativeTransportCoeff N A B (r + 1) (j + 1) =
      B ^ 2 * (derivativeTransportCoeff N A B r (j + 1)).derivative +
        C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
          derivativeTransportCoeff N A B r (j + 1) +
        substitutionWronskian A B * derivativeTransportCoeff N A B r j := by
  rfl

/-- Coefficients strictly above the derivative-transport triangle vanish. -/
theorem derivativeTransportCoeff_eq_zero_of_lt {R : Type*} [CommRing R]
    (N : ℕ) (A B : R[X]) {r j : ℕ} (hrj : r < j) :
    derivativeTransportCoeff N A B r j = 0 := by
  induction r generalizing j with
  | zero =>
      cases j with
      | zero => exact (Nat.not_lt_zero 0 hrj).elim
      | succ j => rfl
  | succ r ih =>
      cases j with
      | zero => exact (Nat.not_lt_zero (r + 1) hrj).elim
      | succ j =>
          rw [derivativeTransportCoeff_succ_succ]
          have hrj' : r < j := Nat.succ_lt_succ_iff.mp hrj
          rw [ih hrj', ih (hrj'.trans (Nat.lt_succ_self j))]
          simp

/-- The diagonal coefficient is the corresponding power of the substitution
Wronskian. -/
theorem derivativeTransportCoeff_diagonal {R : Type*} [CommRing R]
    (N r : ℕ) (A B : R[X]) :
    derivativeTransportCoeff N A B r r = substitutionWronskian A B ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [derivativeTransportCoeff_succ_succ,
        derivativeTransportCoeff_eq_zero_of_lt N A B (Nat.lt_succ_self r), ih]
      simp [pow_succ, mul_comm]

private theorem scaled_iterateDerivative_succ {R : Type*} [CommRing R]
    (B q : R[X]) (r : ℕ) :
    B ^ (2 * (r + 1)) * derivative^[r + 1] q =
      B ^ 2 * (B ^ (2 * r) * derivative^[r] q).derivative -
        C (2 * r : R) * B * B.derivative *
          (B ^ (2 * r) * derivative^[r] q) := by
  cases r with
  | zero => simp
  | succ r =>
      simp only [Function.iterate_succ_apply', derivative_mul, derivative_pow]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp [Nat.mul_succ, pow_add]
      ring

private theorem derivativeTransport_term {R : Type*} [CommRing R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) (r j : ℕ) :
    B ^ 2 *
          (derivativeTransportCoeff N A B r j *
            homogenizedSubstitution N A B (derivative^[j] p)).derivative -
        C (2 * r : R) * B * B.derivative *
          (derivativeTransportCoeff N A B r j *
            homogenizedSubstitution N A B (derivative^[j] p)) =
      (B ^ 2 * (derivativeTransportCoeff N A B r j).derivative +
          C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
            derivativeTransportCoeff N A B r j) *
          homogenizedSubstitution N A B (derivative^[j] p) +
        substitutionWronskian A B * derivativeTransportCoeff N A B r j *
          homogenizedSubstitution N A B (derivative^[j + 1] p) := by
  have hjdeg : (derivative^[j] p).natDegree ≤ N :=
    (natDegree_iterate_derivative p j).trans ((Nat.sub_le _ _).trans hdeg)
  have hfirst := homogenizedSubstitution_firstDerivative (A := A) (B := B) hjdeg
  rw [Function.iterate_succ_apply']
  calc
    B ^ 2 *
          (derivativeTransportCoeff N A B r j *
            homogenizedSubstitution N A B (derivative^[j] p)).derivative -
        C (2 * r : R) * B * B.derivative *
          (derivativeTransportCoeff N A B r j *
            homogenizedSubstitution N A B (derivative^[j] p)) =
      (derivativeTransportCoeff N A B r j).derivative *
          (B ^ 2 * homogenizedSubstitution N A B (derivative^[j] p)) +
        derivativeTransportCoeff N A B r j *
          (B ^ 2 *
            (homogenizedSubstitution N A B (derivative^[j] p)).derivative) -
        C (2 * r : R) * B * B.derivative *
          derivativeTransportCoeff N A B r j *
          homogenizedSubstitution N A B (derivative^[j] p) := by
            rw [derivative_mul]
            ring
    _ = _ := by
      rw [hfirst]
      simp only [map_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem derivativeTransport_sum_succ {R : Type*} [CommRing R]
    (N r : ℕ) (A B : R[X]) (H : ℕ → R[X]) :
    ∑ j ∈ Finset.range (r + 1),
        ((B ^ 2 * (derivativeTransportCoeff N A B r j).derivative +
              C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
                derivativeTransportCoeff N A B r j) * H j +
          substitutionWronskian A B * derivativeTransportCoeff N A B r j *
            H (j + 1)) =
      ∑ j ∈ Finset.range (r + 2),
        derivativeTransportCoeff N A B (r + 1) j * H j := by
  let D : ℕ → R[X] := fun j ↦
    B ^ 2 * (derivativeTransportCoeff N A B r j).derivative +
      C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
        derivativeTransportCoeff N A B r j
  have hDlast : D (r + 1) = 0 := by
    dsimp only [D]
    rw [derivativeTransportCoeff_eq_zero_of_lt N A B (Nat.lt_succ_self r)]
    simp
  have hDsum :
      (∑ j ∈ Finset.range (r + 1), D (j + 1) * H (j + 1)) =
        ∑ j ∈ Finset.range r, D (j + 1) * H (j + 1) := by
    rw [Finset.sum_range_succ, hDlast]
    simp
  have hnextSum :
      (∑ j ∈ Finset.range (r + 2),
          derivativeTransportCoeff N A B (r + 1) j * H j) =
        derivativeTransportCoeff N A B (r + 1) 0 * H 0 +
          ∑ j ∈ Finset.range (r + 1),
            derivativeTransportCoeff N A B (r + 1) (j + 1) * H (j + 1) := by
    rw [show r + 2 = (r + 1) + 1 by ring, Finset.sum_range_succ']
    abel
  change
    ∑ j ∈ Finset.range (r + 1),
        (D j * H j + substitutionWronskian A B *
          derivativeTransportCoeff N A B r j * H (j + 1)) = _
  calc
    ∑ j ∈ Finset.range (r + 1),
        (D j * H j + substitutionWronskian A B *
          derivativeTransportCoeff N A B r j * H (j + 1)) =
      (∑ j ∈ Finset.range (r + 1), D j * H j) +
        ∑ j ∈ Finset.range (r + 1),
          substitutionWronskian A B * derivativeTransportCoeff N A B r j *
            H (j + 1) := by
              rw [Finset.sum_add_distrib]
    _ = D 0 * H 0 +
        ∑ j ∈ Finset.range (r + 1),
          (D (j + 1) * H (j + 1) + substitutionWronskian A B *
            derivativeTransportCoeff N A B r j * H (j + 1)) := by
              rw [Finset.sum_add_distrib, Finset.sum_range_succ', hDsum]
              abel
    _ = ∑ j ∈ Finset.range (r + 2),
        derivativeTransportCoeff N A B (r + 1) j * H j := by
      rw [hnextSum]
      rw [derivativeTransportCoeff_succ_zero]
      change D 0 * H 0 + _ = D 0 * H 0 + _
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [derivativeTransportCoeff_succ_succ]
      dsimp only [D]
      ring

/-- Every iterated derivative of homogeneous substitution is a triangular
linear combination of substitutions of source derivatives. -/
theorem homogenizedSubstitution_iterateDerivative {R : Type*} [CommRing R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) (r : ℕ) :
    B ^ (2 * r) * derivative^[r] (homogenizedSubstitution N A B p) =
      ∑ j ∈ Finset.range (r + 1),
        derivativeTransportCoeff N A B r j *
          homogenizedSubstitution N A B (derivative^[j] p) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [scaled_iterateDerivative_succ, ih, derivative_sum]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      calc
        ∑ j ∈ Finset.range (r + 1),
            (B ^ 2 *
                (derivativeTransportCoeff N A B r j *
                  homogenizedSubstitution N A B (derivative^[j] p)).derivative -
              C (2 * r : R) * B * B.derivative *
                (derivativeTransportCoeff N A B r j *
                  homogenizedSubstitution N A B (derivative^[j] p))) =
          ∑ j ∈ Finset.range (r + 1),
            ((B ^ 2 * (derivativeTransportCoeff N A B r j).derivative +
                  C ((N : R) - (2 * r : ℕ)) * B * B.derivative *
                    derivativeTransportCoeff N A B r j) *
                homogenizedSubstitution N A B (derivative^[j] p) +
              substitutionWronskian A B * derivativeTransportCoeff N A B r j *
                homogenizedSubstitution N A B (derivative^[j + 1] p)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact derivativeTransport_term hdeg r j
        _ = ∑ j ∈ Finset.range (r + 2),
            derivativeTransportCoeff N A B (r + 1) j *
              homogenizedSubstitution N A B (derivative^[j] p) :=
          derivativeTransport_sum_succ N r A B fun j ↦
            homogenizedSubstitution N A B (derivative^[j] p)

private theorem derivativeTransportCoeff_two_zero {R : Type*} [CommRing R]
    (N : ℕ) (A B : R[X]) :
    derivativeTransportCoeff N A B 2 0 =
      C ((N : R) * ((N : R) - 1)) * B ^ 2 * B.derivative ^ 2 +
        C (N : R) * B ^ 3 * B.derivative.derivative := by
  simp [derivativeTransportCoeff, derivative_mul, pow_two,
    map_ofNat (C : R →+* R[X]) 2]
  ring

private theorem derivativeTransportCoeff_two_one {R : Type*} [CommRing R]
    (N : ℕ) (A B : R[X]) :
    derivativeTransportCoeff N A B 2 1 =
      B ^ 2 * (substitutionWronskian A B).derivative +
        C (2 * ((N : R) - 1)) * B * B.derivative *
          substitutionWronskian A B := by
  simp [derivativeTransportCoeff, map_ofNat (C : R →+* R[X]) 2]
  ring

private theorem derivativeTransportCoeff_two_two {R : Type*} [CommRing R]
    (N : ℕ) (A B : R[X]) :
    derivativeTransportCoeff N A B 2 2 = substitutionWronskian A B ^ 2 := by
  exact derivativeTransportCoeff_diagonal N 2 A B

/-- The order-two derivative transport identity in explicit form. -/
theorem homogenizedSubstitution_secondDerivative {R : Type*} [CommRing R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) :
    B ^ 4 * (homogenizedSubstitution N A B p).derivative.derivative =
      (C ((N : R) * ((N : R) - 1)) * B ^ 2 * B.derivative ^ 2 +
          C (N : R) * B ^ 3 * B.derivative.derivative) *
          homogenizedSubstitution N A B p +
        (B ^ 2 * (substitutionWronskian A B).derivative +
          C (2 * ((N : R) - 1)) * B * B.derivative *
            substitutionWronskian A B) *
          homogenizedSubstitution N A B p.derivative +
        substitutionWronskian A B ^ 2 *
          homogenizedSubstitution N A B p.derivative.derivative := by
  have h := homogenizedSubstitution_iterateDerivative (A := A) (B := B) hdeg 2
  simp only [show 2 * 2 = 4 by decide, Function.iterate_succ_apply',
    Function.iterate_zero_apply, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add] at h
  rw [derivativeTransportCoeff_two_zero,
    derivativeTransportCoeff_two_one, derivativeTransportCoeff_two_two] at h
  simpa [add_assoc] using h

/-- The natural-degree Dickson substitution with parameter `a`. -/
def dicksonSubstitution (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  rationalSubstitution (X ^ 2 + C a) X p

/-- A Dickson fiber splits precisely when its discriminant is nonnegative. -/
theorem dickson_fiber_splits_iff (a r : ℝ) :
    (X ^ 2 + C a - C r * X : ℝ[X]).Splits ↔ 4 * a ≤ r ^ 2 := by
  rw [show (X ^ 2 + C a - C r * X : ℝ[X]) =
      X ^ 2 + C (-r) * X + C a by simp only [map_neg]; ring,
    monicQuadraticPoly_splits_iff_discrim_nonneg]
  constructor <;> intro h <;> linarith

private theorem dickson_isCoprime (a : ℝ) (ha : a ≠ 0) :
    IsCoprime (X ^ 2 + C a : ℝ[X]) X := by
  apply IsCoprime.symm
  rw [show (X : ℝ[X]) = X - C 0 by simp,
    (irreducible_X_sub_C 0).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
  simp [ha]

/-- The quotient `(X² + a) / X` is nonconstant. -/
theorem dickson_hasNonconstantRatio (a : ℝ) :
    HasNonconstantRatio (X ^ 2 + C a) X := by
  rw [hasNonconstantRatio_iff]
  intro z hzero
  have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 2) hzero
  norm_num at hcoeff

/-- The Dickson substitution splits exactly when every source root lies
outside the open discriminant interval. -/
theorem dicksonSubstitution_splits_iff {a : ℝ} (ha : a ≠ 0)
    {p : ℝ[X]} (hp : p ≠ 0) :
    (dicksonSubstitution a p).Splits ↔
      p.Splits ∧ ∀ r ∈ p.roots, 4 * a ≤ r ^ 2 := by
  rw [dicksonSubstitution,
    rationalSubstitution_splits_iff hp Polynomial.X_ne_zero
      (dickson_isCoprime a ha) (dickson_hasNonconstantRatio a)]
  apply and_congr_right
  intro hpSplits
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  exact dickson_fiber_splits_iff a r

/-- The Dickson root criterion remains valid at every larger ambient degree;
the extra factor is a power of `X`. -/
theorem homogenizedSubstitution_dickson_splits_iff {N : ℕ} {a : ℝ}
    (ha : a ≠ 0) {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ N) :
    (homogenizedSubstitution N (X ^ 2 + C a) X p).Splits ↔
      p.Splits ∧ ∀ r ∈ p.roots, 4 * a ≤ r ^ 2 := by
  rw [homogenizedSubstitution_eq_pow_mul hdeg]
  rw [Polynomial.splits_mul_iff_right (pow_ne_zero _ Polynomial.X_ne_zero)
    (Polynomial.Splits.X.pow _)]
  exact dicksonSubstitution_splits_iff ha hp

/-- First-derivative transport for the Dickson substitution. -/
theorem homogenizedSubstitution_dickson_firstDerivative {N : ℕ}
    {a : ℝ} {p : ℝ[X]} (hdeg : p.natDegree ≤ N) :
    X ^ 2 * (homogenizedSubstitution N (X ^ 2 + C a) X p).derivative =
      C (N : ℝ) * X * homogenizedSubstitution N (X ^ 2 + C a) X p +
        (X ^ 2 - C a) *
          homogenizedSubstitution N (X ^ 2 + C a) X p.derivative := by
  have hW : substitutionWronskian (X ^ 2 + C a) X = X ^ 2 - C a := by
    simp only [substitutionWronskian, derivative_add, derivative_pow,
      derivative_X, derivative_C]
    rw [C_eq_natCast]
    ring
  rw [← hW]
  simpa using (homogenizedSubstitution_firstDerivative
    (A := X ^ 2 + C a) (B := X) hdeg)

end RealRooted
