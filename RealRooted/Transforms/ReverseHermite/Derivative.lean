import RealRooted.Transforms.ReverseHermite.Basic

/-!
# Derivatives of the reverse-Hermite transform

The basis derivative formula yields the heat-intertwining identity
`(H p)' = H (p') + (1 / 2) H (p'')`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Division-free derivative formula for a reverse-Hermite basis polynomial. -/
theorem reverseHermiteBasis_derivative_succ_succ
    {R : Type*} [CommSemiring R] :
    ∀ n : ℕ,
      (reverseHermiteBasis (R := R) (n + 2)).derivative =
        C ((n : R) + 2) * reverseHermiteBasis (n + 1) +
          C (((n + 2).choose 2 : ℕ) : R) * reverseHermiteBasis n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [reverseHermiteBasis_succ_succ]
      simp only [derivative_mul, derivative_X, one_mul, derivative_add,
        derivative_C, zero_mul, zero_add]
      cases n with
      | zero =>
          simp [reverseHermiteBasis, map_ofNat]
          ring
      | succ n =>
          rw [ih n (by lia)]
          cases n with
          | zero =>
              simp [reverseHermiteBasis, map_ofNat]
              ring
          | succ n =>
              rw [ih n (by lia)]
              simp only [reverseHermiteBasis_succ_succ]
              simp only [Nat.choose_succ_succ, Nat.choose_zero_right,
                Nat.choose_one_right]
              push_cast
              simp only [map_add, map_one, map_natCast, map_ofNat]
              have hchooseNat : n + 2 * n.choose 2 = n ^ 2 := by
                rw [Nat.choose_two_right, Nat.mul_comm 2,
                  Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
                cases n with
                | zero => simp
                | succ n =>
                    simp
                    ring
              have hchoose := congrArg (fun k : ℕ => (k : R[X])) hchooseNat
              push_cast at hchoose
              ring_nf
              rw [← hchoose]
              ring

/-- The derivative of a reverse-Hermite basis polynomial in the two preceding
basis elements. -/
theorem reverseHermiteBasis_derivative_two_step
    {R : Type*} [Field R] [CharZero R] :
    ∀ n : ℕ,
      (reverseHermiteBasis (R := R) (n + 2)).derivative =
        C ((n : R) + 2) * reverseHermiteBasis (n + 1) +
          C ((((n : R) + 2) * ((n : R) + 1)) / 2) *
            reverseHermiteBasis n := by
  intro n
  rw [reverseHermiteBasis_derivative_succ_succ n]
  congr 2
  rw [Nat.cast_choose_two]
  push_cast
  ring_nf

/-- Division-free heat-intertwining identity for the reverse-Hermite
transform. -/
theorem reverseHermiteTransform_derivative_cleared
    {R : Type*} [CommSemiring R] (p : R[X]) :
    C 2 * (reverseHermiteTransform p).derivative =
      C 2 * reverseHermiteTransform p.derivative +
        reverseHermiteTransform p.derivative.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [reverseHermiteTransform_add, derivative_add, mul_add, hp, hq,
        derivative_add, reverseHermiteTransform_add,
        derivative_add, reverseHermiteTransform_add]
      ring
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      rw [reverseHermiteTransform_C_mul,
        reverseHermiteTransform_X_pow]
      cases n with
      | zero =>
          simp
      | succ n =>
          cases n with
          | zero =>
              simp [reverseHermiteTransform]
          | succ n =>
              have hder1 :
                  (C a * X ^ (n + 2)).derivative =
                    C (a * ((n : R) + 2)) * X ^ (n + 1) := by
                simp only [derivative_mul, derivative_C, zero_mul, zero_add,
                  derivative_pow, derivative_X]
                push_cast
                simp only [map_add, map_ofNat, map_mul]
                ring
              have hder2 :
                  (C (a * ((n : R) + 2)) * X ^ (n + 1)).derivative =
                    C (a * ((n : R) + 2) * ((n : R) + 1)) *
                      X ^ n := by
                simp only [derivative_mul, derivative_C, zero_mul, zero_add,
                  derivative_pow, derivative_X]
                push_cast
                simp only [map_add, map_one, map_mul]
                ring
              rw [hder1, hder2,
                reverseHermiteTransform_C_mul,
                reverseHermiteTransform_X_pow,
                reverseHermiteTransform_C_mul,
                reverseHermiteTransform_X_pow]
              simp only [derivative_mul, derivative_C, zero_mul, zero_add]
              rw [reverseHermiteBasis_derivative_succ_succ]
              simp only [map_add, map_one, map_mul, map_natCast, map_ofNat]
              have hchooseNat :
                  2 * (2 + n).choose 2 = (n + 2) * (n + 1) := by
                rw [Nat.choose_two_right, Nat.mul_comm 2,
                  Nat.div_two_mul_two_of_even
                    (Nat.even_mul_pred_self (2 + n))]
                simp [Nat.add_comm]
              have hchoose :=
                congrArg (fun k : ℕ => (k : R[X])) hchooseNat
              push_cast at hchoose
              have hchooseScaled :=
                congrArg (fun q : R[X] =>
                  C a * q * reverseHermiteBasis n) hchoose
              ring_nf at hchooseScaled
              ring_nf
              rw [hchooseScaled]
              ring

/-- The reverse-Hermite transform intertwines differentiation with the heat
operator `p' + (1 / 2) p''`. -/
theorem reverseHermiteTransform_derivative
    {R : Type*} [Field R] [CharZero R] (p : R[X]) :
    (reverseHermiteTransform p).derivative =
      reverseHermiteTransform p.derivative +
        C (1 / 2 : R) *
          reverseHermiteTransform p.derivative.derivative := by
  have h := reverseHermiteTransform_derivative_cleared p
  have hC : C (1 / 2 : R) * C 2 = (1 : R[X]) := by
    rw [← C_mul]
    norm_num
  calc
    (reverseHermiteTransform p).derivative =
        (C (1 / 2 : R) * C 2) *
          (reverseHermiteTransform p).derivative := by rw [hC, one_mul]
    _ = C (1 / 2 : R) *
        (C 2 * (reverseHermiteTransform p).derivative) := by ring
    _ = C (1 / 2 : R) *
        (C 2 * reverseHermiteTransform p.derivative +
          reverseHermiteTransform p.derivative.derivative) := by rw [h]
    _ = reverseHermiteTransform p.derivative +
        C (1 / 2 : R) *
          reverseHermiteTransform p.derivative.derivative := by
      rw [mul_add, ← mul_assoc, hC, one_mul]

end RealRooted
