import RealRooted.ParkingFunctions.ToricContribution.TriangleInvariant

/-!
# Differential algebra for the toric-contribution triangle

The terminating coefficient formula for `J` satisfies its hypergeometric
differential equation.  Differentiating that equation gives the vertical edge
of every Darboux square in the finite-offset triangle.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

theorem jCoeff_succ_mul (m ε k : ℕ) :
    ((ε : ℝ) + 2 + k) * (k + 1) * jCoeff m ε (k + 1) =
      (1 - (m : ℝ) + k) * ((m : ℝ) + 2 + ε + k) * jCoeff m ε k := by
  simp only [jCoeff]
  rw [realRisingFactorial_succ, realRisingFactorial_succ,
    realRisingFactorial_succ, Nat.factorial_succ]
  have hC : 0 < realRisingFactorial ((ε : ℝ) + 2) k := by
    apply realRisingFactorial_pos
    positivity
  have hk : 0 < (k.factorial : ℝ) := by positivity
  have hsucc : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [hC.ne', hk.ne', hsucc.ne']

/-- Differentiating an insertion operator shifts both parameters and contributes
the scalar correction `-b`. -/
theorem derivative_insertionOperator (a b : ℝ) (f : ℝ[X]) :
    (insertionOperator a b f).derivative =
      insertionOperator (a + 1) (b + 2) f.derivative - C b * f := by
  simp only [insertionOperator, intervalWeight, derivative_sub,
    derivative_mul, derivative_C, derivative_X, derivative_one, zero_mul,
    one_mul, map_add, map_one, map_ofNat]
  ring

theorem insertionOperator_add (a b : ℝ) (f g : ℝ[X]) :
    insertionOperator a b (f + g) =
      insertionOperator a b f + insertionOperator a b g := by
  simp only [insertionOperator, derivative_add]
  ring

/-- Shifting both insertion parameters by the same scalar adds a multiple of
`(1-X)f`. -/
theorem insertionOperator_add_parameters (a b s : ℝ) (f : ℝ[X]) :
    insertionOperator (a + s) (b + s) f =
      insertionOperator a b f + C s * (1 - X) * f := by
  simp only [insertionOperator, map_add]
  ring

@[simp]
theorem insertionOperator_zero (a b : ℝ) :
    insertionOperator a b 0 = 0 := by
  simp only [insertionOperator, derivative_zero, mul_zero, add_zero]

/-- Every derivative of an eigenfunction of an insertion operator is again an
eigenfunction, with shifted parameters and the accumulated scalar correction. -/
theorem iteratedDerivative_differentialEquation
    (f : ℝ[X]) (a b eigenvalue : ℝ)
    (hbase : C eigenvalue * f + insertionOperator a b f.derivative = 0) :
    ∀ d : ℕ,
      C (eigenvalue - d * (b + d - 1)) * (derivative^[d]) f +
        insertionOperator (a + d) (b + 2 * d) ((derivative^[d + 1]) f) = 0
  | 0 => by simpa using hbase
  | d + 1 => by
      have hder := congrArg derivative
        (iteratedDerivative_differentialEquation f a b eigenvalue hbase d)
      simp only [derivative_add, derivative_C_mul, derivative_zero,
        derivative_insertionOperator, Function.iterate_succ_apply'] at hder ⊢
      push_cast at hder ⊢
      have hvalue :
          eigenvalue - (d + 1) * (b + (d + 1) - 1) =
            eigenvalue - d * (b + d - 1) - (b + 2 * d) := by
        ring
      have hparameter : b + 2 * (d + 1) = b + 2 * d + 2 := by ring
      rw [hvalue, map_sub, hparameter]
      rw [sub_mul]
      convert hder using 1
      abel_nf

/-- The base hypergeometric differential equation for `J`. -/
theorem jPolynomial_differentialEquation (m ε : ℕ) :
    C (((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) + ε + 3)) * jPolynomial m ε +
      insertionOperator (ε + 2) (ε + 4) (jPolynomial m ε).derivative = 0 := by
  cases m with
  | zero => simp [jPolynomial, insertionOperator]
  | succ m =>
      cases m with
      | zero => simp [jPolynomial, insertionOperator]
      | succ n =>
          simp only [Nat.add_sub_cancel]
          apply Polynomial.ext
          intro k
          cases k with
          | zero =>
              rw [coeff_add, coeff_C_mul, coeff_zero]
              have hM0 :
                  (insertionOperator (ε + 2) (ε + 4)
                    (jPolynomial (n + 1 + 1) ε).derivative).coeff 0 =
                    (ε + 2) * (jPolynomial (n + 1 + 1) ε).coeff 1 := by
                rw [coeff_zero_eq_eval_zero, insertionOperator_eval_zero,
                  ← coeff_zero_eq_eval_zero, coeff_derivative]
                ring
              rw [hM0, coeff_jPolynomial, if_pos (by lia : 0 < n + 1 + 1),
                coeff_jPolynomial, if_pos (by lia : 1 < n + 1 + 1)]
              have hrec := jCoeff_succ_mul (n + 1 + 1) ε 0
              simp only [jCoeff_zero] at hrec ⊢
              push_cast at hrec ⊢
              ring_nf at hrec ⊢
              linear_combination hrec
          | succ k =>
              rw [coeff_add, coeff_C_mul, coeff_insertionOperator_succ,
                coeff_derivative, coeff_derivative, coeff_zero]
              by_cases hk : k + 1 < n + 1 + 1
              · have hcur :
                    (jPolynomial (n + 1 + 1) ε).coeff (k + 1) =
                      jCoeff (n + 1 + 1) ε (k + 1) := by
                  rw [coeff_jPolynomial, if_pos hk]
                have hnext :
                    (jPolynomial (n + 1 + 1) ε).coeff (k + 1 + 1) =
                      jCoeff (n + 1 + 1) ε (k + 1 + 1) := by
                  rw [coeff_jPolynomial]
                  by_cases hlt : k + 1 + 1 < n + 1 + 1
                  · rw [if_pos hlt]
                  · have heq : k + 1 + 1 = n + 1 + 1 := by lia
                    rw [if_neg hlt, heq,
                      jCoeff_self_eq_zero (n + 1 + 1) ε (by lia)]
                rw [hcur, hnext]
                have hrec := jCoeff_succ_mul (n + 1 + 1) ε (k + 1)
                push_cast at hrec ⊢
                ring_nf at hrec ⊢
                linear_combination hrec
              · have hcur :
                    (jPolynomial (n + 1 + 1) ε).coeff (k + 1) = 0 := by
                  rw [coeff_jPolynomial, if_neg hk]
                have hnext :
                    (jPolynomial (n + 1 + 1) ε).coeff (k + 1 + 1) = 0 := by
                  rw [coeff_jPolynomial,
                    if_neg (by lia : ¬k + 1 + 1 < n + 1 + 1)]
                rw [hcur, hnext]
                ring

/-- The differentiated hypergeometric equation for every row of derivatives
of `J`. The identity remains valid after the derivative tower reaches zero. -/
theorem iteratedDerivative_jPolynomial_differentialEquation (m ε d : ℕ) :
    C ((((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)) *
        (derivative^[d]) (jPolynomial m ε) +
      insertionOperator (ε + d + 2) (ε + 2 * d + 4)
        ((derivative^[d + 1]) (jPolynomial m ε)) = 0 := by
  have h := iteratedDerivative_differentialEquation
    (jPolynomial m ε) (ε + 2) (ε + 4)
    (((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) + ε + 3))
    (jPolynomial_differentialEquation m ε) d
  have hvalue :
      (((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3) =
        ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) + ε + 3) -
          d * (ε + 4 + d - 1) := by
    ring
  have ha : (ε : ℝ) + d + 2 = (ε : ℝ) + 2 + d := by ring
  have hb : (ε : ℝ) + 2 * d + 4 = (ε : ℝ) + 4 + 2 * d := by ring
  rw [hvalue, ha, hb]
  exact h

/-- The vertical differential identity propagated across every Darboux square
of the finite-offset triangle. -/
theorem triangleFamily_vertical_differentialEquation (m ε d : ℕ) :
    ∀ t : ℕ,
      C ((((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)) *
          triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d t +
        insertionOperator
          ((ε : ℝ) + 1 / 2 + d + 3 / 2)
          ((ε : ℝ) + 1 / 2 + 2 * d + 7 / 2 - t)
          (triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) t) = 0
  | 0 => by
      have ha : (ε : ℝ) + 1 / 2 + d + 3 / 2 = (ε : ℝ) + d + 2 := by ring
      have hb : (ε : ℝ) + 1 / 2 + 2 * d + 7 / 2 = (ε : ℝ) + 2 * d + 4 := by
        ring
      simp only [triangleFamily_zero, Nat.cast_zero, sub_zero]
      rw [ha, hb]
      exact iteratedDerivative_jPolynomial_differentialEquation m ε d
  | t + 1 => by
      have hmap := congrArg
        (insertionOperator ((ε : ℝ) + 1 / 2 + t)
          ((ε : ℝ) + 1 / 2 + d + 1))
        (triangleFamily_vertical_differentialEquation m ε d t)
      rw [insertionOperator_add, insertionOperator_C_mul, insertionOperator_zero] at hmap
      rw [triangle_insertionOperator_comp_commute] at hmap
      rw [triangleFamily_succ, triangleFamily_succ]
      have ht :
          (ε : ℝ) + 1 / 2 + 2 * d + 7 / 2 - (t + 1) =
            (ε : ℝ) + 1 / 2 + 2 * d + 7 / 2 - t - 1 := by
        ring
      have hd :
          (ε : ℝ) + 1 / 2 + (d + 1) + 1 =
            (ε : ℝ) + 1 / 2 + d + 1 + 1 := by
        ring
      push_cast
      rw [ht, hd]
      exact hmap

/-- The last Darboux square in a row expresses the next diagonal entry using
the vertical eigenvalue and the `(1-X)` correction. -/
theorem triangleFamily_diagonal_relation (m ε d : ℕ) :
    C ((((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)) *
          triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d d +
        triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) (d + 1) =
      -(C (3 / 2 : ℝ) * (1 - X) *
        triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) d) := by
  have hvertical := triangleFamily_vertical_differentialEquation m ε d d
  have hb :
      (ε : ℝ) + 1 / 2 + 2 * d + 7 / 2 - d =
        (ε : ℝ) + 1 / 2 + d + 7 / 2 := by
    ring
  rw [hb] at hvertical
  have hshift := insertionOperator_add_parameters
    ((ε : ℝ) + 1 / 2 + d) ((ε : ℝ) + 1 / 2 + d + 2) (3 / 2)
    (triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) d)
  have hshiftB :
      (ε : ℝ) + 1 / 2 + d + 2 + 3 / 2 =
        (ε : ℝ) + 1 / 2 + d + 7 / 2 := by
    ring
  rw [hshiftB] at hshift
  rw [hshift] at hvertical
  have hdiagonal :
      triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) (d + 1) =
        insertionOperator ((ε : ℝ) + 1 / 2 + d)
          ((ε : ℝ) + 1 / 2 + d + 2)
          (triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) d) := by
    rw [triangleFamily_succ]
    have hdiagB :
        (ε : ℝ) + 1 / 2 + (d + 1) + 1 =
          (ε : ℝ) + 1 / 2 + d + 2 := by
      ring
    push_cast
    rw [hdiagB]
  rw [hdiagonal]
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_assoc] using hvertical

/-- Signed form of the last-square relation. This is the diagonal recurrence
whose correction term has positive coefficient `3/2`. -/
theorem signedTriangleFamily_diagonal_relation (m ε d : ℕ) :
    C ((((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)) *
          signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d d -
        signedTriangleFamily
          ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) (d + 1) =
      C (3 / 2 : ℝ) * (1 - X) *
        signedTriangleFamily
          ((ε : ℝ) + 1 / 2) (jPolynomial m ε) (d + 1) d := by
  have hscaled := congrArg (C ((-1 : ℝ) ^ d) * ·)
    (triangleFamily_diagonal_relation m ε d)
  simp only [signedTriangleFamily, pow_succ, map_mul, map_neg, map_one] at hscaled ⊢
  linear_combination hscaled

end ToricContribution
end ParkingFunctions
end RealRooted
