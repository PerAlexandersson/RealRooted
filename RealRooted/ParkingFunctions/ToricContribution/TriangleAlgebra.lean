import RealRooted.Jacobi
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

/-- The Jacobi degree-raising identity in the notation of the finite-offset
triangle. -/
theorem insertionOperator_shiftedJacobi_degree_add_one_beta_sub_one
    (n : ℕ) (α β : ℝ) :
    insertionOperator (n + α + 1) (n + α + β + 1)
        (shiftedJacobi n α β) =
      C ((n + 1 : ℕ) : ℝ) * shiftedJacobi (n + 1) α (β - 1) := by
  simpa only [insertionOperator, intervalWeight] using
    shiftedJacobi_degree_add_one_beta_sub_one n α β

/-- Starting a triangle row from a constant produces a shifted Jacobi
polynomial at every horizontal step. -/
theorem triangleFamily_eq_C_mul_shiftedJacobi_of_iterate_derivative_eq_C
    (c K : ℝ) (J : ℝ[X]) (d t : ℕ) (ht : t ≤ d)
    (hbase : (derivative^[d]) J = C K) :
    triangleFamily c J d t =
      C ((t.factorial : ℝ) * K) *
        shiftedJacobi t (c - 1) ((d + 1 - t : ℕ) : ℝ) := by
  induction t with
  | zero => simpa using hbase
  | succ t ih =>
      have ht' : t ≤ d := by lia
      have ht_d_succ : t ≤ d + 1 := by lia
      have ht_succ_d_succ : t + 1 ≤ d + 1 := by lia
      have ha : c + (t : ℝ) = (t : ℝ) + (c - 1) + 1 := by ring
      have hb :
          c + (d : ℝ) + 1 =
            (t : ℝ) + (c - 1) + ((d + 1 - t : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub ht_d_succ]
        push_cast
        ring
      have hβ :
          ((d + 1 - t : ℕ) : ℝ) - 1 =
            ((d + 1 - (t + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_sub ht_d_succ, Nat.cast_sub ht_succ_d_succ]
        push_cast
        ring
      rw [triangleFamily_succ, ih ht', insertionOperator_C_mul, ha, hb,
        insertionOperator_shiftedJacobi_degree_add_one_beta_sub_one, hβ]
      rw [← mul_assoc, ← C_mul]
      congr 2
      rw [Nat.factorial_succ]
      push_cast
      ring

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

/-- For positive `m`, the finite polynomial `J` is the shifted Jacobi
polynomial of degree `m-1`, normalized to have constant coefficient one. -/
theorem C_mul_jPolynomial_eq_shiftedJacobi (m ε : ℕ) (hm : 0 < m) :
    C (Ring.choose (((m - 1 : ℕ) : ℝ) + (ε + 1)) (m - 1)) *
        jPolynomial m ε =
      shiftedJacobi (m - 1) (ε + 1) 1 := by
  let scale : ℝ := Ring.choose (((m - 1 : ℕ) : ℝ) + (ε + 1)) (m - 1)
  have hscale : 0 < scale := by
    apply Polynomial.ring_choose_pos
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hα : -1 < (ε : ℝ) + 1 := by
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  apply eq_of_jacobi_differential_equation (m - 1)
    (α := (ε : ℝ) + 1) (β := 1) hα
  · rw [natDegree_C_mul hscale.ne']
    exact natDegree_jPolynomial_le m ε
  · rw [natDegree_shiftedJacobi (m - 1) hα (by norm_num)]
  · simp [coeff_shiftedJacobi, hm]
  · have hbase := jPolynomial_differentialEquation m ε
    have hscaled := congrArg (C scale * ·) hbase
    simp only [mul_zero] at hscaled
    simp only [derivative_C_mul]
    dsimp only [scale] at hscaled ⊢
    simp only [insertionOperator, intervalWeight] at hscaled
    have ha : (ε : ℝ) + 1 + 1 = (ε : ℝ) + 2 := by ring
    have hb : (ε : ℝ) + 2 + 2 = (ε : ℝ) + 4 := by ring
    have heigen :
        ((m - 1 : ℕ) : ℝ) *
            ((m - 1 : ℕ) + ((ε : ℝ) + 1) + 1 + 1) =
          ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) + (ε : ℝ) + 3) := by
      ring
    rw [ha, hb, heigen]
    linear_combination hscaled
  · exact shiftedJacobi_differential_equation (m - 1) (ε + 1) 1

/-- The standard shifted Jacobi root package in the form required by the
finite-offset triangle. -/
theorem shiftedJacobi_intervalRootData
    (n : ℕ) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalRootData (shiftedJacobi n α β) n := by
  have hp_ne := shiftedJacobi_ne_zero n hα hβ
  refine ⟨natDegree_shiftedJacobi n hα hβ, ?_, shiftedJacobi_splits n hα hβ,
    ?_, ?_⟩
  · rw [shiftedJacobi_eval_zero]
    apply ne_of_gt
    apply Polynomial.ring_choose_pos
    linarith
  · intro r hr
    exact shiftedJacobi_isRoot_mem_Ioo n hα hβ ((mem_roots hp_ne).mp hr)
  · intro r hr
    apply eval_derivative_ne_zero_of_rootMultiplicity_eq_one hr
    have hcount : (shiftedJacobi n α β).roots.count r = 1 :=
      Multiset.count_eq_one_of_mem (shiftedJacobi_roots_nodup n hα hβ)
        ((mem_roots hp_ne).mpr hr)
    simpa [count_roots] using hcount

/-- Each derivative of `J` is a nonzero scalar multiple of the corresponding
shifted Jacobi polynomial. -/
theorem exists_iterate_derivative_jPolynomial_eq_C_mul_shiftedJacobi
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    ∃ c : ℝ, c ≠ 0 ∧
      (derivative^[d]) (jPolynomial m ε) =
        C c * shiftedJacobi (m - 1 - d) (ε + 1 + d) (1 + d) := by
  let scale : ℝ := Ring.choose (((m - 1 : ℕ) : ℝ) + (ε + 1)) (m - 1)
  have hscale : 0 < scale := by
    apply Polynomial.ring_choose_pos
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hα : -1 < (ε : ℝ) + 1 := by
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  obtain ⟨c, hc, hcder⟩ :=
    exists_iterate_derivative_shiftedJacobi_eq_C_mul
      (m - 1) d (α := (ε : ℝ) + 1) (β := 1) hα (by norm_num) hd
  have hscaled := congrArg (derivative^[d])
    (C_mul_jPolynomial_eq_shiftedJacobi m ε hm)
  rw [iterate_derivative_C_mul] at hscaled
  refine ⟨scale⁻¹ * c, mul_ne_zero (inv_ne_zero hscale.ne') hc, ?_⟩
  calc
    (derivative^[d]) (jPolynomial m ε) =
        C scale⁻¹ * (C scale * (derivative^[d]) (jPolynomial m ε)) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hscale.ne', C_1, one_mul]
    _ = C scale⁻¹ * (C c * shiftedJacobi (m - 1 - d)
        ((ε : ℝ) + 1 + d) (1 + d)) := by rw [hscaled, hcder]
    _ = C (scale⁻¹ * c) * shiftedJacobi (m - 1 - d)
        ((ε : ℝ) + 1 + d) (1 + d) := by rw [← mul_assoc, ← C_mul]

/-- The Jacobi/Rolle base-row invariant needed for horizontal propagation
through the finite-offset triangle. -/
theorem iteratedDerivative_jPolynomial_intervalRootData
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    IntervalRootData ((derivative^[d]) (jPolynomial m ε)) (m - 1 - d) := by
  obtain ⟨c, hc, heq⟩ :=
    exists_iterate_derivative_jPolynomial_eq_C_mul_shiftedJacobi m ε d hm hd
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hε0 : 0 ≤ (ε : ℝ) := by positivity
  have hα : -1 < (ε : ℝ) + 1 + d := by linarith
  have hβ : -1 < (1 : ℝ) + d := by linarith
  have hdata :=
    (shiftedJacobi_intervalRootData (m - 1 - d) hα hβ).C_mul hc
  rw [← heq] at hdata
  exact hdata

/-- Every entry in the finite `J` triangle through its diagonal has the exact
degree and simple roots in the open unit interval. -/
theorem jPolynomial_triangleFamily_intervalRootData
    (m ε d t : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) (ht : t ≤ d) :
    IntervalRootData
      (triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d t)
      (m - 1 - d + t) := by
  apply triangleFamily_intervalRootData hd (by positivity)
    (iteratedDerivative_jPolynomial_intervalRootData m ε d hm hd) t ht

/-- Signed normalization preserves the complete root package throughout the
finite `J` triangle. -/
theorem jPolynomial_signedTriangleFamily_intervalRootData
    (m ε d t : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) (ht : t ≤ d) :
    IntervalRootData
      (signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d t)
      (m - 1 - d + t) := by
  exact signedTriangleFamily_intervalRootData
    (jPolynomial_triangleFamily_intervalRootData m ε d t hm hd ht)

/-- The value at zero of an iterated derivative of `J` is its corresponding
coefficient times the factorial. -/
theorem iterate_derivative_jPolynomial_eval_zero
    (m ε d : ℕ) (hd : d < m) :
    ((derivative^[d]) (jPolynomial m ε)).eval 0 =
      d.factorial * jCoeff m ε d := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
    nsmul_eq_mul, Nat.descFactorial_self, coeff_jPolynomial, if_pos hd]

/-- The terminating rising factorial `(1-m)_d` has sign `(-1)^d` before its
zero at `d=m`. -/
theorem negOnePow_mul_realRisingFactorial_one_sub_nat_pos
    (m d : ℕ) (hd : d ≤ m - 1) :
    0 < (-1 : ℝ) ^ d * realRisingFactorial (1 - (m : ℝ)) d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : d ≤ m - 1 := by lia
      have hfactor : 1 - (m : ℝ) + d < 0 := by
        have hdm : d + 1 < m := by lia
        have hdmR : (d : ℝ) + 1 < m := by exact_mod_cast hdm
        linarith
      rw [realRisingFactorial_succ, pow_succ]
      rw [show (-1 : ℝ) ^ d * -1 *
          (realRisingFactorial (1 - (m : ℝ)) d * (1 - (m : ℝ) + d)) =
        ((-1 : ℝ) ^ d * realRisingFactorial (1 - (m : ℝ)) d) *
          -(1 - (m : ℝ) + d) by ring]
      exact mul_pos (ih hd') (neg_pos.mpr hfactor)

/-- The derivative tower has the sign removed by the normalization
`(-1)^d`. -/
theorem negOnePow_mul_iterate_derivative_jPolynomial_eval_zero_pos
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    0 < (-1 : ℝ) ^ d * ((derivative^[d]) (jPolynomial m ε)).eval 0 := by
  rw [iterate_derivative_jPolynomial_eval_zero m ε d (by lia), jCoeff]
  have hA := negOnePow_mul_realRisingFactorial_one_sub_nat_pos m d hd
  have hB : 0 < realRisingFactorial ((m : ℝ) + 2 + ε) d := by
    apply realRisingFactorial_pos
    positivity
  have hC : 0 < realRisingFactorial ((ε : ℝ) + 2) d := by
    apply realRisingFactorial_pos
    positivity
  have hF : 0 < (d.factorial : ℝ) := by positivity
  rw [show
      (-1 : ℝ) ^ d *
          ((d.factorial : ℝ) *
            (realRisingFactorial (1 - (m : ℝ)) d *
                realRisingFactorial ((m : ℝ) + 2 + ε) d /
              (realRisingFactorial ((ε : ℝ) + 2) d * d.factorial))) =
        ((-1 : ℝ) ^ d * realRisingFactorial (1 - (m : ℝ)) d) *
            realRisingFactorial ((m : ℝ) + 2 + ε) d /
          realRisingFactorial ((ε : ℝ) + 2) d by
      field_simp [hF.ne']]
  exact div_pos (mul_pos hA hB) hC

/-- Every signed triangle entry in a nonexceptional row is positively oriented
at the left endpoint. -/
theorem signedTriangleFamily_eval_zero_pos
    (m ε d t : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    0 < (signedTriangleFamily ((ε : ℝ) + 1 / 2)
      (jPolynomial m ε) d t).eval 0 := by
  rw [signedTriangleFamily, eval_mul, eval_C, triangleFamily_eval_zero]
  have hc : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) t := by
    apply realRisingFactorial_pos
    positivity
  have hder := negOnePow_mul_iterate_derivative_jPolynomial_eval_zero_pos
    m ε d hm hd
  nlinarith

/-- Every signed diagonal entry is positively oriented at the left endpoint. -/
theorem signedTriangleFamily_diagonal_eval_zero_pos
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    0 < (signedTriangleFamily ((ε : ℝ) + 1 / 2)
      (jPolynomial m ε) d d).eval 0 := by
  exact signedTriangleFamily_eval_zero_pos m ε d d hm hd

/-- The terminal signed diagonal is a positively scaled shifted Jacobi
polynomial with the lower half-integer first parameter. -/
theorem exists_signedTriangleFamily_terminal_eq_C_mul_shiftedJacobi
    (m ε : ℕ) (hm : 0 < m) :
    ∃ k : ℝ, 0 < k ∧
      signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
          (m - 1) (m - 1) =
        C k * shiftedJacobi (m - 1) ((ε : ℝ) - 1 / 2) 1 := by
  obtain ⟨u, hu, hderivative⟩ :=
    exists_iterate_derivative_jPolynomial_eq_C_mul_shiftedJacobi
      m ε (m - 1) hm le_rfl
  have hbase :
      (derivative^[m - 1]) (jPolynomial m ε) = C u := by
    simpa using hderivative
  have htriangle :=
    triangleFamily_eq_C_mul_shiftedJacobi_of_iterate_derivative_eq_C
      ((ε : ℝ) + 1 / 2) u (jPolynomial m ε) (m - 1) (m - 1)
      le_rfl hbase
  have htriangle' :
      triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
          (m - 1) (m - 1) =
        C (((m - 1).factorial : ℝ) * u) *
          shiftedJacobi (m - 1) ((ε : ℝ) - 1 / 2) 1 := by
    have hα : (ε : ℝ) + 1 / 2 - 1 = (ε : ℝ) - 1 / 2 := by ring
    have hβ : m - 1 + 1 - (m - 1) = 1 := by lia
    simpa only [hα, hβ, Nat.cast_one] using htriangle
  let k : ℝ := (-1 : ℝ) ^ (m - 1) * (((m - 1).factorial : ℝ) * u)
  have heq :
      signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
          (m - 1) (m - 1) =
        C k * shiftedJacobi (m - 1) ((ε : ℝ) - 1 / 2) 1 := by
    rw [signedTriangleFamily, htriangle', ← mul_assoc, ← C_mul]
  have hsigned :
      0 < (signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
        (m - 1) (m - 1)).eval 0 :=
    signedTriangleFamily_diagonal_eval_zero_pos m ε (m - 1) hm le_rfl
  have hJacobi :
      0 < (shiftedJacobi (m - 1) ((ε : ℝ) - 1 / 2) 1).eval 0 := by
    rw [shiftedJacobi_eval_zero]
    apply Polynomial.ring_choose_pos
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have heval := congrArg (Polynomial.eval 0) heq
  simp only [eval_mul, eval_C] at heval
  refine ⟨k, ?_, heq⟩
  nlinarith

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
