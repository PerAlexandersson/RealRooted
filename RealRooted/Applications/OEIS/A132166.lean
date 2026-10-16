module

public import Mathlib
public import RealRooted.MaWang.DerivativeStep
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
public import RealRooted.Mathlib.Algebra.Polynomial.Derivative
public import RealRooted.QuadraticRoot
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.ScalarNormalization
public import RealRooted.WagnerX.NonnegativeRoots

/-!
# OEIS A132166

This module defines the shifted row polynomials of OEIS A132166 by their
differential recurrence. It proves the exact multiplicity of the recurring
root `-36` and the two recurrences for the residual quotients.

The intended repository destination is
`RealRooted/Applications/OEIS/A132166.lean`.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.Applications.OEIS.A132166

/-- Row polynomials `P_n = ∑_m a(n+3, m) X^(m-1)` of OEIS A132166 (convolution triangle from
A036224), defined by `P_0 = X² + 42 X + 336` and the first-order derivative recurrence
`P_{n+1} = 2 (X + 3n + 27)/(n+4) · P_n + X (X+36)/(n+4) · P_n'`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => X ^ 2 + C 42 * X + C 336
  | n + 1 =>
    C (2 / ((n : ℝ) + 4)) * (X + C (3 * (n : ℝ) + 27)) * polynomial n +
      C (1 / ((n : ℝ) + 4)) * (X * (X + C 36)) * derivative (polynomial n)

/-- The expected multiplicity `⌊(n+2)/6⌋` of the root `-36` of `P_n`. -/
def multiplicity (n : ℕ) : ℕ := (n + 2) / 6

private def translatedPolynomial (n : ℕ) : ℝ[X] :=
  (polynomial n).comp (X + C (-36))

private theorem translatedPolynomial_zero :
    translatedPolynomial 0 = X ^ 2 + C (-30) * X + C 120 := by
  simp only [translatedPolynomial, polynomial, add_comp, pow_comp, mul_comp, C_comp, X_comp]
  simp only [map_neg, map_ofNat]
  ring

private theorem translatedPolynomial_succ (n : ℕ) :
    translatedPolynomial (n + 1) =
    C (2 / ((n : ℝ) + 4)) * (X * translatedPolynomial n) +
    C (2 * (3 * (n : ℝ) - 9) / ((n : ℝ) + 4)) * translatedPolynomial n +
    C (1 / ((n : ℝ) + 4)) * (X * (X * derivative (translatedPolynomial n))) +
    C (-36 / ((n : ℝ) + 4)) * (X * derivative (translatedPolynomial n)) := by
  have hd :
      derivative (translatedPolynomial n) =
        (derivative (polynomial n)).comp (X + C (-36)) := by
    simp [translatedPolynomial, derivative_comp]
  rw [hd]
  simp only [translatedPolynomial, polynomial, add_comp, mul_comp, C_comp, X_comp]
  have e1 : C (2 * (3 * (n : ℝ) - 9) / ((n : ℝ) + 4)) =
      C (2 / ((n : ℝ) + 4)) * (C (3 * (n:ℝ) + 27) + C (-36)) := by
    rw [← C_add, ← C_mul]; congr 1; ring
  have e2 : C (-36 / ((n : ℝ) + 4)) = C (1 / ((n : ℝ) + 4)) * C (-36) := by
    rw [← C_mul]; congr 1; ring
  have e3 : (C (-36 : ℝ)) + C 36 = 0 := by rw [← C_add]; norm_num
  rw [e1, e2]
  linear_combination
    (C (1 / ((n : ℝ) + 4)) * (X + C (-36)) *
      (derivative (polynomial n)).comp (X + C (-36))) * e3

private theorem coeff_X_mul_derivative' (p : ℝ[X]) (j : ℕ) :
    (X * derivative p).coeff j = (j : ℝ) * p.coeff j := by
  cases j with
  | zero => simp
  | succ k => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

private theorem coeff_translatedPolynomial_succ_succ (n j : ℕ) :
    (translatedPolynomial (n + 1)).coeff (j + 1) =
      (1 / ((n : ℝ) + 4)) * (((j : ℝ) + 2) * (translatedPolynomial n).coeff j +
        (6 * (n : ℝ) - 18 - 36 * ((j : ℝ) + 1)) * (translatedPolynomial n).coeff (j + 1)) := by
  rw [translatedPolynomial_succ]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_mul_derivative', coeff_derivative]
  ring

private theorem coeff_translatedPolynomial_succ_zero (n : ℕ) :
    (translatedPolynomial (n + 1)).coeff 0 =
      (1 / ((n : ℝ) + 4)) * ((6 * (n : ℝ) - 18) * (translatedPolynomial n).coeff 0) := by
  rw [translatedPolynomial_succ]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero]
  ring

private def signedCoefficient (n j : ℕ) : ℝ :=
  (-1) ^ (n + j) * (translatedPolynomial n).coeff j

private theorem sc_succ_succ (n j : ℕ) :
    signedCoefficient (n + 1) (j + 1) =
    (1 / ((n : ℝ) + 4)) * (((j : ℝ) + 2) * signedCoefficient n j +
      (36 * ((j : ℝ) + 1) + 18 - 6 * (n : ℝ)) * signedCoefficient n (j + 1)) := by
  simp only [signedCoefficient, coeff_translatedPolynomial_succ_succ,
    pow_succ, show n + 1 + (j + 1) = n + j + 2 by ring,
    show n + (j + 1) = n + j + 1 by ring]
  ring

private theorem sc_succ_zero (n : ℕ) : signedCoefficient (n + 1) 0 =
    (1 / ((n : ℝ) + 4)) * ((18 - 6 * (n : ℝ)) * signedCoefficient n 0) := by
  simp only [signedCoefficient, coeff_translatedPolynomial_succ_zero, add_zero, pow_succ]
  ring

private def Invariant (n : ℕ) : Prop :=
  (∀ j, 0 ≤ signedCoefficient n j) ∧
    (∀ j, 6 * j + 4 ≤ n → signedCoefficient n j = 0) ∧
      0 < signedCoefficient n (multiplicity n)

private theorem inv_zero : Invariant 0 := by
  have hc : ∀ j, signedCoefficient 0 j = (translatedPolynomial 0).coeff j * (-1) ^ j := by
    intro j; simp [signedCoefficient, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [hc, translatedPolynomial_zero]
    rcases j with _ | _ | _ | j
    · simp
    · simp [coeff_C]
    · simp [coeff_X_pow]
    · simp [coeff_X_pow]
  · intro j hj; lia
  · rw [show multiplicity 0 = 0 from rfl, hc, translatedPolynomial_zero]; simp

private theorem term0_nonneg (n : ℕ) (h : Invariant n) :
    0 ≤ (18 - 6 * (n : ℝ)) * signedCoefficient n 0 := by
  by_cases hn : n ≤ 3
  · apply mul_nonneg _ (h.1 0)
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  · rw [h.2.1 0 (by lia)]; simp

private theorem term1_nonneg (n j : ℕ) (h : Invariant n) :
    0 ≤ (36 * ((j : ℝ) + 1) + 18 - 6 * (n : ℝ)) * signedCoefficient n (j + 1) := by
  by_cases hn : 6 * (j + 1) + 4 ≤ n
  · rw [h.2.1 _ hn]; simp
  · apply mul_nonneg _ (h.1 _)
    have : (n : ℝ) ≤ 6 * j + 9 := by exact_mod_cast (by lia : n ≤ 6 * j + 9)
    linarith

private theorem inv_succ (n : ℕ) (h : Invariant n) :
    Invariant (n + 1) := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rcases j with _ | j
    · rw [sc_succ_zero]; exact mul_nonneg hpos.le (term0_nonneg n h)
    · rw [sc_succ_succ]
      exact mul_nonneg hpos.le (add_nonneg (mul_nonneg (by positivity) (h.1 j))
        (term1_nonneg n j h))
  · intro j hj
    rcases j with _ | j
    · rw [sc_succ_zero]
      by_cases hn : n = 3
      · subst hn; norm_num
      · rw [h.2.1 0 (by lia)]; simp
    · have h1 : 6 * j + 4 ≤ n := by lia
      rw [sc_succ_succ, h.2.1 j h1]
      by_cases hn : n = 6 * j + 9
      · subst hn; push_cast; ring
      · have h2 : 6 * (j + 1) + 4 ≤ n := by lia
        rw [h.2.1 (j + 1) h2]; simp
  · rcases (by
        unfold multiplicity
        lia : multiplicity (n + 1) = multiplicity n ∨
          multiplicity (n + 1) = multiplicity n + 1) with hm | hm
    · rcases hk : multiplicity n with _ | k
      · rw [hm, hk, sc_succ_zero]
        have h0 := h.2.2; rw [hk] at h0
        have : (n : ℝ) ≤ 2 := by exact_mod_cast (by unfold multiplicity at hm hk; lia : n ≤ 2)
        apply mul_pos hpos (mul_pos (by linarith) h0)
      · rw [hm, hk, sc_succ_succ]
        have h0 := h.2.2; rw [hk] at h0
        have : (n : ℝ) ≤ 6 * k + 8 := by
          exact_mod_cast (by unfold multiplicity at hm hk; lia : n ≤ 6 * k + 8)
        apply mul_pos hpos
        apply add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (h.1 k))
        apply mul_pos (by linarith) h0
    · rw [hm, sc_succ_succ]
      apply mul_pos hpos
      exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) h.2.2) (term1_nonneg _ _ h)

private theorem inv_all (n : ℕ) : Invariant n := by
  induction n with
  | zero => exact inv_zero
  | succ n ih => exact inv_succ n ih

private theorem coeff_translatedPolynomial_eq_zero (n j : ℕ)
    (hj : j < multiplicity n) :
    (translatedPolynomial n).coeff j = 0 := by
  have := (inv_all n).2.1 j (by unfold multiplicity at hj; lia)
  simpa [signedCoefficient] using this

private theorem coeff_translatedPolynomial_mu_ne_zero (n : ℕ) :
    (translatedPolynomial n).coeff (multiplicity n) ≠ 0 := by
  have := (inv_all n).2.2
  intro h0; simp [signedCoefficient, h0] at this

private theorem polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 := by
  intro h0
  apply coeff_translatedPolynomial_mu_ne_zero n
  simp [translatedPolynomial, h0]

private theorem X_sub_C_neg36 : X - C (-36 : ℝ) = X + C 36 := by
  simp [sub_eq_add_neg]

private theorem rootMultiplicity_neg_thirty_six_polynomial_aux (n : ℕ) :
    (polynomial n).rootMultiplicity (-36) = multiplicity n := by
  rw [rootMultiplicity_eq_natTrailingDegree]
  change (translatedPolynomial n).natTrailingDegree = multiplicity n
  have hne : translatedPolynomial n ≠ 0 := fun h0 =>
    coeff_translatedPolynomial_mu_ne_zero n (by simp [h0])
  exact le_antisymm (natTrailingDegree_le_of_ne_zero (coeff_translatedPolynomial_mu_ne_zero n))
    (le_natTrailingDegree hne (fun j hj => coeff_translatedPolynomial_eq_zero n j hj))

/-! ## Sanity checks (exact) -/

/-- The quotient `R_n = P_n / (X + 36)^{μ_n}`. -/
def quotient (n : ℕ) : ℝ[X] := polynomial n /ₘ (X + C 36) ^ multiplicity n

/-- Exact factorization `P_n = (X+36)^{μ_n} R_n`. -/
theorem polynomial_eq_pow_mul_quotient (n : ℕ) :
    polynomial n = (X + C 36) ^ multiplicity n * quotient n := by
  have := pow_mul_divByMonic_rootMultiplicity_eq (polynomial n) (-36)
  rw [rootMultiplicity_neg_thirty_six_polynomial_aux, X_sub_C_neg36] at this
  exact this.symm

/-- `-36` is a root of `P_n` of exact multiplicity `⌊(n+2)/6⌋`. -/
theorem rootMultiplicity_neg_thirty_six_polynomial (n : ℕ) :
    (polynomial n).rootMultiplicity (-36) = multiplicity n := by
  exact rootMultiplicity_neg_thirty_six_polynomial_aux n

/-- The residual quotient does not vanish at `-36`. -/
theorem eval_neg_thirty_six_quotient_ne_zero (n : ℕ) :
    (quotient n).eval (-36) ≠ 0 := by
  have := eval_divByMonic_pow_rootMultiplicity_ne_zero (-36) (polynomial_ne_zero n)
  rwa [rootMultiplicity_neg_thirty_six_polynomial, X_sub_C_neg36] at this

private theorem mul_derivative_pow_X_add_C (m : ℕ) :
    (X + C (36 : ℝ)) * derivative ((X + C 36) ^ m) = C (m : ℝ) * (X + C 36) ^ m := by
  rw [derivative_pow]
  cases m with
  | zero => simp
  | succ k =>
      simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ,
        derivative_add, derivative_X, derivative_C, add_zero]
      ring

private theorem key_succ (n : ℕ) :
    C ((n : ℝ) + 4) * polynomial (n + 1) =
    (X + C 36) ^ multiplicity n *
      ((C 2 * (X + C (3 * (n : ℝ) + 27)) +
          C (multiplicity n : ℝ) * X) * quotient n +
      X * (X + C 36) * derivative (quotient n)) := by
  have hP := polynomial_eq_pow_mul_quotient n
  have hd := mul_derivative_pow_X_add_C (multiplicity n)
  have hn : (n : ℝ) + 4 ≠ 0 := by positivity
  have e1 : C ((n : ℝ) + 4) * C (2 / ((n : ℝ) + 4)) = C 2 := by
    rw [← C_mul]; congr 1; field_simp
  have e2 : C ((n : ℝ) + 4) * C (1 / ((n : ℝ) + 4)) = 1 := by
    rw [← C_mul, ← C_1]; congr 1; field_simp
  rw [polynomial, hP, derivative_mul]
  linear_combination
    ((X + C (3 * (n : ℝ) + 27)) *
      (X + C 36) ^ multiplicity n * quotient n) * e1 +
    (X * (X + C 36) * derivative ((X + C 36) ^ multiplicity n) * quotient n +
      X * (X + C 36) * (X + C 36) ^ multiplicity n *
        derivative (quotient n)) * e2 + X * quotient n * hd

/-- Quotient recurrence when the multiplicity does not jump
(`μ_{n+1} = μ_n = m`):
`(n+4) R_{n+1} = X (X+36) R_n' + ((m+2) X + 6n + 54) R_n`. -/
theorem quotient_succ_of_multiplicity_eq (n : ℕ)
    (h : multiplicity (n + 1) = multiplicity n) :
    C ((n : ℝ) + 4) * quotient (n + 1) =
      X * (X + C 36) * derivative (quotient n) +
        (C ((multiplicity n : ℝ) + 2) * X + C (6 * (n : ℝ) + 54)) * quotient n := by
  have k := key_succ n
  rw [polynomial_eq_pow_mul_quotient (n + 1), h] at k
  have e : C 2 * (X + C (3 * (n : ℝ) + 27)) + C (multiplicity n : ℝ) * X =
      C ((multiplicity n : ℝ) + 2) * X + C (6 * (n : ℝ) + 54) := by
    simp only [map_add, map_mul, map_ofNat]; ring
  apply mul_left_cancel₀ (pow_ne_zero (multiplicity n) (X_add_C_ne_zero (36 : ℝ)))
  linear_combination k + ((X + C 36) ^ multiplicity n * quotient n) * e

/-- Quotient recurrence at a multiplicity jump (`n = 6m + 3`, `μ_{n+1} = μ_n + 1`):
`(n+4) R_{n+1} = X R_n' + (m+2) R_n`. -/
theorem quotient_succ_of_multiplicity_succ (n : ℕ)
    (h : multiplicity (n + 1) = multiplicity n + 1) :
    C ((n : ℝ) + 4) * quotient (n + 1) =
      X * derivative (quotient n) + C ((multiplicity n : ℝ) + 2) * quotient n := by
  have k := key_succ n
  rw [polynomial_eq_pow_mul_quotient (n + 1), h] at k
  have hn6 : (n : ℝ) = 6 * (multiplicity n : ℝ) + 3 := by
    exact_mod_cast (by unfold multiplicity at h ⊢; lia : n = 6 * multiplicity n + 3)
  have e : C 2 * (X + C (3 * (n : ℝ) + 27)) + C (multiplicity n : ℝ) * X =
      (X + C 36) * C ((multiplicity n : ℝ) + 2) := by
    rw [hn6]; simp only [map_add, map_mul, map_ofNat]; ring
  apply mul_left_cancel₀ (pow_ne_zero (multiplicity n + 1) (X_add_C_ne_zero (36 : ℝ)))
  linear_combination k + ((X + C 36) ^ multiplicity n * quotient n) * e

private theorem polynomial_degree_and_monic (n : ℕ) :
    (polynomial n).natDegree = n + 2 ∧ (polynomial n).Monic := by
  let den : ℕ → ℝ := fun k => (k : ℝ) + 4
  have hrec : ∀ k, polynomial (k + 1) =
      (C (36 / den k) * X + C (1 / den k) * X ^ 2) *
          (polynomial k).derivative +
        (C ((6 * (k : ℝ) + 54) / den k) + C (2 / den k) * X) *
          polynomial k + 0 := by
    intro k
    rw [polynomial]
    simp only [den]
    have ha : C (36 / ((k : ℝ) + 4)) =
        C (1 / ((k : ℝ) + 4)) * C 36 := by
      rw [← C_mul]
      congr 1
      ring
    have hc : C ((6 * (k : ℝ) + 54) / ((k : ℝ) + 4)) =
        C (2 / ((k : ℝ) + 4)) * C (3 * (k : ℝ) + 27) := by
      rw [← C_mul]
      congr 1
      ring
    rw [ha, hc]
    ring
  have hseed : polynomial 0 ≠ 0 := by
    intro hz
    have hc := congrArg (Polynomial.coeff · 2) hz
    norm_num [polynomial, coeff_add, coeff_X_pow, coeff_X] at hc
  have hrem : ∀ k, (0 : ℝ[X]).natDegree ≤ (polynomial 0).natDegree + k := by
    intro k
    simp
  have hfactor : ∀ k,
      (1 / den k) * (((polynomial 0).natDegree + k : ℕ) : ℝ) +
        2 / den k ≠ 0 := by
    intro k
    have hdegree : (polynomial 0).natDegree = 2 := by
      rw [polynomial]
      compute_degree!
    rw [hdegree]
    simp only [den]
    positivity
  have hresult :=
    Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_recurrence_of_ne_zero
      polynomial (fun _ => 0) (fun k => 36 / den k) (fun k => 1 / den k)
      (fun k => (6 * (k : ℝ) + 54) / den k) (fun k => 2 / den k)
      hrec hseed hrem hfactor n
  have hzeroDegree : (polynomial 0).natDegree = 2 := by
    rw [polynomial]
    compute_degree!
  have hfactorOne : ∀ k,
      (1 / den k) * (((polynomial 0).natDegree + k : ℕ) : ℝ) +
        2 / den k = 1 := by
    intro k
    rw [hzeroDegree]
    simp only [den]
    have hden : (k : ℝ) + 4 ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hzeroLeading : (polynomial 0).leadingCoeff = 1 := by
    have hmonic : (polynomial 0).Monic := by
      rw [polynomial]
      monicity!
    exact hmonic.leadingCoeff
  constructor
  · simpa [hzeroDegree, Nat.add_comm] using hresult.1
  · rw [Monic.def, hresult.2]
    simp only [hfactorOne, Finset.prod_const_one, one_mul]
    exact hzeroLeading

/-- The A132166 model row indexed by `n` is monic of degree `n + 2`. -/
theorem polynomial_natDegree (n : ℕ) :
    (polynomial n).natDegree = n + 2 :=
  (polynomial_degree_and_monic n).1

private theorem polynomial_monic (n : ℕ) : (polynomial n).Monic :=
  (polynomial_degree_and_monic n).2

private theorem polynomial_nonneg (n : ℕ) :
    HasNonnegCoeffs (polynomial n) := by
  induction n with
  | zero =>
      rw [polynomial]
      exact ((hasNonnegCoeffs_X.pow 2).add
        ((hasNonnegCoeffs_C (by norm_num)).mul hasNonnegCoeffs_X)).add
          (hasNonnegCoeffs_C (by norm_num))
  | succ n ih =>
      rw [polynomial]
      apply HasNonnegCoeffs.add
      · exact ((hasNonnegCoeffs_C (by positivity)).mul
          (hasNonnegCoeffs_X_add_C (by positivity))).mul ih
      · exact ((hasNonnegCoeffs_C (by positivity)).mul
          (hasNonnegCoeffs_X.mul (hasNonnegCoeffs_X_add_C (by norm_num)))).mul
            ih.derivative

private def reflectedPolynomial (n : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ n) * (translatedPolynomial n).comp (-X)

private theorem coeff_reflectedPolynomial (n j : ℕ) :
    (reflectedPolynomial n).coeff j = signedCoefficient n j := by
  rw [reflectedPolynomial, coeff_C_mul, coeff_comp_neg_X]
  simp only [signedCoefficient, pow_add]
  ring

private theorem reflectedPolynomial_nonneg (n : ℕ) :
    HasNonnegCoeffs (reflectedPolynomial n) := by
  intro j
  rw [coeff_reflectedPolynomial]
  exact (inv_all n).1 j

private theorem reflectedPolynomial_ne_zero (n : ℕ) :
    reflectedPolynomial n ≠ 0 := by
  intro hz
  have hc := congrArg (Polynomial.coeff · (multiplicity n)) hz
  rw [coeff_reflectedPolynomial] at hc
  exact (ne_of_gt (inv_all n).2.2) (by simpa using hc)

private theorem isRoot_le_zero {n : ℕ} {r : ℝ}
    (hr : (polynomial n).IsRoot r) : r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (polynomial_nonneg n) r
    ((mem_roots (polynomial_monic n).ne_zero).mpr hr)

private theorem isRoot_ge_neg_thirty_six {n : ℕ} {r : ℝ}
    (hr : (polynomial n).IsRoot r) : -36 ≤ r := by
  have hreflect : (reflectedPolynomial n).IsRoot (-36 - r) := by
    rw [Polynomial.IsRoot.def] at hr ⊢
    simp only [reflectedPolynomial, eval_mul, eval_C, eval_comp, eval_neg,
      eval_X, translatedPolynomial, eval_add]
    convert mul_eq_zero_of_right ((-1 : ℝ) ^ n) hr using 1
    ring_nf
  have hnonpos : -36 - r ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs (reflectedPolynomial_nonneg n) (-36 - r)
      ((mem_roots (reflectedPolynomial_ne_zero n)).mpr hreflect)
  linarith

private theorem quotient_ne_zero (n : ℕ) : quotient n ≠ 0 := by
  intro hz
  exact eval_neg_thirty_six_quotient_ne_zero n (by simp [hz])

private theorem quotient_natDegree (n : ℕ) :
    (quotient n).natDegree = n + 2 - multiplicity n := by
  rw [quotient, natDegree_divByMonic _ ((monic_X_add_C 36).pow _),
    polynomial_natDegree, natDegree_pow, natDegree_X_add_C]
  simp only [Nat.mul_one]

private theorem quotient_posLeading (n : ℕ) :
    HasPosLeadingCoeff (quotient n) := by
  unfold HasPosLeadingCoeff
  rw [quotient]
  have hmonic : ((X + C (36 : ℝ)) ^ multiplicity n).Monic :=
    (monic_X_add_C 36).pow _
  have hdegree : ((X + C (36 : ℝ)) ^ multiplicity n).degree ≤
      (polynomial n).degree := by
    rw [degree_eq_natDegree hmonic.ne_zero,
      degree_eq_natDegree (polynomial_monic n).ne_zero,
      natDegree_pow, natDegree_X_add_C, polynomial_natDegree]
    simp only [Nat.mul_one]
    exact_mod_cast (by unfold multiplicity; lia : multiplicity n ≤ n + 2)
  rw [leadingCoeff_divByMonic_of_monic hmonic hdegree,
    (polynomial_monic n).leadingCoeff]
  norm_num

private theorem quotient_isRoot_polynomial {n : ℕ} {r : ℝ}
    (hr : (quotient n).IsRoot r) : (polynomial n).IsRoot r := by
  rw [polynomial_eq_pow_mul_quotient, Polynomial.IsRoot.def, eval_mul]
  rw [Polynomial.IsRoot.def] at hr
  exact mul_eq_zero_of_right _ hr

private theorem quotient_splits_zero : (quotient 0).Splits := by
  have heq : quotient 0 = polynomial 0 := by
    simp only [quotient, multiplicity, Nat.zero_add, Nat.reduceDiv, pow_zero,
      divByMonic_one]
  rw [heq, polynomial]
  apply splits_of_natDegree_eq_two_of_discrim_nonneg
  · compute_degree!
  · norm_num [discrim, coeff_add, coeff_X, coeff_X_pow]

private theorem quotient_splits (n : ℕ) : (quotient n).Splits := by
  induction n with
  | zero => exact quotient_splits_zero
  | succ n ih =>
      rcases (by
        unfold multiplicity
        lia : multiplicity (n + 1) = multiplicity n ∨
          multiplicity (n + 1) = multiplicity n + 1) with hm | hm
      · let u : ℝ[X] := C (1 / ((n : ℝ) + 4)) *
            (C ((multiplicity n : ℝ) + 2) * X + C (6 * (n : ℝ) + 54))
        let v : ℝ[X] := C (1 / ((n : ℝ) + 4)) * X * (X + C 36)
        have hrec : quotient (n + 1) =
            u * quotient n + v * (quotient n).derivative := by
          have h := quotient_succ_of_multiplicity_eq n hm
          have hn : (n : ℝ) + 4 ≠ 0 := by positivity
          have hnorm := eq_C_inv_mul_of_C_mul_eq hn h
          simp only [u, v]
          rw [hnorm]
          simp only [one_div]
          ring
        have hv : ∀ r, (quotient n).IsRoot r → v.eval r ≤ 0 := by
          intro r hr
          have hp := quotient_isRoot_polynomial hr
          have hlo := isRoot_ge_neg_thirty_six hp
          have hhi := isRoot_le_zero hp
          simp only [v, eval_mul, eval_C, eval_X, eval_add]
          have hscale : 0 ≤ 1 / ((n : ℝ) + 4) := by positivity
          have hprod : r * (r + 36) ≤ 0 := by nlinarith
          nlinarith
        have hstrict :=
          MaWang.strictInterl_derivative_of_nonpos_of_recurrence_of_splits
            ih hrec (quotient_posLeading (n + 1))
            (by
              rw [quotient_natDegree, quotient_natDegree, hm]
              exact Nat.sub_le_sub_right (by lia) _)
            (by
              rw [quotient_natDegree, quotient_natDegree, hm]
              have hmu : multiplicity n ≤ n + 2 := by
                unfold multiplicity
                lia
              have hadd : n + 1 + 2 = (n + 2) + 1 := by lia
              rw [hadd]
              exact (Nat.succ_sub hmu).le)
            (quotient_posLeading n) hv
        rw [← hrec] at hstrict
        exact hstrict.2.1.2
      · let u : ℝ[X] := C (1 / ((n : ℝ) + 4)) *
            C ((multiplicity n : ℝ) + 2)
        let v : ℝ[X] := C (1 / ((n : ℝ) + 4)) * X
        have hrec : quotient (n + 1) =
            u * quotient n + v * (quotient n).derivative := by
          have h := quotient_succ_of_multiplicity_succ n hm
          have hn : (n : ℝ) + 4 ≠ 0 := by positivity
          have hnorm := eq_C_inv_mul_of_C_mul_eq hn h
          simp only [u, v]
          rw [hnorm]
          simp only [one_div]
          ring
        have hv : ∀ r, (quotient n).IsRoot r → v.eval r ≤ 0 := by
          intro r hr
          have hhi := isRoot_le_zero (quotient_isRoot_polynomial hr)
          simp only [v, eval_mul, eval_C, eval_X]
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hhi
        have hstrict :=
          MaWang.strictInterl_derivative_of_nonpos_of_recurrence_of_splits
            ih hrec (quotient_posLeading (n + 1))
            (by
              rw [quotient_natDegree, quotient_natDegree, hm]
              have hadd : n + 1 + 2 = (n + 2) + 1 := by lia
              rw [hadd, Nat.add_sub_add_right])
            (by
              rw [quotient_natDegree, quotient_natDegree, hm]
              have hadd : n + 1 + 2 = (n + 2) + 1 := by lia
              rw [hadd, Nat.add_sub_add_right]
              lia)
            (quotient_posLeading n) hv
        rw [← hrec] at hstrict
        exact hstrict.2.1.2

/-- Every A132166 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  rw [polynomial_eq_pow_mul_quotient]
  exact ((Splits.X_add_C 36).pow (multiplicity n)).mul (quotient_splits n)

/-- Consecutive A132166 model rows strictly interlace. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  let u : ℝ[X] := C (2 / ((n : ℝ) + 4)) *
    (X + C (3 * (n : ℝ) + 27))
  let v : ℝ[X] := C (1 / ((n : ℝ) + 4)) * (X * (X + C 36))
  have hrec : polynomial (n + 1) =
      u * polynomial n + v * (polynomial n).derivative := by
    rw [polynomial]
  have hv : ∀ r, (polynomial n).IsRoot r → v.eval r ≤ 0 := by
    intro r hr
    have hlo := isRoot_ge_neg_thirty_six hr
    have hhi := isRoot_le_zero hr
    simp only [v, eval_mul, eval_C, eval_X, eval_add]
    have hscale : 0 ≤ 1 / ((n : ℝ) + 4) := by positivity
    have hprod : r * (r + 36) ≤ 0 := by nlinarith
    nlinarith
  have hstrict :=
    MaWang.strictInterl_derivative_of_nonpos_of_recurrence_of_splits
      (polynomial_splits n) hrec
      (hasPosLeadingCoeff_of_monic (polynomial_monic (n + 1)))
      (by rw [polynomial_natDegree, polynomial_natDegree]; lia)
      (by rw [polynomial_natDegree, polynomial_natDegree])
      (hasPosLeadingCoeff_of_monic (polynomial_monic n)) hv
  rw [← hrec] at hstrict
  exact hstrict

/-- Consecutive A132166 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_natDegree, polynomial_natDegree])

/-- The first-order update used by the A132166 recurrence model. -/
def nextRow (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (2 / ((n : ℝ) + 4)) * (X + C (3 * (n : ℝ) + 27)) * p +
    C (1 / ((n : ℝ) + 4)) * (X * (X + C 36)) * p.derivative

private theorem polynomial_step (n : ℕ) :
    polynomial (n + 1) = nextRow n (polynomial n) := rfl

private theorem polynomial_one :
    polynomial 1 = C 4536 + C 1113 * X + C 63 * X ^ 2 + X ^ 3 := by
  apply Polynomial.funext
  intro r
  norm_num [polynomial, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

/-- Every sequence with the A132166 base rows and first-order update interlaces. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = C 336 + C 42 * X + X ^ 2)
    (_hone : P 1 = C 4536 + C 1113 * X + C 63 * X ^ 2 + X ^ 3)
    (hrec : ∀ n, P (n + 1) = nextRow n (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hbase : P 0 = polynomial 0 := by
    rw [polynomial]
    linear_combination hzero
  have heq := sequence_eq_of_same_lag_one_recurrence nextRow
    hbase hrec polynomial_step
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A132166
