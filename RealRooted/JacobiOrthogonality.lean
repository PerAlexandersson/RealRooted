import RealRooted.Jacobi.Orthogonality

/-!
# Algebraic orthogonality for shifted Jacobi polynomials

We encode the beta-one Jacobi inner product through its moments.  This keeps
the polynomial orthogonality argument finite; the power-log integral enters
only later, when strict Markoff monotonicity is extracted from the derivative
of this moment functional.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The `k`th moment of `x ^ α * (1 - x)` on the unit interval. -/
def jacobiBetaOneMoment (α : ℝ) (k : ℕ) : ℝ :=
  (((α + k + 1) * (α + k + 2))⁻¹ : ℝ)

/-- The legacy rational beta-one moments agree with the general shifted
Jacobi moments in the classical parameter range. -/
theorem jacobiBetaOneMoment_eq_shiftedJacobiMoment
    {α : ℝ} (hα : -1 < α) (k : ℕ) :
    jacobiBetaOneMoment α k = shiftedJacobiMoment α 1 k := by
  symm
  simpa only [jacobiBetaOneMoment] using shiftedJacobiMoment_beta_one hα k

/-- The beta-one Jacobi moment functional on real polynomials. -/
def jacobiBetaOneFunctional (α : ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun k c => c * jacobiBetaOneMoment α k

/-- The symmetric beta-one Jacobi pairing. -/
def jacobiBetaOneInner (α : ℝ) (p q : ℝ[X]) : ℝ :=
  jacobiBetaOneFunctional α (p * q)

@[simp]
theorem jacobiBetaOneFunctional_zero (α : ℝ) :
    jacobiBetaOneFunctional α 0 = 0 := by
  simp [jacobiBetaOneFunctional]

@[simp]
theorem jacobiBetaOneFunctional_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneFunctional α (p + q) =
      jacobiBetaOneFunctional α p + jacobiBetaOneFunctional α q := by
  simp only [jacobiBetaOneFunctional]
  apply Polynomial.sum_add_index <;> simp [add_mul]

@[simp]
theorem jacobiBetaOneFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneFunctional α (C c * p) =
      c * jacobiBetaOneFunctional α p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq, mul_add]
  | monomial n a =>
      simp [jacobiBetaOneFunctional, C_mul_monomial, mul_assoc]

@[simp]
theorem jacobiBetaOneFunctional_monomial (α c : ℝ) (k : ℕ) :
    jacobiBetaOneFunctional α (monomial k c) =
      c * jacobiBetaOneMoment α k := by
  simp [jacobiBetaOneFunctional]

@[simp]
theorem jacobiBetaOneFunctional_X_pow (α : ℝ) (k : ℕ) :
    jacobiBetaOneFunctional α (X ^ k) = jacobiBetaOneMoment α k := by
  rw [X_pow_eq_monomial, jacobiBetaOneFunctional_monomial]
  simp

theorem jacobiBetaOneInner_comm (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α p q = jacobiBetaOneInner α q p := by
  simp [jacobiBetaOneInner, mul_comm]

@[simp]
theorem jacobiBetaOneInner_zero_left (α : ℝ) (p : ℝ[X]) :
    jacobiBetaOneInner α 0 p = 0 := by
  simp [jacobiBetaOneInner]

@[simp]
theorem jacobiBetaOneInner_zero_right (α : ℝ) (p : ℝ[X]) :
    jacobiBetaOneInner α p 0 = 0 := by
  simp [jacobiBetaOneInner]

@[simp]
theorem jacobiBetaOneInner_add_left (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaOneInner α (p + q) s =
      jacobiBetaOneInner α p s + jacobiBetaOneInner α q s := by
  simp [jacobiBetaOneInner, add_mul]

@[simp]
theorem jacobiBetaOneInner_add_right (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaOneInner α p (q + s) =
      jacobiBetaOneInner α p q + jacobiBetaOneInner α p s := by
  rw [jacobiBetaOneInner_comm]
  simp only [jacobiBetaOneInner_add_left]
  rw [jacobiBetaOneInner_comm α q p, jacobiBetaOneInner_comm α s p]

@[simp]
theorem jacobiBetaOneInner_sum_right {ι : Type*} (α : ℝ) (p : ℝ[X])
    (s : Finset ι) (q : ι → ℝ[X]) :
    jacobiBetaOneInner α p (∑ i ∈ s, q i) =
      ∑ i ∈ s, jacobiBetaOneInner α p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp]
theorem jacobiBetaOneInner_C_mul_left (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α (C c * p) q =
      c * jacobiBetaOneInner α p q := by
  simp [jacobiBetaOneInner, mul_assoc]

@[simp]
theorem jacobiBetaOneInner_C_mul_right (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α p (C c * q) =
      c * jacobiBetaOneInner α p q := by
  rw [jacobiBetaOneInner_comm]
  simp only [jacobiBetaOneInner_C_mul_left]
  rw [jacobiBetaOneInner_comm]

@[simp]
theorem jacobiBetaOneInner_monomial (α a b : ℝ) (i j : ℕ) :
    jacobiBetaOneInner α (monomial i a) (monomial j b) =
      a * b * jacobiBetaOneMoment α (i + j) := by
  simp [jacobiBetaOneInner, monomial_mul_monomial, mul_assoc]

/-- The legacy beta-one functional is the specialization of the general
shifted Jacobi functional in the classical parameter range. -/
theorem jacobiBetaOneFunctional_eq_shiftedJacobiFunctional
    {α : ℝ} (hα : -1 < α) (p : ℝ[X]) :
    jacobiBetaOneFunctional α p = shiftedJacobiFunctional α 1 p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
      rw [jacobiBetaOneFunctional_monomial,
        shiftedJacobiFunctional_monomial,
        jacobiBetaOneMoment_eq_shiftedJacobiMoment hα]

/-- The legacy beta-one pairing is the specialization of the general shifted
Jacobi pairing in the classical parameter range. -/
theorem jacobiBetaOneInner_eq_shiftedJacobiInner
    {α : ℝ} (hα : -1 < α) (p q : ℝ[X]) :
    jacobiBetaOneInner α p q = shiftedJacobiInner α 1 p q := by
  change jacobiBetaOneFunctional α (p * q) =
    shiftedJacobiFunctional α 1 (p * q)
  exact jacobiBetaOneFunctional_eq_shiftedJacobiFunctional hα _

/-- The differential part of the beta-one shifted Jacobi operator. -/
abbrev jacobiBetaOneOperator (α : ℝ) (p : ℝ[X]) : ℝ[X] :=
  jacobiDifferentialOperator (α + 1) (α + 3) p

@[simp]
theorem jacobiBetaOneOperator_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneOperator α (p + q) =
      jacobiBetaOneOperator α p + jacobiBetaOneOperator α q := by
  simpa only [jacobiBetaOneOperator] using
    jacobiDifferentialOperator_add (α + 1) (α + 3) p q

@[simp]
theorem jacobiBetaOneOperator_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneOperator α (C c * p) =
      C c * jacobiBetaOneOperator α p := by
  simpa only [jacobiBetaOneOperator] using
    jacobiDifferentialOperator_C_mul (α + 1) (α + 3) c p

theorem jacobiBetaOneOperator_monomial (α a : ℝ) (n : ℕ) :
    jacobiBetaOneOperator α (monomial n a) =
      monomial (n - 1) (a * n * (n + α)) +
        monomial n (-a * n * (n + α + 2)) := by
  rw [jacobiBetaOneOperator, jacobiDifferentialOperator_monomial,
    sub_eq_add_neg, ← monomial_neg]
  congr 2 <;> ring

/-- The differential part of the beta-one shifted Jacobi operator is
self-adjoint for its moment pairing. -/
theorem jacobiBetaOneOperator_inner_symm {α : ℝ} (hα : -1 < α)
    (p q : ℝ[X]) :
    jacobiBetaOneInner α (jacobiBetaOneOperator α p) q =
      jacobiBetaOneInner α p (jacobiBetaOneOperator α q) := by
  calc
    _ = shiftedJacobiInner α 1 (jacobiBetaOneOperator α p) q :=
      jacobiBetaOneInner_eq_shiftedJacobiInner hα _ _
    _ = shiftedJacobiInner α 1 p (jacobiBetaOneOperator α q) := by
      change shiftedJacobiInner α 1
        (jacobiDifferentialOperator (α + 1) (α + 3) p) q =
          shiftedJacobiInner α 1 p
            (jacobiDifferentialOperator (α + 1) (α + 3) q)
      convert shiftedJacobiInner_operator_symm (β := 1) hα (by norm_num) p q
        using 1 <;> ring_nf
    _ = _ := (jacobiBetaOneInner_eq_shiftedJacobiInner hα _ _).symm

/-- A shifted Jacobi polynomial with beta parameter one is an eigenvector of
the beta-one differential operator. -/
theorem jacobiBetaOneOperator_shiftedJacobi (n : ℕ) (α : ℝ) :
    jacobiBetaOneOperator α (shiftedJacobi n α 1) =
      C (-(n * (n + α + 2))) * shiftedJacobi n α 1 := by
  change jacobiDifferentialOperator (α + 1) (α + 3)
    (shiftedJacobi n α 1) = _
  have h := jacobiDifferentialOperator_shiftedJacobi n α 1
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) := Polynomial.C_ofNat 2
  simp only [map_add, map_mul, map_neg, map_natCast] at h ⊢
  simp only [hC2] at h ⊢
  norm_num at h ⊢
  convert h using 1 <;> ring

theorem jacobiBetaOneOperator_X_pow (α : ℝ) (n : ℕ) :
    jacobiBetaOneOperator α (X ^ n) =
      C (n * (n + α)) * X ^ (n - 1) +
        C (-(n * (n + α + 2))) * X ^ n := by
  rw [X_pow_eq_monomial, jacobiBetaOneOperator_monomial]
  simp only [← C_mul_X_pow_eq_monomial, one_mul, map_one]
  ring

@[simp]
theorem jacobiBetaOneInner_monomial_right (α c : ℝ) (p : ℝ[X]) (n : ℕ) :
    jacobiBetaOneInner α p (monomial n c) =
      c * jacobiBetaOneInner α p (X ^ n) := by
  rw [← C_mul_X_pow_eq_monomial, jacobiBetaOneInner_C_mul_right]

/-- Beta-one shifted Jacobi polynomials are orthogonal to every lower
monomial. -/
theorem shiftedJacobi_betaOneInner_X_pow_eq_zero {α : ℝ} (hα : -1 < α)
    {n j : ℕ} (hj : j < n) :
    jacobiBetaOneInner α (shiftedJacobi n α 1) (X ^ j) = 0 := by
  rw [jacobiBetaOneInner_eq_shiftedJacobiInner hα]
  exact shiftedJacobiInner_X_pow_eq_zero hα (by norm_num) hj

/-- Beta-one shifted Jacobi polynomials are orthogonal to every polynomial of
strictly smaller degree. -/
theorem shiftedJacobi_betaOneInner_eq_zero {α : ℝ} (hα : -1 < α)
    {n : ℕ} (q : ℝ[X]) (hq : q.natDegree < n) :
    jacobiBetaOneInner α (shiftedJacobi n α 1) q = 0 := by
  rw [jacobiBetaOneInner_eq_shiftedJacobiInner hα]
  exact shiftedJacobiInner_eq_zero hα (by norm_num) q hq

end RealRooted
