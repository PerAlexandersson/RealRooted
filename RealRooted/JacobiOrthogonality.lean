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
  Polynomial.momentFunctional (jacobiBetaOneMoment α) p

/-- The symmetric beta-one Jacobi pairing. -/
def jacobiBetaOneInner (α : ℝ) (p q : ℝ[X]) : ℝ :=
  Polynomial.momentPairing (jacobiBetaOneMoment α) p q

@[simp]
theorem jacobiBetaOneFunctional_zero (α : ℝ) :
    jacobiBetaOneFunctional α 0 = 0 := by
  simpa only [jacobiBetaOneFunctional] using
    Polynomial.momentFunctional_zero (jacobiBetaOneMoment α)

@[simp]
theorem jacobiBetaOneFunctional_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneFunctional α (p + q) =
      jacobiBetaOneFunctional α p + jacobiBetaOneFunctional α q := by
  simpa only [jacobiBetaOneFunctional] using
    Polynomial.momentFunctional_add (jacobiBetaOneMoment α) p q

@[simp]
theorem jacobiBetaOneFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneFunctional α (C c * p) =
      c * jacobiBetaOneFunctional α p := by
  simpa only [jacobiBetaOneFunctional] using
    Polynomial.momentFunctional_C_mul (jacobiBetaOneMoment α) c p

@[simp]
theorem jacobiBetaOneFunctional_monomial (α c : ℝ) (k : ℕ) :
    jacobiBetaOneFunctional α (monomial k c) =
      c * jacobiBetaOneMoment α k := by
  simpa only [jacobiBetaOneFunctional] using
    Polynomial.momentFunctional_monomial (jacobiBetaOneMoment α) c k

@[simp]
theorem jacobiBetaOneFunctional_X_pow (α : ℝ) (k : ℕ) :
    jacobiBetaOneFunctional α (X ^ k) = jacobiBetaOneMoment α k := by
  simpa only [jacobiBetaOneFunctional] using
    Polynomial.momentFunctional_X_pow (jacobiBetaOneMoment α) k

theorem jacobiBetaOneInner_comm (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α p q = jacobiBetaOneInner α q p := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_comm (jacobiBetaOneMoment α) p q

@[simp]
theorem jacobiBetaOneInner_zero_left (α : ℝ) (p : ℝ[X]) :
    jacobiBetaOneInner α 0 p = 0 := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_zero_left (jacobiBetaOneMoment α) p

@[simp]
theorem jacobiBetaOneInner_zero_right (α : ℝ) (p : ℝ[X]) :
    jacobiBetaOneInner α p 0 = 0 := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_zero_right (jacobiBetaOneMoment α) p

@[simp]
theorem jacobiBetaOneInner_add_left (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaOneInner α (p + q) s =
      jacobiBetaOneInner α p s + jacobiBetaOneInner α q s := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_add_left (jacobiBetaOneMoment α) p q s

@[simp]
theorem jacobiBetaOneInner_add_right (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaOneInner α p (q + s) =
      jacobiBetaOneInner α p q + jacobiBetaOneInner α p s := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_add_right (jacobiBetaOneMoment α) p q s

@[simp]
theorem jacobiBetaOneInner_sum_right {ι : Type*} (α : ℝ) (p : ℝ[X])
    (s : Finset ι) (q : ι → ℝ[X]) :
    jacobiBetaOneInner α p (∑ i ∈ s, q i) =
      ∑ i ∈ s, jacobiBetaOneInner α p (q i) := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_sum_right (jacobiBetaOneMoment α) p s q

@[simp]
theorem jacobiBetaOneInner_C_mul_left (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α (C c * p) q =
      c * jacobiBetaOneInner α p q := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_C_mul_left (jacobiBetaOneMoment α) c p q

@[simp]
theorem jacobiBetaOneInner_C_mul_right (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α p (C c * q) =
      c * jacobiBetaOneInner α p q := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_C_mul_right (jacobiBetaOneMoment α) c p q

theorem jacobiBetaOneInner_monomial (α a b : ℝ) (i j : ℕ) :
    jacobiBetaOneInner α (monomial i a) (monomial j b) =
      a * b * jacobiBetaOneMoment α (i + j) := by
  simpa only [jacobiBetaOneInner] using
    Polynomial.momentPairing_monomial (jacobiBetaOneMoment α) a b i j

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

@[simp]
theorem jacobiBetaOneInner_monomial_right (α c : ℝ) (p : ℝ[X]) (n : ℕ) :
    jacobiBetaOneInner α p (monomial n c) =
      c * jacobiBetaOneInner α p (X ^ n) := by
  rw [← C_mul_X_pow_eq_monomial, jacobiBetaOneInner_C_mul_right]

/-- Beta-one shifted Jacobi polynomials are orthogonal to every polynomial of
strictly smaller degree. -/
theorem shiftedJacobi_betaOneInner_eq_zero {α : ℝ} (hα : -1 < α)
    {n : ℕ} (q : ℝ[X]) (hq : q.natDegree < n) :
    jacobiBetaOneInner α (shiftedJacobi n α 1) q = 0 := by
  rw [jacobiBetaOneInner_eq_shiftedJacobiInner hα]
  exact shiftedJacobiInner_eq_zero hα (by norm_num) q hq

end RealRooted
