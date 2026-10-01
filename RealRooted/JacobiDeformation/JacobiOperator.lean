import RealRooted.JacobiDeformation.Kernel
import RealRooted.JacobiDeformation.Quadrature

/-!
# The positive shifted-Jacobi operator

`positiveJacobiOperator α β` is the negative of the library operator
`jacobiDifferentialOperator (α + 1) (α + β + 2)`, packaged as a linear map.
It does not raise degrees, it is self-adjoint for the shifted-Jacobi moment
pairing and positive on nonconstant polynomials (the finite Jacobi energy
identity), and the
monic shifted-Jacobi polynomials are its eigenvectors with the eigenvalues
`λ_n = n (n + α + β + 1)`.  In Lagrange coordinates at the roots of a
quasi-Jacobi polynomial, the evaluation vectors of `p_0, …, p_{q-1}` are
explicit eigenvectors of its collocation matrix.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Linear-map packaging of the shifted-Jacobi differential operator. -/
def jacobiDifferentialOperatorLinearMap (b c : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := jacobiDifferentialOperator b c
  map_add' := jacobiDifferentialOperator_add b c
  map_smul' a p := by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using
      jacobiDifferentialOperator_C_mul b c a p

theorem natDegree_jacobiDifferentialOperator_le (b c : ℝ) (p : ℝ[X]) :
    (jacobiDifferentialOperator b c p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_jacobiDifferentialOperator,
    coeff_eq_zero_of_natDegree_lt hk,
    coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < k + 1)]
  ring

/-- Negating the library operator gives the positive Jacobi eigenvalues
`j (j + α + β + 1)` used in the deformation proof. -/
def positiveJacobiOperator (α β : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  -jacobiDifferentialOperatorLinearMap (α + 1) (α + β + 2)

theorem eval_positiveJacobiOperator (α β t : ℝ) (p : ℝ[X]) :
    (positiveJacobiOperator α β p).eval t =
      -(t * (1 - t) * p.derivative.derivative.eval t +
        (α + 1 - (α + β + 2) * t) * p.derivative.eval t) := by
  simp only [positiveJacobiOperator, LinearMap.neg_apply, eval_neg]
  change -(jacobiDifferentialOperator (α + 1) (α + β + 2) p).eval t = _
  simp only [jacobiDifferentialOperator, eval_add, eval_mul, eval_X,
    eval_sub, eval_one, eval_C]

/-- Monomial form of the finite Jacobi energy identity. -/
theorem shiftedJacobiInner_X_pow_succ_positiveJacobiOperator_X_pow_succ
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) :
    shiftedJacobiInner α β (X ^ (m + 1))
        (positiveJacobiOperator α β (X ^ (n + 1))) =
      shiftedJacobiInner (α + 1) (β + 1)
        (derivative (X ^ (m + 1))) (derivative (X ^ (n + 1))) := by
  have hop : positiveJacobiOperator α β (X ^ (n + 1)) =
      C ((n + 1 : ℝ) * ((n + 1 : ℝ) + α + β + 1)) * X ^ (n + 1) -
        C ((n + 1 : ℝ) * ((n + 1 : ℝ) + α)) * X ^ n := by
    change -jacobiDifferentialOperator (α + 1) (α + β + 2) (X ^ (n + 1)) = _
    rw [jacobiDifferentialOperator_X_pow]
    push_cast
    ring_nf
  have hrec := shiftedJacobiMoment_succ hα hβ (m + n + 1)
  have hbeta := shiftedJacobiMoment_sub_succ_eq_shift_beta
    hα hβ (m + n + 1)
  have halpha := shiftedJacobiMoment_succ_eq_shift_alpha
    α (β + 1) (m + n)
  have hshift :
      shiftedJacobiMoment (α + 1) (β + 1) (m + n) =
        shiftedJacobiMoment α β (m + n + 1) -
          shiftedJacobiMoment α β (m + n + 2) := by
    rw [← halpha, hbeta]
  rw [hop, shiftedJacobiInner_sub_right,
    shiftedJacobiInner_C_mul_right, shiftedJacobiInner_C_mul_right]
  have hinnerpow (a b : ℕ) :
      shiftedJacobiInner α β (X ^ a) (X ^ b) =
        shiftedJacobiMoment α β (a + b) := by
    simp [shiftedJacobiInner, Polynomial.momentPairing, ← pow_add]
  rw [hinnerpow, hinnerpow]
  have hderivinner :
      shiftedJacobiInner (α + 1) (β + 1)
          (derivative (X ^ (m + 1))) (derivative (X ^ (n + 1))) =
        (m + 1 : ℝ) * (n + 1 : ℝ) *
          shiftedJacobiMoment (α + 1) (β + 1) (m + n) := by
    have hinnerpow' (a b : ℕ) :
        shiftedJacobiInner (α + 1) (β + 1) (X ^ a) (X ^ b) =
          shiftedJacobiMoment (α + 1) (β + 1) (a + b) := by
      simp [shiftedJacobiInner, Polynomial.momentPairing, ← pow_add]
    rw [derivative_X_pow_succ, derivative_X_pow_succ,
      shiftedJacobiInner_C_mul_left, shiftedJacobiInner_C_mul_right,
      hinnerpow']
    ring
  rw [hderivinner]
  rw [show m + 1 + (n + 1) = m + n + 2 by lia,
    show m + 1 + n = m + n + 1 by lia]
  rw [show m + n + 1 + 1 = m + n + 2 by lia] at hrec
  rw [hshift]
  push_cast at hrec ⊢
  linear_combination -(n + 1) * hrec

theorem positiveJacobiOperator_natDegree_lt {q : ℕ} (α β : ℝ)
    (p : ℝ[X]) (hp : p.natDegree < q) :
    (positiveJacobiOperator α β p).natDegree < q := by
  apply lt_of_le_of_lt _ hp
  simpa [positiveJacobiOperator, jacobiDifferentialOperatorLinearMap] using
    natDegree_jacobiDifferentialOperator_le (α + 1) (α + β + 2) p

theorem shiftedJacobiFunctional_mul_positiveJacobiOperator_comm
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p r : ℝ[X]) :
    shiftedJacobiFunctional α β (p * positiveJacobiOperator α β r) =
      shiftedJacobiFunctional α β (positiveJacobiOperator α β p * r) := by
  have hsymm := shiftedJacobiInner_operator_symm hα hβ p r
  have hbase :
      shiftedJacobiFunctional α β
          (p * jacobiDifferentialOperator (α + 1) (α + β + 2) r) =
        shiftedJacobiFunctional α β
          (jacobiDifferentialOperator (α + 1) (α + β + 2) p * r) :=
    hsymm.symm
  have hneg (f : ℝ[X]) :
      shiftedJacobiFunctional α β (-f) = -shiftedJacobiFunctional α β f :=
    (Polynomial.momentFunctionalLinearMap
      (shiftedJacobiMoment α β)).map_neg f
  change shiftedJacobiFunctional α β
      (p * -jacobiDifferentialOperator (α + 1) (α + β + 2) r) =
    shiftedJacobiFunctional α β
      (-jacobiDifferentialOperator (α + 1) (α + β + 2) p * r)
  rw [mul_neg, neg_mul, hneg, hneg]
  exact congrArg Neg.neg hbase

/-- The Jacobi energy identity on arbitrary pairs of power-basis vectors,
including the constant boundary cases. -/
theorem shiftedJacobiInner_X_pow_positiveJacobiOperator_X_pow
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) :
    shiftedJacobiInner α β (X ^ m)
        (positiveJacobiOperator α β (X ^ n)) =
      shiftedJacobiInner (α + 1) (β + 1)
        (derivative (X ^ m)) (derivative (X ^ n)) := by
  cases m with
  | zero =>
      have hcomm := shiftedJacobiFunctional_mul_positiveJacobiOperator_comm
        hα hβ 1 (X ^ n)
      have hop : positiveJacobiOperator α β 1 = 0 := by
        change -jacobiDifferentialOperator (α + 1) (α + β + 2) 1 = 0
        simp [jacobiDifferentialOperator]
      rw [show derivative (X ^ 0 : ℝ[X]) = 0 by simp,
        shiftedJacobiInner_zero_left]
      change shiftedJacobiFunctional α β
          (1 * positiveJacobiOperator α β (X ^ n)) = 0
      rw [hcomm, hop]
      simp
  | succ m =>
      cases n with
      | zero =>
          have hop : positiveJacobiOperator α β 1 = 0 := by
            change -jacobiDifferentialOperator
                (α + 1) (α + β + 2) 1 = 0
            simp [jacobiDifferentialOperator]
          simp [hop]
      | succ n =>
          exact
            shiftedJacobiInner_X_pow_succ_positiveJacobiOperator_X_pow_succ
              hα hβ m n

/-- Finite Jacobi integration by parts: the positive differential operator
has Dirichlet energy given by the shifted moment pairing of derivatives. -/
theorem shiftedJacobiInner_positiveJacobiOperator_eq_derivative
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p r : ℝ[X]) :
    shiftedJacobiInner α β p (positiveJacobiOperator α β r) =
      shiftedJacobiInner (α + 1) (β + 1) p.derivative r.derivative := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs =>
      simp only [shiftedJacobiInner_add_left, derivative_add, hp, hs]
  | monomial m a =>
      induction r using Polynomial.induction_on' with
      | add r s hr hs =>
          simp only [map_add, shiftedJacobiInner_add_right, hr, hs]
      | monomial n b =>
          rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
            show positiveJacobiOperator α β (C b * X ^ n) =
                C b * positiveJacobiOperator α β (X ^ n) by
              rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul],
            derivative_C_mul, derivative_C_mul,
            shiftedJacobiInner_C_mul_left,
            shiftedJacobiInner_C_mul_right,
            shiftedJacobiInner_C_mul_left,
            shiftedJacobiInner_C_mul_right,
            shiftedJacobiInner_X_pow_positiveJacobiOperator_X_pow hα hβ]

/-- The positive Jacobi differential operator has strictly positive energy
on every nonconstant polynomial. -/
theorem shiftedJacobiInner_positiveJacobiOperator_self_pos
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {p : ℝ[X]}
    (hp : p.derivative ≠ 0) :
    0 < shiftedJacobiInner α β p (positiveJacobiOperator α β p) := by
  rw [shiftedJacobiInner_positiveJacobiOperator_eq_derivative hα hβ]
  have hpos := shiftedJacobiMomentPairingBilinForm_posDef
    (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)
      p.derivative hp
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
    Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos

theorem positiveJacobiOperator_shiftedJacobiMonic
    (n : ℕ) (α β : ℝ) :
    positiveJacobiOperator α β (shiftedJacobiMonic n α β) =
      C (eigenvalue (α + β + 2) n) * shiftedJacobiMonic n α β := by
  have hraw :
      positiveJacobiOperator α β (shiftedJacobi n α β) =
        C (eigenvalue (α + β + 2) n) * shiftedJacobi n α β := by
    change -jacobiDifferentialOperator (α + 1) (α + β + 2)
        (shiftedJacobi n α β) = _
    rw [jacobiDifferentialOperator_shiftedJacobi]
    unfold eigenvalue
    simp only [map_neg, map_mul, neg_mul]
    ring_nf
  rw [shiftedJacobiMonic]
  rw [show positiveJacobiOperator α β (C _ * shiftedJacobi n α β) =
      C _ * positiveJacobiOperator α β (shiftedJacobi n α β) by
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul], hraw]
  ring

/-- The quasi-Jacobi nodal polynomial is an eigenpolynomial up to the single
preceding Jacobi direction. -/
theorem positiveJacobiOperator_quasiJacobiPolynomial
    (q : ℕ) (α β τ : ℝ) :
    positiveJacobiOperator α β (quasiJacobiPolynomial q α β τ) =
      C (eigenvalue (α + β + 2) q) *
          quasiJacobiPolynomial q α β τ +
        C (τ * (eigenvalue (α + β + 2) q -
          eigenvalue (α + β + 2) (q - 1))) *
            shiftedJacobiMonic (q - 1) α β := by
  rw [quasiJacobiPolynomial, map_sub,
    positiveJacobiOperator_shiftedJacobiMonic]
  rw [show positiveJacobiOperator α β
      (C τ * shiftedJacobiMonic (q - 1) α β) =
      C τ * positiveJacobiOperator α β
        (shiftedJacobiMonic (q - 1) α β) by
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul],
    positiveJacobiOperator_shiftedJacobiMonic]
  simp only [map_mul, map_sub]
  ring

/-- At a root of the quasi-Jacobi polynomial, the positive Jacobi operator
has only the preceding-eigenvector residual. -/
theorem eval_positiveJacobiOperator_quasiJacobiPolynomial_at_root
    {q : ℕ} {α β τ t : ℝ}
    (ht : (quasiJacobiPolynomial q α β τ).IsRoot t) :
    (positiveJacobiOperator α β
        (quasiJacobiPolynomial q α β τ)).eval t =
      τ * (eigenvalue (α + β + 2) q -
          eigenvalue (α + β + 2) (q - 1)) *
        (shiftedJacobiMonic (q - 1) α β).eval t := by
  rw [positiveJacobiOperator_quasiJacobiPolynomial, eval_add,
    eval_mul, eval_C, ht.eq_zero, mul_zero, zero_add, eval_mul, eval_C]

/-- The evaluation vectors of the first `q` monic shifted-Jacobi polynomials
are explicit eigenvectors of the positive collocation matrix. -/
theorem collocationMatrix_mulVec_shiftedJacobiMonic {q n : ℕ}
    (hn : n < q) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ)
    (hx : Function.Injective x) :
    (Lagrange.collocationMatrix (positiveJacobiOperator α β) x).mulVec
        (fun j => (shiftedJacobiMonic n α β).eval (x j)) =
      eigenvalue (α + β + 2) n •
        (fun j => (shiftedJacobiMonic n α β).eval (x j)) := by
  rw [Lagrange.collocationMatrix_mulVec_eval _ x hx]
  · funext i
    rw [positiveJacobiOperator_shiftedJacobiMonic, eval_mul, eval_C]
    rfl
  · rw [natDegree_shiftedJacobiMonic n hα hβ]
    exact hn

end RealRooted.JacobiDeformation
