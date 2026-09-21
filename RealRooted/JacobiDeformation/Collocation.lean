import RealRooted.JacobiDeformation.Quadrature
import RealRooted.JacobiDeformation.Kernel
import RealRooted.Mathlib.LinearAlgebra.Matrix.RankOneCompression

/-!
# Weighted self-adjointness of finite collocation matrices

This file turns exact positive quadrature into the matrix symmetry needed in
the quasi-Jacobi argument.  It is stated for an arbitrary degree-preserving
self-adjoint polynomial operator, so the differential-operator calculation
can be supplied separately.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Matrix of a polynomial endomorphism in Lagrange evaluation coordinates. -/
def collocationMatrix {q : ℕ} (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (D (Lagrange.basis Finset.univ x j)).eval (x i)

/-- Exact quadrature isolates one row of the collocation matrix when paired
with a Lagrange cardinal polynomial. -/
theorem quadrature_cardinal_operator {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    (hD : ∀ p : ℝ[X], p.natDegree < q → (D p).natDegree < q)
    (i j : Fin q) :
    L (Lagrange.basis Finset.univ x i *
        D (Lagrange.basis Finset.univ x j)) =
      quadratureWeight L x i * collocationMatrix D x i j := by
  let bi := Lagrange.basis Finset.univ x i
  let bj := Lagrange.basis Finset.univ x j
  have hbideg : bi.natDegree = q - 1 := by
    simpa [bi] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hbjdeg : bj.natDegree = q - 1 := by
    simpa [bj] using Lagrange.natDegree_basis hx.injOn (mem_univ j)
  have hDjdeg : (D bj).natDegree < q := hD bj (by lia)
  have hproddeg : (bi * D bj).natDegree ≤ 2 * q - 2 := by
    calc
      (bi * D bj).natDegree ≤ bi.natDegree + (D bj).natDegree := natDegree_mul_le
      _ ≤ (q - 1) + (q - 1) := by rw [hbideg]; lia
      _ = 2 * q - 2 := by lia
  rw [quadrature_exact hq L x hx horth hproddeg]
  calc
    (∑ k : Fin q,
        quadratureWeight L x k * (bi * D bj).eval (x k)) =
        quadratureWeight L x i * (bi * D bj).eval (x i) := by
      apply Fintype.sum_eq_single i
      intro k hki
      rw [eval_mul, show bi.eval (x k) = 0 by
        exact Lagrange.eval_basis_of_ne hki.symm (mem_univ k), zero_mul, mul_zero]
    _ = quadratureWeight L x i * collocationMatrix D x i j := by
      rw [eval_mul, show bi.eval (x i) = 1 by
        exact Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      simp [bj, collocationMatrix]

/-- Self-adjointness of the polynomial operator becomes weighted symmetry of
its collocation matrix. -/
theorem quadratureWeight_mul_collocationMatrix_comm {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    (hD : ∀ p : ℝ[X], p.natDegree < q → (D p).natDegree < q)
    (hadj : ∀ p r : ℝ[X], L (p * D r) = L (D p * r))
    (i j : Fin q) :
    quadratureWeight L x i * collocationMatrix D x i j =
      quadratureWeight L x j * collocationMatrix D x j i := by
  rw [← quadrature_cardinal_operator hq L D x hx horth hD i j,
    ← quadrature_cardinal_operator hq L D x hx horth hD j i,
    hadj, mul_comm]

/-- Positive diagonal similarity which removes the quadrature weights from a
weighted-self-adjoint collocation matrix. -/
def symmetrizedCollocationMatrix {q : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ)
    (D : ℝ[X] →ₗ[ℝ] ℝ[X]) (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => Real.sqrt (quadratureWeight L x i) /
    Real.sqrt (quadratureWeight L x j) * collocationMatrix D x i j

theorem symmetrizedCollocationMatrix_isSymm {q : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ)
    (hweight : ∀ i, 0 < quadratureWeight L x i)
    (hweighted : ∀ i j,
      quadratureWeight L x i * collocationMatrix D x i j =
        quadratureWeight L x j * collocationMatrix D x j i) :
    (symmetrizedCollocationMatrix L D x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have hi := hweight i
  have hj := hweight j
  have hsqrti : Real.sqrt (quadratureWeight L x i) ≠ 0 :=
    (Real.sqrt_pos.2 hi).ne'
  have hsqrtj : Real.sqrt (quadratureWeight L x j) ≠ 0 :=
    (Real.sqrt_pos.2 hj).ne'
  rw [symmetrizedCollocationMatrix, symmetrizedCollocationMatrix]
  field_simp [hsqrti, hsqrtj]
  rw [Real.sq_sqrt hi.le, Real.sq_sqrt hj.le]
  exact (hweighted i j).symm

/-! ## Shifted-Jacobi differential collocation -/

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
    ring
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
          (jacobiDifferentialOperator (α + 1) (α + β + 2) p * r) := by
    exact hsymm.symm
  have hneg (f : ℝ[X]) :
      shiftedJacobiFunctional α β (-f) = -shiftedJacobiFunctional α β f := by
    exact (Polynomial.momentFunctionalLinearMap
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

/-- Evaluation vectors intertwine a polynomial operator with its collocation
matrix on degrees below the number of nodes. -/
theorem collocationMatrix_mulVec_eval {q : ℕ}
    (D : ℝ[X] →ₗ[ℝ] ℝ[X]) (x : Fin q → ℝ)
    (hx : Function.Injective x) (p : ℝ[X]) (hp : p.natDegree < q) :
    (collocationMatrix D x).mulVec (fun j => p.eval (x j)) =
      fun i => (D p).eval (x i) := by
  funext i
  have hpdeg : p.degree < (#(Finset.univ : Finset (Fin q)) : WithBot ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    simpa using hp
  have hinterp := Lagrange.eq_interpolate hx.injOn
    (f := p) hpdeg
  have heval := congrArg (fun r : ℝ[X] => (D r).eval (x i)) hinterp
  rw [Lagrange.interpolate_apply, map_sum, eval_finsetSum] at heval
  rw [Matrix.mulVec]
  change (∑ j, (D (Lagrange.basis Finset.univ x j)).eval (x i) *
    p.eval (x j)) = (D p).eval (x i)
  rw [heval]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_eq_C_mul, map_smul]
  simp only [eval_smul, smul_eq_mul]
  ring

/-- The evaluation vectors of the first `q` monic shifted-Jacobi polynomials
are explicit eigenvectors of the positive collocation matrix. -/
theorem collocationMatrix_mulVec_shiftedJacobiMonic {q n : ℕ}
    (hn : n < q) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ)
    (hx : Function.Injective x) :
    (collocationMatrix (positiveJacobiOperator α β) x).mulVec
        (fun j => (shiftedJacobiMonic n α β).eval (x j)) =
      eigenvalue (α + β + 2) n •
        (fun j => (shiftedJacobiMonic n α β).eval (x j)) := by
  rw [collocationMatrix_mulVec_eval _ x hx]
  · funext i
    rw [positiveJacobiOperator_shiftedJacobiMonic, eval_mul, eval_C]
    rfl
  · rw [natDegree_shiftedJacobiMonic n hα hβ]
    exact hn

/-! ## Off-diagonal cardinal derivatives -/

/-- At a different node, the first derivative of a Lagrange cardinal
polynomial is the quotient of the two nodal derivatives. -/
theorem eval_derivative_lagrangeBasis_of_ne {q : ℕ}
    (x : Fin q → ℝ) (hx : Function.Injective x)
    {i j : Fin q} (hij : i ≠ j) :
    (Lagrange.basis Finset.univ x j).derivative.eval (x i) =
      (Lagrange.nodal Finset.univ x).derivative.eval (x i) /
        ((x i - x j) *
          (Lagrange.nodal Finset.univ x).derivative.eval (x j)) := by
  let v := Lagrange.nodal Finset.univ x
  let r := Lagrange.nodal (Finset.univ.erase j) x
  let b := Lagrange.basis Finset.univ x j
  let di := v.derivative.eval (x i)
  let dj := v.derivative.eval (x j)
  have hsub : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hdj : dj ≠ 0 := eval_derivative_nodal_ne_zero x hx j
  have hri : r.eval (x i) = 0 := by
    apply Lagrange.eval_nodal_at_node
    exact Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  have hv : v = (X - C (x j)) * r := by
    exact Lagrange.nodal_eq_mul_nodal_erase (mem_univ j)
  have hdi : di = (x i - x j) * r.derivative.eval (x i) := by
    dsimp only [di]
    rw [hv, derivative_mul]
    simp only [eval_add, eval_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_sub, eval_X, eval_C, hri,
      one_mul, zero_add]
  have hb : b = C dj⁻¹ * r := by
    rw [show b = C (Lagrange.nodalWeight Finset.univ x j) * r by
      dsimp only [b, r]
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ j),
        ← Lagrange.nodal_erase_eq_nodal_div (mem_univ j)]]
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j)]
  rw [show (Lagrange.basis Finset.univ x j).derivative.eval (x i) =
      dj⁻¹ * r.derivative.eval (x i) by
    change b.derivative.eval (x i) = _
    rw [hb, derivative_C_mul, eval_mul, eval_C]]
  change dj⁻¹ * r.derivative.eval (x i) = di / ((x i - x j) * dj)
  field_simp [hsub, hdj]
  nlinarith [hdi]

/-- At a different node, the second cardinal derivative is determined by the
first and second derivatives of the nodal polynomial. -/
theorem eval_secondDerivative_lagrangeBasis_of_ne {q : ℕ}
    (x : Fin q → ℝ) (hx : Function.Injective x)
    {i j : Fin q} (hij : i ≠ j) :
    (Lagrange.basis Finset.univ x j).derivative.derivative.eval (x i) =
      ((Lagrange.nodal Finset.univ x).derivative.derivative.eval (x i) -
          2 * (Lagrange.nodal Finset.univ x).derivative.eval (x i) /
            (x i - x j)) /
        ((x i - x j) *
          (Lagrange.nodal Finset.univ x).derivative.eval (x j)) := by
  let v := Lagrange.nodal Finset.univ x
  let r := Lagrange.nodal (Finset.univ.erase j) x
  let b := Lagrange.basis Finset.univ x j
  let di := v.derivative.eval (x i)
  let dj := v.derivative.eval (x j)
  have hsub : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hdj : dj ≠ 0 := eval_derivative_nodal_ne_zero x hx j
  have hri : r.eval (x i) = 0 := by
    apply Lagrange.eval_nodal_at_node
    exact Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  have hv : v = (X - C (x j)) * r := by
    exact Lagrange.nodal_eq_mul_nodal_erase (mem_univ j)
  have hdi : di = (x i - x j) * r.derivative.eval (x i) := by
    dsimp only [di]
    rw [hv, derivative_mul]
    simp only [eval_add, eval_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_sub, eval_X, eval_C, hri,
      one_mul, zero_add]
  have hddi : v.derivative.derivative.eval (x i) =
      2 * r.derivative.eval (x i) +
        (x i - x j) * r.derivative.derivative.eval (x i) := by
    rw [hv, derivative_mul, derivative_add, derivative_mul, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero,
      derivative_one, zero_mul, zero_add, eval_add, eval_mul, eval_one,
      eval_sub, eval_X, eval_C]
    ring
  have hsecond : r.derivative.derivative.eval (x i) * (x i - x j) ^ 2 =
      v.derivative.derivative.eval (x i) * (x i - x j) - 2 * di := by
    linear_combination -(x i - x j) * hddi + 2 * hdi
  have hb : b = C dj⁻¹ * r := by
    rw [show b = C (Lagrange.nodalWeight Finset.univ x j) * r by
      dsimp only [b, r]
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ j),
        ← Lagrange.nodal_erase_eq_nodal_div (mem_univ j)]]
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j)]
  rw [show (Lagrange.basis Finset.univ x j).derivative.derivative.eval (x i) =
      dj⁻¹ * r.derivative.derivative.eval (x i) by
    change b.derivative.derivative.eval (x i) = _
    rw [hb, derivative_C_mul, derivative_C_mul, eval_mul, eval_C]]
  change dj⁻¹ * r.derivative.derivative.eval (x i) =
    (v.derivative.derivative.eval (x i) - 2 * di / (x i - x j)) /
      ((x i - x j) * dj)
  field_simp [hsub, hdj]
  nlinarith [hsecond]

/-- Explicit off-diagonal quasi-Jacobi collocation formula.  The first term
is the rank-one residual and the second is the differential cardinal term. -/
theorem shiftedJacobi_collocationMatrix_offdiag
    {q : ℕ} {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j) :
    collocationMatrix (positiveJacobiOperator α β) x i j =
      τ * (eigenvalue (α + β + 2) q -
          eigenvalue (α + β + 2) (q - 1)) *
        (shiftedJacobiMonic (q - 1) α β).eval (x i) /
          ((x i - x j) *
            (quasiJacobiPolynomial q α β τ).derivative.eval (x j)) +
      2 * (x i * (1 - x i)) *
        (quasiJacobiPolynomial q α β τ).derivative.eval (x i) /
          ((x i - x j) ^ 2 *
            (quasiJacobiPolynomial q α β τ).derivative.eval (x j)) := by
  let v := Lagrange.nodal Finset.univ x
  let p := shiftedJacobiMonic (q - 1) α β
  let d := fun k ↦ v.derivative.eval (x k)
  let s := x i - x j
  let σ := x i * (1 - x i)
  let ρ := α + 1 - (α + β + 2) * x i
  let e := τ * (eigenvalue (α + β + 2) q -
    eigenvalue (α + β + 2) (q - 1))
  have hv : v = quasiJacobiPolynomial q α β τ :=
    nodal_eq_quasiJacobiPolynomial (by have := i.isLt; lia)
      hα hβ x hx hroot
  have hs : s ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hdj : d j ≠ 0 := eval_derivative_nodal_ne_zero x hx j
  have hb1 := eval_derivative_lagrangeBasis_of_ne x hx hij
  change (Lagrange.basis Finset.univ x j).derivative.eval (x i) =
    d i / (s * d j) at hb1
  have hb2 := eval_secondDerivative_lagrangeBasis_of_ne x hx hij
  change (Lagrange.basis Finset.univ x j).derivative.derivative.eval (x i) =
    (v.derivative.derivative.eval (x i) - 2 * d i / s) / (s * d j) at hb2
  have hdiff :
      -(σ * v.derivative.derivative.eval (x i) + ρ * d i) =
        e * p.eval (x i) := by
    calc
      -(σ * v.derivative.derivative.eval (x i) + ρ * d i) =
          (positiveJacobiOperator α β v).eval (x i) := by
        symm
        exact eval_positiveJacobiOperator α β (x i) v
      _ = (positiveJacobiOperator α β
          (quasiJacobiPolynomial q α β τ)).eval (x i) := by rw [hv]
      _ = e * p.eval (x i) := by
        exact eval_positiveJacobiOperator_quasiJacobiPolynomial_at_root (hroot i)
  rw [collocationMatrix, eval_positiveJacobiOperator, hb1, hb2]
  rw [← hv]
  change -(σ * ((v.derivative.derivative.eval (x i) - 2 * d i / s) /
      (s * d j)) + ρ * (d i / (s * d j))) =
    e * p.eval (x i) / (s * d j) +
      2 * σ * d i / (s ^ 2 * d j)
  field_simp [hs, hdj]
  linear_combination s * hdiff

/-- Signed diagonal scale from the quasi-Jacobi proof. -/
def quasiJacobiCollocationScale (q : ℕ) (α β τ : ℝ)
    (x : Fin q → ℝ) (i : Fin q) : ℝ :=
  Real.sqrt (quasiJacobiEta q α β τ x i) *
    (shiftedJacobiMonic (q - 1) α β).eval (x i)

/-- The signed diagonal similarity `R⁻¹ D R` used for entrywise
positivity. -/
def quasiJacobiCollocationMatrix (q : ℕ) (α β τ : ℝ)
    (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j ↦ quasiJacobiCollocationScale q α β τ x j /
    quasiJacobiCollocationScale q α β τ x i *
      collocationMatrix (positiveJacobiOperator α β) x i j

theorem quasiJacobiCollocationScale_ne_zero
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    quasiJacobiCollocationScale q α β τ x i ≠ 0 := by
  apply mul_ne_zero
  · exact (Real.sqrt_pos.2
      (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i)).ne'
  · exact shiftedJacobiMonic_eval_prev_ne_zero_of_roots
      hq hα hβ x hx hroot i

/-- The quadrature weight times the squared signed scale is independent of
the node and equals the preceding Jacobi squared norm. -/
theorem quadratureWeight_mul_quasiJacobiCollocationScale_sq
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        quasiJacobiCollocationScale q α β τ x i ^ 2 =
      shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
  let d := (quasiJacobiPolynomial q α β τ).derivative.eval (x i)
  let p := (shiftedJacobiMonic (q - 1) α β).eval (x i)
  let w := quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
  have heta : 0 < quasiJacobiEta q α β τ x i :=
    quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hp : p ≠ 0 := shiftedJacobiMonic_eval_prev_ne_zero_of_roots
    hq hα hβ x hx hroot i
  have hid := shiftedJacobi_derivative_mul_quadratureWeight_mul_eval_prev
    hq hα hβ x hx hroot i
  change w * (Real.sqrt (quasiJacobiEta q α β τ x i) * p) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt heta.le]
  change w * (d / p * p ^ 2) = _
  field_simp [hp]
  nlinarith [hid]

/-- Weighted self-adjointness of positive-Jacobi collocation at explicit
distinct quasi-Jacobi roots. -/
theorem shiftedJacobi_weighted_collocation_comm {q : ℕ} (hq : 2 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i j : Fin q) :
    quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        collocationMatrix (positiveJacobiOperator α β) x i j =
      quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j *
        collocationMatrix (positiveJacobiOperator α β) x j i := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  apply quadratureWeight_mul_collocationMatrix_comm hq L
    (positiveJacobiOperator α β) x hx
  · intro g hg
    change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
    rw [nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot]
    exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg
  · exact positiveJacobiOperator_natDegree_lt α β
  · exact shiftedJacobiFunctional_mul_positiveJacobiOperator_comm hα hβ

/-- The signed quasi-Jacobi collocation similarity is symmetric. -/
theorem quasiJacobiCollocationMatrix_isSymm
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    (quasiJacobiCollocationMatrix q α β τ x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  let w := fun k ↦ quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x k
  let r := quasiJacobiCollocationScale q α β τ x
  let D := collocationMatrix (positiveJacobiOperator α β) x
  have hwi : w i ≠ 0 := (shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i).ne'
  have hri : r i ≠ 0 :=
    quasiJacobiCollocationScale_ne_zero hq hα hβ x hx hroot i
  have hrj : r j ≠ 0 :=
    quasiJacobiCollocationScale_ne_zero hq hα hβ x hx hroot j
  have hweighted : w i * D i j = w j * D j i :=
    shiftedJacobi_weighted_collocation_comm hq hα hβ x hx hroot i j
  have hscale : w i * r i ^ 2 = w j * r j ^ 2 := by
    rw [quadratureWeight_mul_quasiJacobiCollocationScale_sq
        hq hα hβ x hx hroot i,
      quadratureWeight_mul_quasiJacobiCollocationScale_sq
        hq hα hβ x hx hroot j]
  have hcross : r j ^ 2 * D i j = r i ^ 2 * D j i := by
    have hwcross : w i * (r j ^ 2 * D i j - r i ^ 2 * D j i) = 0 := by
      linear_combination r j ^ 2 * hweighted - D j i * hscale
    exact sub_eq_zero.mp ((mul_eq_zero.mp hwcross).resolve_left hwi)
  change r i / r j * D j i = r j / r i * D i j
  field_simp [hri, hrj]
  nlinarith [hcross]

/-- Before symmetrizing the numerator, the signed off-diagonal entry is the
sum of the local differential term and the rank-one residual. -/
theorem quasiJacobiCollocationMatrix_offdiag_raw
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j) :
    quasiJacobiCollocationMatrix q α β τ x i j =
      (2 * (x i * (1 - x i)) * quasiJacobiEta q α β τ x i +
        τ * (eigenvalue (α + β + 2) q -
          eigenvalue (α + β + 2) (q - 1)) * (x i - x j)) /
        ((x i - x j) ^ 2 *
          Real.sqrt (quasiJacobiEta q α β τ x i) *
          Real.sqrt (quasiJacobiEta q α β τ x j)) := by
  let ηi := quasiJacobiEta q α β τ x i
  let ηj := quasiJacobiEta q α β τ x j
  let yi := Real.sqrt ηi
  let yj := Real.sqrt ηj
  let pi := (shiftedJacobiMonic (q - 1) α β).eval (x i)
  let pj := (shiftedJacobiMonic (q - 1) α β).eval (x j)
  let di := (quasiJacobiPolynomial q α β τ).derivative.eval (x i)
  let dj := (quasiJacobiPolynomial q α β τ).derivative.eval (x j)
  let s := x i - x j
  let e := τ * (eigenvalue (α + β + 2) q -
    eigenvalue (α + β + 2) (q - 1))
  have hηi : 0 < ηi := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hηj : 0 < ηj := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j
  have hyi : yi ≠ 0 := (Real.sqrt_pos.2 hηi).ne'
  have hyj : yj ≠ 0 := (Real.sqrt_pos.2 hηj).ne'
  have hpi : pi ≠ 0 := shiftedJacobiMonic_eval_prev_ne_zero_of_roots
    hq hα hβ x hx hroot i
  have hpj : pj ≠ 0 := shiftedJacobiMonic_eval_prev_ne_zero_of_roots
    hq hα hβ x hx hroot j
  have hs : s ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hdi : di = ηi * pi := by
    change di = di / pi * pi
    field_simp [hpi]
  have hdj : dj = ηj * pj := by
    change dj = dj / pj * pj
    field_simp [hpj]
  have hyi2 : ηi = yi ^ 2 := (Real.sq_sqrt hηi.le).symm
  have hyj2 : ηj = yj ^ 2 := (Real.sq_sqrt hηj.le).symm
  rw [quasiJacobiCollocationMatrix, quasiJacobiCollocationScale,
    shiftedJacobi_collocationMatrix_offdiag hα hβ x hx hroot hij]
  change yj * pj / (yi * pi) *
      (e * pi / (s * dj) + 2 * (x i * (1 - x i)) * di / (s ^ 2 * dj)) =
    (2 * (x i * (1 - x i)) * ηi + e * s) / (s ^ 2 * yi * yj)
  rw [hdi, hdj, hyi2, hyj2]
  field_simp [hs, hyi, hyj, hpi, hpj]
  ring

/-- Symmetry cancels the rank-one residual and gives formula (15). -/
theorem quasiJacobiCollocationMatrix_offdiag
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j) :
    quasiJacobiCollocationMatrix q α β τ x i j =
      ((x i * (1 - x i)) * quasiJacobiEta q α β τ x i +
        (x j * (1 - x j)) * quasiJacobiEta q α β τ x j) /
        ((x i - x j) ^ 2 *
          Real.sqrt (quasiJacobiEta q α β τ x i) *
          Real.sqrt (quasiJacobiEta q α β τ x j)) := by
  let A := quasiJacobiCollocationMatrix q α β τ x
  let η := quasiJacobiEta q α β τ x
  let e := τ * (eigenvalue (α + β + 2) q -
    eigenvalue (α + β + 2) (q - 1))
  let s := x i - x j
  have hηi : 0 < η i := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hηj : 0 < η j := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j
  have hyi : Real.sqrt (η i) ≠ 0 := (Real.sqrt_pos.2 hηi).ne'
  have hyj : Real.sqrt (η j) ≠ 0 := (Real.sqrt_pos.2 hηj).ne'
  have hs : s ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hsji : x j - x i ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h).symm)
  have hrawij := quasiJacobiCollocationMatrix_offdiag_raw
    hq hα hβ x hx hroot hij
  change A i j =
    (2 * (x i * (1 - x i)) * η i + e * s) /
      (s ^ 2 * Real.sqrt (η i) * Real.sqrt (η j)) at hrawij
  have hrawji := quasiJacobiCollocationMatrix_offdiag_raw
    hq hα hβ x hx hroot hij.symm
  change A j i =
    (2 * (x j * (1 - x j)) * η j + e * (x j - x i)) /
      ((x j - x i) ^ 2 * Real.sqrt (η j) * Real.sqrt (η i)) at hrawji
  have hsymm : A j i = A i j :=
    (quasiJacobiCollocationMatrix_isSymm hq hα hβ x hx hroot).apply i j
  change A i j =
    ((x i * (1 - x i)) * η i + (x j * (1 - x j)) * η j) /
      (s ^ 2 * Real.sqrt (η i) * Real.sqrt (η j))
  calc
    A i j = (A i j + A j i) / 2 := by rw [hsymm]; ring
    _ = ((2 * (x i * (1 - x i)) * η i + e * s) /
          (s ^ 2 * Real.sqrt (η i) * Real.sqrt (η j)) +
        (2 * (x j * (1 - x j)) * η j + e * (x j - x i)) /
          ((x j - x i) ^ 2 * Real.sqrt (η j) * Real.sqrt (η i))) / 2 := by
      rw [hrawij, hrawji]
    _ = ((x i * (1 - x i)) * η i + (x j * (1 - x j)) * η j) /
          (s ^ 2 * Real.sqrt (η i) * Real.sqrt (η j)) := by
      field_simp [hs, hsji, hyi, hyj]
      ring

theorem quasiJacobiCollocationMatrix_offdiag_pos_of_numerator
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j)
    (hnum : 0 <
      (x i * (1 - x i)) * quasiJacobiEta q α β τ x i +
        (x j * (1 - x j)) * quasiJacobiEta q α β τ x j) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  rw [quasiJacobiCollocationMatrix_offdiag hq hα hβ x hx hroot hij]
  apply div_pos hnum
  exact mul_pos
    (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (fun h ↦ hij (hx h))))
      (Real.sqrt_pos.2 (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i)))
    (Real.sqrt_pos.2 (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j))

/-- Formula (15) is strictly positive when both quasi-nodes are interior. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_mem_Ioo
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j)
    (hi : x i ∈ Set.Ioo (0 : ℝ) 1) (hj : x j ∈ Set.Ioo (0 : ℝ) 1) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  apply quasiJacobiCollocationMatrix_offdiag_pos_of_numerator
    hq hα hβ x hx hroot hij
  exact add_pos
    (mul_pos (mul_pos hi.1 (sub_pos.mpr hi.2))
      (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i))
    (mul_pos (mul_pos hj.1 (sub_pos.mpr hj.2))
      (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j))

/-! ## Two-point multiplication compression -/

/-- A Lagrange cardinal polynomial normalized to have unit squared norm for
the shifted-Jacobi moment pairing. -/
def normalizedJacobiCardinal {q : ℕ} (α β : ℝ) (x : Fin q → ℝ)
    (i : Fin q) : ℝ[X] :=
  C (Real.sqrt (quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))⁻¹ *
      Lagrange.basis Finset.univ x i

/-- Signed last-coordinate model for the rank-one quasi-Jacobi update.  Its
square is the inverse Christoffel ratio `quasiJacobiEta`. -/
def quasiJacobiCompressionCoordinate (q : ℕ) (α β τ : ℝ)
    (x : Fin q → ℝ) (i : Fin q) : ℝ :=
  Real.sqrt (shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
      (shiftedJacobiMonic (q - 1) α β)) /
    ((quasiJacobiPolynomial q α β τ).derivative.eval (x i) *
      Real.sqrt (quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))

/-- The compression of multiplication by `X` to two normalized cardinal
polynomials. -/
def quasiJacobiTwoPointCompression {q : ℕ} (α β : ℝ) (x : Fin q → ℝ)
    (i j : Fin q) : Matrix (Fin 2) (Fin 2) ℝ :=
  let ei := normalizedJacobiCardinal α β x i
  let ej := normalizedJacobiCardinal α β x j
  !![shiftedJacobiInner α β ei (X * ei),
      shiftedJacobiInner α β ei (X * ej);
    shiftedJacobiInner α β ej (X * ei),
      shiftedJacobiInner α β ej (X * ej)]

/-- The complementary compression, represented as multiplication by
`1 - X` on the same two normalized cardinal polynomials. -/
def quasiJacobiTwoPointComplement {q : ℕ} (α β : ℝ) (x : Fin q → ℝ)
    (i j : Fin q) : Matrix (Fin 2) (Fin 2) ℝ :=
  let ei := normalizedJacobiCardinal α β x i
  let ej := normalizedJacobiCardinal α β x j
  !![shiftedJacobiInner α β ei ((1 - X) * ei),
      shiftedJacobiInner α β ei ((1 - X) * ej);
    shiftedJacobiInner α β ej ((1 - X) * ei),
      shiftedJacobiInner α β ej ((1 - X) * ej)]

/-- The cardinal polynomials are orthogonal for the exact quasi-Jacobi
quadrature, with squared norms equal to their quadrature weights. -/
theorem shiftedJacobiInner_lagrangeBasis
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i j : Fin q) :
    shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
        (Lagrange.basis Finset.univ x j) =
      if i = j then
        quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
      else 0 := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  let bi := Lagrange.basis Finset.univ x i
  let bj := Lagrange.basis Finset.univ x j
  have hbjdeg : bj.natDegree < q := by
    rw [show bj.natDegree = q - 1 by
      simpa [bj] using Lagrange.natDegree_basis hx.injOn (mem_univ j)]
    lia
  have hpair := quadratureWeight_mul_eval hq L x hx
    (fun g hg ↦ by
      change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
      rw [nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot]
      exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg)
    bj hbjdeg i
  change quadratureWeight L x i * bj.eval (x i) =
    shiftedJacobiInner α β bi bj at hpair
  rw [← hpair]
  by_cases hij : i = j
  · subst j
    simp [bj, L, Lagrange.eval_basis_self hx.injOn (mem_univ i)]
  · rw [ite_eq_right hij,
      Lagrange.eval_basis_of_ne (Ne.symm hij) (mem_univ i), mul_zero]

theorem shiftedJacobiInner_normalizedJacobiCardinal
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i j : Fin q) :
    shiftedJacobiInner α β (normalizedJacobiCardinal α β x i)
        (normalizedJacobiCardinal α β x j) = if i = j then 1 else 0 := by
  have hwi := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i
  rw [normalizedJacobiCardinal, normalizedJacobiCardinal,
    shiftedJacobiInner_C_mul_left, shiftedJacobiInner_C_mul_right,
    shiftedJacobiInner_lagrangeBasis hq hα hβ x hx hroot]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    field_simp [(Real.sqrt_pos.2 hwi).ne']
    simpa using (Real.sq_sqrt hwi.le).symm
  · simp [hij]

/-- The nodal derivative clears the sole quasi-Jacobi correction in the
pairing of a cardinal polynomial with the nodal polynomial. -/
theorem shiftedJacobi_derivative_mul_inner_basis_quasi
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i : Fin q) :
    (quasiJacobiPolynomial q α β τ).derivative.eval (x i) *
        shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
          (quasiJacobiPolynomial q α β τ) =
      -τ * shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
  have hdeg : (Lagrange.basis Finset.univ x i).natDegree < q := by
    rw [Lagrange.natDegree_basis hx.injOn (mem_univ i)]
    simp
    lia
  have hqzero :
      shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
        (shiftedJacobiMonic q α β) = 0 := by
    rw [shiftedJacobiInner_comm]
    exact shiftedJacobiMonicInner_eq_zero hα hβ _ hdeg
  have hbase := shiftedJacobi_eval_derivative_nodal_mul_inner_basis
    hq hα hβ x hx i
  have hnodal := nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot
  rw [hnodal] at hbase
  have hinner :
      shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
          (quasiJacobiPolynomial q α β τ) =
        -τ * shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
          (shiftedJacobiMonic (q - 1) α β) := by
    rw [quasiJacobiPolynomial, shiftedJacobiInner_sub_right,
      shiftedJacobiInner_C_mul_right, hqzero, zero_sub]
    ring
  rw [hinner]
  calc
    _ = -τ * ((quasiJacobiPolynomial q α β τ).derivative.eval (x i) *
        shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
          (shiftedJacobiMonic (q - 1) α β)) := by ring
    _ = _ := by rw [hbase]

/-- Matrix entries of the multiplication compression have the diagonal
minus rank-one form dictated by the quasi-Jacobi nodal polynomial. -/
theorem shiftedJacobiInner_normalizedCardinal_mul_X
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i j : Fin q) :
    shiftedJacobiInner α β (normalizedJacobiCardinal α β x i)
        (X * normalizedJacobiCardinal α β x j) =
      (if i = j then x j else 0) - τ *
        quasiJacobiCompressionCoordinate q α β τ x i *
        quasiJacobiCompressionCoordinate q α β τ x j := by
  let bi := Lagrange.basis Finset.univ x i
  let bj := Lagrange.basis Finset.univ x j
  let wi := quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
  let wj := quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j
  let di := (quasiJacobiPolynomial q α β τ).derivative.eval (x i)
  let dj := (quasiJacobiPolynomial q α β τ).derivative.eval (x j)
  let N := shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
    (shiftedJacobiMonic (q - 1) α β)
  have hwi : 0 < wi := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i
  have hwj : 0 < wj := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot j
  have hnodal := nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot
  have hdi : di ≠ 0 := by
    change (quasiJacobiPolynomial q α β τ).derivative.eval (x i) ≠ 0
    rw [← hnodal]
    exact eval_derivative_nodal_ne_zero x hx i
  have hdj : dj ≠ 0 := by
    change (quasiJacobiPolynomial q α β τ).derivative.eval (x j) ≠ 0
    rw [← hnodal]
    exact eval_derivative_nodal_ne_zero x hx j
  have hN : 0 < N := by
    have hpmono :=
      (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).isMonicOfDegree
        (q - 1)
    have hpos := shiftedJacobiMomentPairingBilinForm_posDef hα hβ
      (shiftedJacobiMonic (q - 1) α β) hpmono.monic.ne_zero
    simpa only [N, LinearMap.BilinMap.toQuadraticMap_apply,
      Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos
  have hsi : Real.sqrt wi ≠ 0 := (Real.sqrt_pos.2 hwi).ne'
  have hsj : Real.sqrt wj ≠ 0 := (Real.sqrt_pos.2 hwj).ne'
  have hsN : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  have haction := X_mul_lagrangeBasis x j
  rw [hnodal] at haction
  have hpair := shiftedJacobi_derivative_mul_inner_basis_quasi
    hq hα hβ x hx hroot i
  change di * shiftedJacobiInner α β bi (quasiJacobiPolynomial q α β τ) =
    -τ * N at hpair
  have horth := shiftedJacobiInner_lagrangeBasis hq hα hβ x hx hroot i j
  change shiftedJacobiInner α β bi bj = if i = j then wi else 0 at horth
  change shiftedJacobiInner α β
      (C (Real.sqrt wi)⁻¹ * bi) (X * (C (Real.sqrt wj)⁻¹ * bj)) = _
  rw [show X * (C (Real.sqrt wj)⁻¹ * bj) =
      C (Real.sqrt wj)⁻¹ * (X * bj) by ring,
    shiftedJacobiInner_C_mul_left, shiftedJacobiInner_C_mul_right, haction,
    shiftedJacobiInner_add_right, shiftedJacobiInner_C_mul_right,
    shiftedJacobiInner_C_mul_right, horth]
  change (Real.sqrt wi)⁻¹ * ((Real.sqrt wj)⁻¹ *
      ((x j) * (if i = j then wi else 0) + dj⁻¹ *
        shiftedJacobiInner α β bi (quasiJacobiPolynomial q α β τ))) =
    (if i = j then x j else 0) - τ *
      (Real.sqrt N / (di * Real.sqrt wi)) *
      (Real.sqrt N / (dj * Real.sqrt wj))
  rw [show shiftedJacobiInner α β bi (quasiJacobiPolynomial q α β τ) =
      -τ * N / di by
    apply (eq_div_iff hdi).2
    simpa [mul_comm] using hpair]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    change (Real.sqrt wi)⁻¹ * ((Real.sqrt wi)⁻¹ *
        (x i * wi + di⁻¹ * (-τ * N / di))) =
      x i - τ * (Real.sqrt N / (di * Real.sqrt wi)) *
        (Real.sqrt N / (di * Real.sqrt wi))
    field_simp [hdi, hsi]
    rw [Real.sq_sqrt hwi.le, hsN]
    ring
  · simp only [ite_false, hij, mul_zero, zero_add]
    rw [zero_sub]
    change (Real.sqrt wi)⁻¹ * ((Real.sqrt wj)⁻¹ *
        (dj⁻¹ * (-τ * N / di))) =
      -(τ * (Real.sqrt N / (di * Real.sqrt wi)) *
        (Real.sqrt N / (dj * Real.sqrt wj)))
    field_simp [hdi, hdj, hsi, hsj]
    rw [hsN]

/-- The abstract Gram compression is exactly the explicit diagonal
rank-one compression used by the exterior-node determinant identity. -/
theorem quasiJacobiTwoPointCompression_eq_rankOne
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j) :
    quasiJacobiTwoPointCompression α β x i j =
      Matrix.twoPointRankOneCompression (x i) (x j) τ
        (quasiJacobiCompressionCoordinate q α β τ x i)
        (quasiJacobiCompressionCoordinate q α β τ x j) := by
  apply Matrix.ext
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [quasiJacobiTwoPointCompression, Matrix.twoPointRankOneCompression,
      shiftedJacobiInner_normalizedCardinal_mul_X hq hα hβ x hx hroot,
      hij, Ne.symm hij]

/-- The squared signed compression coordinate is the inverse Christoffel
ratio appearing in formula (15). -/
theorem quasiJacobiCompressionCoordinate_sq
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i : Fin q) :
    quasiJacobiCompressionCoordinate q α β τ x i ^ 2 =
      (quasiJacobiEta q α β τ x i)⁻¹ := by
  let d := (quasiJacobiPolynomial q α β τ).derivative.eval (x i)
  let p := (shiftedJacobiMonic (q - 1) α β).eval (x i)
  let w := quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
  let N := shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
    (shiftedJacobiMonic (q - 1) α β)
  have hw : 0 < w := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i
  have hp : p ≠ 0 := shiftedJacobiMonic_eval_prev_ne_zero_of_roots
    hq hα hβ x hx hroot i
  have hnodal := nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot
  have hd : d ≠ 0 := by
    change (quasiJacobiPolynomial q α β τ).derivative.eval (x i) ≠ 0
    rw [← hnodal]
    exact eval_derivative_nodal_ne_zero x hx i
  have hN : 0 < N := by
    have hpmono :=
      (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).isMonicOfDegree
        (q - 1)
    have hpos := shiftedJacobiMomentPairingBilinForm_posDef hα hβ
      (shiftedJacobiMonic (q - 1) α β) hpmono.monic.ne_zero
    simpa only [N, LinearMap.BilinMap.toQuadraticMap_apply,
      Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos
  have hid := shiftedJacobi_derivative_mul_quadratureWeight_mul_eval_prev
    hq hα hβ x hx hroot i
  change d * w * p = N at hid
  change (Real.sqrt N / (d * Real.sqrt w)) ^ 2 = (d / p)⁻¹
  have hsw : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  field_simp [hd, hp, hsw]
  nlinarith [Real.sq_sqrt hN.le, Real.sq_sqrt hw.le]

theorem shiftedJacobiInner_mul_X_comm (α β : ℝ) (p r : ℝ[X]) :
    shiftedJacobiInner α β p (X * r) =
      shiftedJacobiInner α β r (X * p) := by
  simp only [shiftedJacobiInner, Polynomial.momentPairing]
  congr 1
  ring

theorem shiftedJacobiInner_mul_one_sub_X_comm (α β : ℝ) (p r : ℝ[X]) :
    shiftedJacobiInner α β p ((1 - X) * r) =
      shiftedJacobiInner α β r ((1 - X) * p) := by
  simp only [shiftedJacobiInner, Polynomial.momentPairing]
  congr 1
  ring

/-- Distinct normalized cardinal polynomials give a positive-definite
two-point compression of multiplication by `X`. -/
theorem quasiJacobiTwoPointCompression_posDef
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j) :
    (quasiJacobiTwoPointCompression α β x i j).PosDef := by
  let ei := normalizedJacobiCardinal α β x i
  let ej := normalizedJacobiCardinal α β x j
  have hwi := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i
  have hwj := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot j
  have hsi : Real.sqrt (quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i) ≠ 0 :=
    (Real.sqrt_pos.2 hwi).ne'
  have hsj : Real.sqrt (quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j) ≠ 0 :=
    (Real.sqrt_pos.2 hwj).ne'
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · apply Matrix.IsHermitian.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [quasiJacobiTwoPointCompression,
        shiftedJacobiInner_mul_X_comm]
  · intro y hy
    let p := C (y 0) * ei + C (y 1) * ej
    have hp : p ≠ 0 := by
      intro hpzero
      have hi := congrArg (Polynomial.eval (x i)) hpzero
      have hj := congrArg (Polynomial.eval (x j)) hpzero
      have hei_i : ei.eval (x i) = (Real.sqrt (quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))⁻¹ := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      have hei_j : ei.eval (x j) = 0 := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij (mem_univ j)]
      have hej_i : ej.eval (x i) = 0 := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij.symm (mem_univ i)]
      have hej_j : ej.eval (x j) = (Real.sqrt (quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j))⁻¹ := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ j)]
      simp only [p, eval_add, eval_mul, eval_C, eval_zero,
        hei_i, hei_j, hej_i, hej_j, mul_zero, add_zero, zero_add] at hi hj
      have hyi : y 0 = 0 := by
        exact (mul_eq_zero.mp hi).resolve_right (inv_ne_zero hsi)
      have hyj : y 1 = 0 := by
        exact (mul_eq_zero.mp hj).resolve_right (inv_ne_zero hsj)
      apply hy
      funext a
      fin_cases a <;> assumption
    have hpositive := shiftedJacobiInner_mul_X_self_pos hα hβ hp
    have hXC (a : ℝ) (r : ℝ[X]) : X * (C a * r) = C a * (X * r) := by
      ring
    have hform :
        dotProduct (star y)
            (Matrix.mulVec (quasiJacobiTwoPointCompression α β x i j) y) =
          shiftedJacobiInner α β p (X * p) := by
      simp only [quasiJacobiTwoPointCompression, Matrix.cons_mulVec,
        Matrix.empty_mulVec, Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        add_zero, star_trivial]
      simp [Matrix.vecHead, Matrix.vecTail, p, ei, ej, mul_add, hXC,
        shiftedJacobiInner_add_left,
        shiftedJacobiInner_add_right, shiftedJacobiInner_C_mul_left,
        shiftedJacobiInner_C_mul_right]
      ring
    rwa [hform]

/-- The complementary two-point compression is also positive definite. -/
theorem quasiJacobiTwoPointComplement_posDef
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j) :
    (quasiJacobiTwoPointComplement α β x i j).PosDef := by
  let ei := normalizedJacobiCardinal α β x i
  let ej := normalizedJacobiCardinal α β x j
  have hwi := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i
  have hwj := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot j
  have hsi : Real.sqrt (quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i) ≠ 0 :=
    (Real.sqrt_pos.2 hwi).ne'
  have hsj : Real.sqrt (quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j) ≠ 0 :=
    (Real.sqrt_pos.2 hwj).ne'
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · apply Matrix.IsHermitian.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [quasiJacobiTwoPointComplement,
        shiftedJacobiInner_mul_one_sub_X_comm]
  · intro y hy
    let p := C (y 0) * ei + C (y 1) * ej
    have hp : p ≠ 0 := by
      intro hpzero
      have hi := congrArg (Polynomial.eval (x i)) hpzero
      have hj := congrArg (Polynomial.eval (x j)) hpzero
      have hei_i : ei.eval (x i) = (Real.sqrt (quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))⁻¹ := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      have hei_j : ei.eval (x j) = 0 := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij (mem_univ j)]
      have hej_i : ej.eval (x i) = 0 := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij.symm (mem_univ i)]
      have hej_j : ej.eval (x j) = (Real.sqrt (quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j))⁻¹ := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ j)]
      simp only [p, eval_add, eval_mul, eval_C, eval_zero,
        hei_i, hei_j, hej_i, hej_j, mul_zero, add_zero, zero_add] at hi hj
      have hyi : y 0 = 0 := by
        exact (mul_eq_zero.mp hi).resolve_right (inv_ne_zero hsi)
      have hyj : y 1 = 0 := by
        exact (mul_eq_zero.mp hj).resolve_right (inv_ne_zero hsj)
      apply hy
      funext a
      fin_cases a <;> assumption
    have hpositive := shiftedJacobiInner_mul_one_sub_X_self_pos hα hβ hp
    have hfactor (a : ℝ) (r : ℝ[X]) :
        (1 - X) * (C a * r) = C a * ((1 - X) * r) := by
      ring
    have hform :
        dotProduct (star y)
            (Matrix.mulVec (quasiJacobiTwoPointComplement α β x i j) y) =
          shiftedJacobiInner α β p ((1 - X) * p) := by
      simp only [quasiJacobiTwoPointComplement, Matrix.cons_mulVec,
        Matrix.empty_mulVec, Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty,
        add_zero, star_trivial]
      simp [Matrix.vecHead, Matrix.vecTail, p, ei, ej, mul_add, hfactor,
        shiftedJacobiInner_add_left, shiftedJacobiInner_add_right,
        shiftedJacobiInner_C_mul_left, shiftedJacobiInner_C_mul_right]
      ring
    rwa [hform]

/-- The complement Gram compression is literally `I - C`. -/
theorem quasiJacobiTwoPointComplement_eq_one_sub
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j) :
    quasiJacobiTwoPointComplement α β x i j =
      1 - quasiJacobiTwoPointCompression α β x i j := by
  apply Matrix.ext
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [quasiJacobiTwoPointComplement, quasiJacobiTwoPointCompression,
      sub_mul, shiftedJacobiInner_sub_right,
      shiftedJacobiInner_normalizedJacobiCardinal hq hα hβ x hx hroot,
      hij, Ne.symm hij]

/-- The checked two-point compression identity closes formula (15) when the
second quasi-node is on or beyond the right endpoint. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior_certificate
    {q : ℕ} (hq : 2 ≤ q) {α β τ detC detOneSubC : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j)
    (hi : x i ∈ Set.Ioo (0 : ℝ) 1) (hj : 1 ≤ x j)
    (hτ : 0 < τ) (hdetC : 0 < detC) (hdetOneSubC : 0 < detOneSubC)
    (hidentity :
      τ * ((quasiJacobiEta q α β τ x j)⁻¹ * x i * (1 - x i) +
        (quasiJacobiEta q α β τ x i)⁻¹ * x j * (1 - x j)) =
      x i * x j * detOneSubC -
        (1 - x i) * (1 - x j) * detC) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  have hηi := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hηj := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j
  have hscalar := Matrix.twoPointCompression_scalar_pos_of_right_exterior
    hi.1 hi.2 hj hτ (inv_pos.mpr hηi) (inv_pos.mpr hηj)
      hdetC hdetOneSubC hidentity
  apply quasiJacobiCollocationMatrix_offdiag_pos_of_numerator
    hq hα hβ x hx hroot hij
  simpa [div_inv_eq_mul, mul_assoc] using hscalar

/-- The checked two-point compression identity closes formula (15) when the
first quasi-node is on or beyond the left endpoint. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior_certificate
    {q : ℕ} (hq : 2 ≤ q) {α β τ detC detOneSubC : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j)
    (hi : x i ≤ 0) (hj : x j ∈ Set.Ioo (0 : ℝ) 1)
    (hτ : τ < 0) (hdetC : 0 < detC) (hdetOneSubC : 0 < detOneSubC)
    (hidentity :
      τ * ((quasiJacobiEta q α β τ x j)⁻¹ * x i * (1 - x i) +
        (quasiJacobiEta q α β τ x i)⁻¹ * x j * (1 - x j)) =
      x i * x j * detOneSubC -
        (1 - x i) * (1 - x j) * detC) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  have hηi := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hηj := quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j
  have hscalar := Matrix.twoPointCompression_scalar_pos_of_left_exterior
    hi hj.1 hj.2 hτ (inv_pos.mpr hηi) (inv_pos.mpr hηj)
      hdetC hdetOneSubC hidentity
  apply quasiJacobiCollocationMatrix_offdiag_pos_of_numerator
    hq hα hβ x hx hroot hij
  simpa [div_inv_eq_mul, mul_assoc] using hscalar

/-- Formula (15) is strictly positive for a right-exterior quasi-node.  The
finite multiplication compression supplies both positive determinants, so no
spectral or sign certificate remains as a hypothesis. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j)
    (hi : x i ∈ Set.Ioo (0 : ℝ) 1) (hj : 1 ≤ x j)
    (hτ : 0 < τ) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  let u := quasiJacobiCompressionCoordinate q α β τ x i
  let v := quasiJacobiCompressionCoordinate q α β τ x j
  let C := Matrix.twoPointRankOneCompression (x i) (x j) τ u v
  have hcompression := quasiJacobiTwoPointCompression_eq_rankOne
    hq hα hβ x hx hroot hij
  have hC : C.PosDef := by
    change (Matrix.twoPointRankOneCompression (x i) (x j) τ
      (quasiJacobiCompressionCoordinate q α β τ x i)
      (quasiJacobiCompressionCoordinate q α β τ x j)).PosDef
    rw [← hcompression]
    exact quasiJacobiTwoPointCompression_posDef hq hα hβ x hx hroot hij
  have hcomplement := quasiJacobiTwoPointComplement_posDef
    hq hα hβ x hx hroot hij
  rw [quasiJacobiTwoPointComplement_eq_one_sub hq hα hβ x hx hroot hij,
    hcompression] at hcomplement
  have hidentity := Matrix.twoPointRankOneCompression_det_identity
    (x i) (x j) τ u v
  rw [quasiJacobiCompressionCoordinate_sq hq hα hβ x hx hroot i,
    quasiJacobiCompressionCoordinate_sq hq hα hβ x hx hroot j] at hidentity
  exact quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior_certificate
    hq hα hβ x hx hroot hij hi hj hτ hC.det_pos hcomplement.det_pos hidentity

/-- Formula (15) is strictly positive for a left-exterior quasi-node, with
the finite multiplication compression discharging the determinant signs. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j)
    (hi : x i ≤ 0) (hj : x j ∈ Set.Ioo (0 : ℝ) 1)
    (hτ : τ < 0) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  let u := quasiJacobiCompressionCoordinate q α β τ x i
  let v := quasiJacobiCompressionCoordinate q α β τ x j
  let C := Matrix.twoPointRankOneCompression (x i) (x j) τ u v
  have hcompression := quasiJacobiTwoPointCompression_eq_rankOne
    hq hα hβ x hx hroot hij
  have hC : C.PosDef := by
    change (Matrix.twoPointRankOneCompression (x i) (x j) τ
      (quasiJacobiCompressionCoordinate q α β τ x i)
      (quasiJacobiCompressionCoordinate q α β τ x j)).PosDef
    rw [← hcompression]
    exact quasiJacobiTwoPointCompression_posDef hq hα hβ x hx hroot hij
  have hcomplement := quasiJacobiTwoPointComplement_posDef
    hq hα hβ x hx hroot hij
  rw [quasiJacobiTwoPointComplement_eq_one_sub hq hα hβ x hx hroot hij,
    hcompression] at hcomplement
  have hidentity := Matrix.twoPointRankOneCompression_det_identity
    (x i) (x j) τ u v
  rw [quasiJacobiCompressionCoordinate_sq hq hα hβ x hx hroot i,
    quasiJacobiCompressionCoordinate_sq hq hα hβ x hx hroot j] at hidentity
  exact quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior_certificate
    hq hα hβ x hx hroot hij hi hj hτ hC.det_pos hcomplement.det_pos hidentity

/-- Every off-diagonal entry of the normalized quasi-Jacobi collocation
matrix is strictly positive.  The proof includes `τ = 0` and both possible
single exterior-node configurations. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    {i j : Fin q} (hij : i ≠ j) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  let u := quasiJacobiCompressionCoordinate q α β τ x i
  let v := quasiJacobiCompressionCoordinate q α β τ x j
  let C := Matrix.twoPointRankOneCompression (x i) (x j) τ u v
  have hcompression := quasiJacobiTwoPointCompression_eq_rankOne
    hq hα hβ x hx hroot hij
  have hC : C.PosDef := by
    change (Matrix.twoPointRankOneCompression (x i) (x j) τ
      (quasiJacobiCompressionCoordinate q α β τ x i)
      (quasiJacobiCompressionCoordinate q α β τ x j)).PosDef
    rw [← hcompression]
    exact quasiJacobiTwoPointCompression_posDef hq hα hβ x hx hroot hij
  have hcomplement := quasiJacobiTwoPointComplement_posDef
    hq hα hβ x hx hroot hij
  rw [quasiJacobiTwoPointComplement_eq_one_sub hq hα hβ x hx hroot hij,
    hcompression] at hcomplement
  have hui : 0 < u ^ 2 := by
    rw [quasiJacobiCompressionCoordinate_sq hq hα hβ x hx hroot i]
    exact inv_pos.mpr (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i)
  have hvj : 0 < v ^ 2 := by
    rw [quasiJacobiCompressionCoordinate_sq hq hα hβ x hx hroot j]
    exact inv_pos.mpr (quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j)
  have hu : u ≠ 0 := sq_pos_iff.mp hui
  have hv : v ≠ 0 := sq_pos_iff.mp hvj
  have hCii : 0 < x i - τ * u ^ 2 := by
    have := hC.diag_pos (i := (0 : Fin 2))
    have hraw : 0 < x i - τ * u * u := by
      simpa [C, Matrix.twoPointRankOneCompression] using this
    nlinarith
  have hCjj : 0 < x j - τ * v ^ 2 := by
    have := hC.diag_pos (i := (1 : Fin 2))
    have hraw : 0 < x j - τ * v * v := by
      simpa [C, Matrix.twoPointRankOneCompression] using this
    nlinarith
  have hIii : 0 < 1 - x i + τ * u ^ 2 := by
    have := hcomplement.diag_pos (i := (0 : Fin 2))
    have hraw : x i - τ * u * u < 1 := by
      simpa [u, Matrix.twoPointRankOneCompression] using this
    nlinarith
  have hIjj : 0 < 1 - x j + τ * v ^ 2 := by
    have := hcomplement.diag_pos (i := (1 : Fin 2))
    have hraw : x j - τ * v * v < 1 := by
      simpa [v, Matrix.twoPointRankOneCompression] using this
    nlinarith
  have hnotRight : ¬(1 ≤ x i ∧ 1 ≤ x j) := by
    rintro ⟨hi, hj⟩
    exact Matrix.one_sub_twoPointRankOneCompression_not_posDef_of_one_le
      hi hj (Or.inl hu) hcomplement
  have hnotLeft : ¬(x i ≤ 0 ∧ x j ≤ 0) := by
    rintro ⟨hi, hj⟩
    exact Matrix.twoPointRankOneCompression_not_posDef_of_nonpos
      hi hj (Or.inl hu) hC
  have hsymm := (quasiJacobiCollocationMatrix_isSymm
    hq hα hβ x hx hroot).apply i j
  rcases lt_trichotomy τ 0 with hτ | hτ | hτ
  · have hi1 : x i < 1 := by nlinarith
    have hj1 : x j < 1 := by nlinarith
    by_cases hi0 : 0 < x i
    · by_cases hj0 : 0 < x j
      · exact quasiJacobiCollocationMatrix_offdiag_pos_of_mem_Ioo
          hq hα hβ x hx hroot hij ⟨hi0, hi1⟩ ⟨hj0, hj1⟩
      · have hjle : x j ≤ 0 := le_of_not_gt hj0
        rw [← hsymm]
        exact quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior
          hq hα hβ x hx hroot hij.symm hjle ⟨hi0, hi1⟩ hτ
    · have hile : x i ≤ 0 := le_of_not_gt hi0
      have hj0 : 0 < x j := by
        by_contra h
        exact hnotLeft ⟨hile, le_of_not_gt h⟩
      exact quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior
        hq hα hβ x hx hroot hij hile ⟨hj0, hj1⟩ hτ
  · subst τ
    apply quasiJacobiCollocationMatrix_offdiag_pos_of_mem_Ioo
      hq hα hβ x hx hroot hij
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · have hi0 : 0 < x i := by nlinarith
    have hj0 : 0 < x j := by nlinarith
    by_cases hi1 : x i < 1
    · by_cases hj1 : x j < 1
      · exact quasiJacobiCollocationMatrix_offdiag_pos_of_mem_Ioo
          hq hα hβ x hx hroot hij ⟨hi0, hi1⟩ ⟨hj0, hj1⟩
      · exact quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior
          hq hα hβ x hx hroot hij ⟨hi0, hi1⟩ (le_of_not_gt hj1) hτ
    · have hiRight : 1 ≤ x i := le_of_not_gt hi1
      have hj1 : x j < 1 := by
        by_contra h
        exact hnotRight ⟨hiRight, le_of_not_gt h⟩
      rw [← hsymm]
      exact quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior
        hq hα hβ x hx hroot hij.symm ⟨hj0, hj1⟩ hiRight hτ

/-- Every diagonal entry of positive-Jacobi collocation at distinct
quasi-Jacobi roots is strictly positive. -/
theorem shiftedJacobi_collocationMatrix_diag_pos
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i : Fin q) :
    0 < collocationMatrix (positiveJacobiOperator α β) x i i := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  let bi := Lagrange.basis Finset.univ x i
  have hbdeg : bi.natDegree = q - 1 := by
    simpa [bi] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hbderiv : bi.derivative ≠ 0 := by
    apply (bi.derivative_ne_zero).mpr
    rw [hbdeg]
    lia
  have henergy :
      0 < shiftedJacobiInner α β bi (positiveJacobiOperator α β bi) :=
    shiftedJacobiInner_positiveJacobiOperator_self_pos hα hβ hbderiv
  have hquad := quadrature_cardinal_operator hq L
    (positiveJacobiOperator α β) x hx
    (fun g hg ↦ by
      change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
      rw [nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot]
      exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg)
    (positiveJacobiOperator_natDegree_lt α β) i i
  change shiftedJacobiInner α β bi (positiveJacobiOperator α β bi) =
      quadratureWeight L x i *
        collocationMatrix (positiveJacobiOperator α β) x i i at hquad
  rw [hquad] at henergy
  have hweight : 0 < quadratureWeight L x i :=
    shiftedJacobi_quadratureWeight_pos_of_roots hq hα hβ x hx hroot i
  nlinarith

/-- The signed diagonal similarity preserves the strictly positive diagonal
entries of positive-Jacobi collocation. -/
theorem quasiJacobiCollocationMatrix_diag_pos
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i : Fin q) :
    0 < quasiJacobiCollocationMatrix q α β τ x i i := by
  have hscale := quasiJacobiCollocationScale_ne_zero
    hq hα hβ x hx hroot i
  rw [quasiJacobiCollocationMatrix, div_self hscale, one_mul]
  exact shiftedJacobi_collocationMatrix_diag_pos hq hα hβ x hx hroot i

/-- Every entry of the normalized quasi-Jacobi collocation matrix is
strictly positive, including the diagonal and every exterior-node case. -/
theorem quasiJacobiCollocationMatrix_entry_pos
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ k, (quasiJacobiPolynomial q α β τ).IsRoot (x k))
    (i j : Fin q) :
    0 < quasiJacobiCollocationMatrix q α β τ x i j := by
  by_cases hij : i = j
  · subst j
    exact quasiJacobiCollocationMatrix_diag_pos hq hα hβ x hx hroot i
  · exact quasiJacobiCollocationMatrix_offdiag_pos
      hq hα hβ x hx hroot hij

/-- The positively normalized quasi-Jacobi collocation matrix is symmetric. -/
theorem shiftedJacobi_symmetrizedCollocationMatrix_isSymm
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    (symmetrizedCollocationMatrix
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β))
      (positiveJacobiOperator α β) x).IsSymm := by
  apply symmetrizedCollocationMatrix_isSymm
  · exact shiftedJacobi_quadratureWeight_pos_of_roots hq hα hβ x hx hroot
  · exact shiftedJacobi_weighted_collocation_comm hq hα hβ x hx hroot

end RealRooted.JacobiDeformation
