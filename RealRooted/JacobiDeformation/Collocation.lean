import RealRooted.JacobiDeformation.Quadrature
import RealRooted.JacobiDeformation.Kernel

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
