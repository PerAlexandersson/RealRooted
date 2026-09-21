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
