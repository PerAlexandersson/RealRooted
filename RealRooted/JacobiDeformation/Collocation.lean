import RealRooted.JacobiDeformation.JacobiOperator

/-!
# The symmetric quasi-Jacobi collocation matrix

Let `t_1, …, t_q` be the distinct roots of a quasi-Jacobi polynomial
`v = p_q - τ p_{q-1}` and let `D` be the collocation matrix of the positive
Jacobi operator at these nodes.  Exact quadrature makes `Ω D` symmetric for
the diagonal matrix `Ω` of quadrature weights, so the diagonal similarity by
`√η_i p_{q-1}(t_i)` gives a symmetric matrix `A`
(`quasiJacobiCollocationMatrix`).  Differentiating the cardinal polynomials
gives, for `i ≠ j`,

`A_{ij} = (σ(t_i) η_i + σ(t_j) η_j) / ((t_i - t_j) ^ 2 √(η_i η_j))`,

with `σ(t) = t (1 - t)` (`quasiJacobiCollocationMatrix_offdiag`), after the
rank-one residual cancels by symmetry.  This is strictly positive when both
nodes lie in `(0, 1)`; exterior nodes are handled in
`RealRooted.JacobiDeformation.CollocationPositivity`.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Explicit off-diagonal quasi-Jacobi collocation formula.  The first term
is the rank-one residual and the second is the differential cardinal term. -/
theorem shiftedJacobi_collocationMatrix_offdiag
    {q : ℕ} {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {i j : Fin q} (hij : i ≠ j) :
    Lagrange.collocationMatrix (positiveJacobiOperator α β) x i j =
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
  have hdj : d j ≠ 0 := Lagrange.eval_derivative_nodal_ne_zero x hx j
  have hb1 := Lagrange.eval_derivative_basis_of_ne x hx hij
  change (Lagrange.basis Finset.univ x j).derivative.eval (x i) =
    d i / (s * d j) at hb1
  have hb2 := Lagrange.eval_derivative_derivative_basis_of_ne x hx hij
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
  rw [Lagrange.collocationMatrix, eval_positiveJacobiOperator, hb1, hb2]
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
      Lagrange.collocationMatrix (positiveJacobiOperator α β) x i j

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
    Lagrange.quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        quasiJacobiCollocationScale q α β τ x i ^ 2 =
      shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
  let d := (quasiJacobiPolynomial q α β τ).derivative.eval (x i)
  let p := (shiftedJacobiMonic (q - 1) α β).eval (x i)
  let w := Lagrange.quadratureWeight
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
    Lagrange.quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        Lagrange.collocationMatrix (positiveJacobiOperator α β) x i j =
      Lagrange.quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j *
        Lagrange.collocationMatrix (positiveJacobiOperator α β) x j i := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  apply Lagrange.quadratureWeight_mul_collocationMatrix_comm hq L
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
  let w := fun k ↦ Lagrange.quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x k
  let r := quasiJacobiCollocationScale q α β τ x
  let D := Lagrange.collocationMatrix (positiveJacobiOperator α β) x
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

/-- Symmetry cancels the rank-one residual and gives the off-diagonal
formula. -/
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

/-- The off-diagonal entry is strictly positive when both quasi-nodes are
interior. -/
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

end RealRooted.JacobiDeformation
