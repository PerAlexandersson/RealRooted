import RealRooted.JacobiDeformation.Collocation
import RealRooted.Mathlib.LinearAlgebra.Matrix.RankOneCompression

/-!
# Entrywise positivity of the quasi-Jacobi collocation matrix

A quasi-Jacobi polynomial may have one root outside `(0, 1)`, so the
off-diagonal formula for the symmetric collocation matrix `A` needs a separate
argument at an exterior node.  In normalized Lagrange coordinates,
multiplication by `X` compresses to the two-point matrix
`diag(t_i, t_j) - τ w wᵀ` with `w_i ^ 2 = 1 / η_i`, and multiplication by
`1 - X` compresses to its complement.  Both compressions are positive
definite, and the determinant identity of
`Matrix.twoPointRankOneCompression_det_identity` then forces the numerator
`σ(t_i) η_i + σ(t_j) η_j` to be positive in every exterior configuration.
The finite Jacobi energy identity proves the diagonal entries positive, so
every entry of `A` is strictly positive
(`quasiJacobiCollocationMatrix_entry_pos`).
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- A Lagrange cardinal polynomial normalized to have unit squared norm for
the shifted-Jacobi moment pairing. -/
def normalizedJacobiCardinal {q : ℕ} (α β : ℝ) (x : Fin q → ℝ)
    (i : Fin q) : ℝ[X] :=
  C (Real.sqrt (Lagrange.quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))⁻¹ *
      Lagrange.basis Finset.univ x i

/-- Signed last-coordinate model for the rank-one quasi-Jacobi update.  Its
square is the inverse Christoffel ratio `quasiJacobiEta`. -/
def quasiJacobiCompressionCoordinate (q : ℕ) (α β τ : ℝ)
    (x : Fin q → ℝ) (i : Fin q) : ℝ :=
  Real.sqrt (shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
      (shiftedJacobiMonic (q - 1) α β)) /
    ((quasiJacobiPolynomial q α β τ).derivative.eval (x i) *
      Real.sqrt (Lagrange.quadratureWeight
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
        Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
      else 0 := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  let bi := Lagrange.basis Finset.univ x i
  let bj := Lagrange.basis Finset.univ x j
  have hbjdeg : bj.natDegree < q := by
    rw [show bj.natDegree = q - 1 by
      simpa [bj] using Lagrange.natDegree_basis hx.injOn (mem_univ j)]
    lia
  have hpair := Lagrange.quadratureWeight_mul_eval hq L x hx
    (fun g hg ↦ by
      change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
      rw [nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot]
      exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg)
    bj hbjdeg i
  change Lagrange.quadratureWeight L x i * bj.eval (x i) =
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
  let wi := Lagrange.quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
  let wj := Lagrange.quadratureWeight
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
    exact Lagrange.eval_derivative_nodal_ne_zero x hx i
  have hdj : dj ≠ 0 := by
    change (quasiJacobiPolynomial q α β τ).derivative.eval (x j) ≠ 0
    rw [← hnodal]
    exact Lagrange.eval_derivative_nodal_ne_zero x hx j
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
  have haction := Lagrange.X_mul_basis x j
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
ratio `1 / η_i` appearing in the off-diagonal formula. -/
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
  let w := Lagrange.quadratureWeight
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
    exact Lagrange.eval_derivative_nodal_ne_zero x hx i
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
  have hsi : Real.sqrt (Lagrange.quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i) ≠ 0 :=
    (Real.sqrt_pos.2 hwi).ne'
  have hsj : Real.sqrt (Lagrange.quadratureWeight
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
      have hei_i : ei.eval (x i) = (Real.sqrt (Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))⁻¹ := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      have hei_j : ei.eval (x j) = 0 := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij (mem_univ j)]
      have hej_i : ej.eval (x i) = 0 := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij.symm (mem_univ i)]
      have hej_j : ej.eval (x j) = (Real.sqrt (Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j))⁻¹ := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ j)]
      simp only [p, eval_add, eval_mul, eval_C, eval_zero,
        hei_i, hei_j, hej_i, hej_j, mul_zero, add_zero, zero_add] at hi hj
      have hyi : y 0 = 0 :=
        (mul_eq_zero.mp hi).resolve_right (inv_ne_zero hsi)
      have hyj : y 1 = 0 :=
        (mul_eq_zero.mp hj).resolve_right (inv_ne_zero hsj)
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
  have hsi : Real.sqrt (Lagrange.quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i) ≠ 0 :=
    (Real.sqrt_pos.2 hwi).ne'
  have hsj : Real.sqrt (Lagrange.quadratureWeight
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
      have hei_i : ei.eval (x i) = (Real.sqrt (Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i))⁻¹ := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      have hei_j : ei.eval (x j) = 0 := by
        simp [ei, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij (mem_univ j)]
      have hej_i : ej.eval (x i) = 0 := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_of_ne hij.symm (mem_univ i)]
      have hej_j : ej.eval (x j) = (Real.sqrt (Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j))⁻¹ := by
        simp [ej, normalizedJacobiCardinal,
          Lagrange.eval_basis_self hx.injOn (mem_univ j)]
      simp only [p, eval_add, eval_mul, eval_C, eval_zero,
        hei_i, hei_j, hej_i, hej_j, mul_zero, add_zero, zero_add] at hi hj
      have hyi : y 0 = 0 :=
        (mul_eq_zero.mp hi).resolve_right (inv_ne_zero hsi)
      have hyj : y 1 = 0 :=
        (mul_eq_zero.mp hj).resolve_right (inv_ne_zero hsj)
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

/-- Given positive compression determinants, the two-point determinant identity
proves the off-diagonal entry positive when the second quasi-node is on or
beyond the right endpoint. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior_of_det_pos
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

/-- Given positive compression determinants, the two-point determinant identity
proves the off-diagonal entry positive when the first quasi-node is on or
beyond the left endpoint. -/
theorem quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior_of_det_pos
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

/-- The off-diagonal entry is strictly positive for a right-exterior
quasi-node.  The finite multiplication compressions supply both positive
determinants. -/
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
  exact quasiJacobiCollocationMatrix_offdiag_pos_of_right_exterior_of_det_pos
    hq hα hβ x hx hroot hij hi hj hτ hC.det_pos hcomplement.det_pos hidentity

/-- The off-diagonal entry is strictly positive for a left-exterior
quasi-node, with the finite multiplication compressions supplying the
determinant signs. -/
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
  exact quasiJacobiCollocationMatrix_offdiag_pos_of_left_exterior_of_det_pos
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
    linarith
  have hCjj : 0 < x j - τ * v ^ 2 := by
    have := hC.diag_pos (i := (1 : Fin 2))
    have hraw : 0 < x j - τ * v * v := by
      simpa [C, Matrix.twoPointRankOneCompression] using this
    linarith
  have hIii : 0 < 1 - x i + τ * u ^ 2 := by
    have := hcomplement.diag_pos (i := (0 : Fin 2))
    have hraw : x i - τ * u * u < 1 := by
      simpa [u, Matrix.twoPointRankOneCompression] using this
    linarith
  have hIjj : 0 < 1 - x j + τ * v ^ 2 := by
    have := hcomplement.diag_pos (i := (1 : Fin 2))
    have hraw : x j - τ * v * v < 1 := by
      simpa [v, Matrix.twoPointRankOneCompression] using this
    linarith
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
    · constructor <;> linarith
    · constructor <;> linarith
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
    0 < Lagrange.collocationMatrix (positiveJacobiOperator α β) x i i := by
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
  have hquad := Lagrange.quadrature_basis_mul_apply hq L
    (positiveJacobiOperator α β) x hx
    (fun g hg ↦ by
      change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
      rw [nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot]
      exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg)
    (positiveJacobiOperator_natDegree_lt α β) i i
  change shiftedJacobiInner α β bi (positiveJacobiOperator α β bi) =
      Lagrange.quadratureWeight L x i *
        Lagrange.collocationMatrix (positiveJacobiOperator α β) x i i at hquad
  rw [hquad] at henergy
  have hweight : 0 < Lagrange.quadratureWeight L x i :=
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
    (Lagrange.symmetrizedCollocationMatrix
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β))
      (positiveJacobiOperator α β) x).IsSymm := by
  apply Lagrange.symmetrizedCollocationMatrix_isSymm
  · exact shiftedJacobi_quadratureWeight_pos_of_roots hq hα hβ x hx hroot
  · exact shiftedJacobi_weighted_collocation_comm hq hα hβ x hx hroot

end RealRooted.JacobiDeformation
