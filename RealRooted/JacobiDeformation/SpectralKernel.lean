import RealRooted.JacobiDeformation.CollocationPositivity
import RealRooted.JacobiDeformation.KernelSign
import RealRooted.JacobiDeformation.NewtonIdentity

/-!
# The spectral kernel of the quasi-Jacobi collocation matrix

Let `A` be the symmetric quasi-Jacobi collocation matrix at the roots
`t_1, …, t_q` of `p_q - τ p_{q-1}`.  Exact quadrature gives an explicit
inverse of the matrix of Jacobi evaluations `p_l(t_i)`, and the resulting
similarity diagonalizes `A` with the simple spectrum `λ_0 < ⋯ < λ_{q-1}`.
Hence, for every polynomial `Φ`,

`Φ(A)_{ij} = h_{q-1} / (√(η_i η_j) p_{q-1}(t_i) p_{q-1}(t_j)) ·
  ∑_{l < q} Φ(λ_l) p_l(t_i) p_l(t_j) / h_l`.

Applying this to the positive Newton polynomial of the kernel weights and
combining with `RealRooted.JacobiDeformation.KernelSign`, the weighted kernel
`∑_l w_l p_l(t_i) p_l(t_j) / h_l` divided by `p_{q-1}(t_i) p_{q-1}(t_j)` is
strictly positive, even at a quasi-node outside `(0, 1)`.
-/

open Finset Matrix Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Diagonalization of the collocation matrix -/

/-- Squared norm of the monic shifted-Jacobi polynomial. -/
def shiftedJacobiMonicNorm (n : ℕ) (α β : ℝ) : ℝ :=
  shiftedJacobiInner α β (shiftedJacobiMonic n α β)
    (shiftedJacobiMonic n α β)

theorem shiftedJacobiMonicNorm_pos {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < shiftedJacobiMonicNorm n α β := by
  have hpmono :=
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).isMonicOfDegree n
  have hpos := shiftedJacobiMomentPairingBilinForm_posDef hα hβ
    (shiftedJacobiMonic n α β) hpmono.monic.ne_zero
  simpa only [shiftedJacobiMonicNorm, LinearMap.BilinMap.toQuadraticMap_apply,
    Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos

/-- Matrix whose columns are the first `q` monic shifted-Jacobi polynomials
evaluated at the `q` quasi-Jacobi nodes. -/
def jacobiEvaluationMatrix (q : ℕ) (α β : ℝ) (x : Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun i n => (shiftedJacobiMonic n α β).eval (x i)

/-- Quadrature formula for the pairwise orthogonality of the first `q` monic
shifted-Jacobi polynomials. -/
theorem shiftedJacobiMonic_quadrature_orthogonality
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (n k : Fin q) :
    ∑ i : Fin q,
        Lagrange.quadratureWeight
            (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
          (shiftedJacobiMonic n α β).eval (x i) *
          (shiftedJacobiMonic k α β).eval (x i) =
      if n = k then shiftedJacobiMonicNorm n α β else 0 := by
  let pn := shiftedJacobiMonic n α β
  let pk := shiftedJacobiMonic k α β
  have hndeg : pn.natDegree = n :=
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).natDegree_eq n
  have hkdeg : pk.natDegree = k :=
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).natDegree_eq k
  have hdeg : (pn * pk).natDegree ≤ 2 * q - 2 := by
    calc
      (pn * pk).natDegree ≤ pn.natDegree + pk.natDegree := natDegree_mul_le
      _ ≤ (q - 1) + (q - 1) := by rw [hndeg, hkdeg]; lia
      _ = 2 * q - 2 := by lia
  have hquad := shiftedJacobi_quadrature_exact_of_roots
    hq hα hβ x hx hroot hdeg
  change shiftedJacobiInner α β pn pk = _ at hquad
  calc
    _ = shiftedJacobiInner α β pn pk := by
      simpa only [eval_mul, pn, pk, mul_assoc] using hquad.symm
    _ = _ := by
      by_cases hnk : n = k
      · subst k
        simp [shiftedJacobiMonicNorm, pn, pk]
      · simp only [hnk, ↓reduceIte]
        rcases lt_or_gt_of_ne hnk with hlt | hgt
        · rw [← shiftedJacobiInner_comm]
          exact shiftedJacobiMonicInner_eq_zero hα hβ pn
            (by simpa [hndeg] using hlt)
        · exact shiftedJacobiMonicInner_eq_zero hα hβ pk
            (by simpa [hkdeg] using hgt)

/-- Explicit quadrature inverse of `jacobiEvaluationMatrix`. -/
def jacobiEvaluationMatrixInv (q : ℕ) (α β : ℝ) (x : Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun n i =>
    Lagrange.quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
      (shiftedJacobiMonic n α β).eval (x i) /
        shiftedJacobiMonicNorm n α β

theorem jacobiEvaluationMatrixInv_mul
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    jacobiEvaluationMatrixInv q α β x * jacobiEvaluationMatrix q α β x = 1 := by
  apply Matrix.ext
  intro n k
  rw [Matrix.mul_apply]
  simp only [jacobiEvaluationMatrixInv, jacobiEvaluationMatrix]
  rw [Matrix.one_apply]
  have hsum :
      (∑ j : Fin q,
          Lagrange.quadratureWeight
                (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j *
              (shiftedJacobiMonic n α β).eval (x j) /
                shiftedJacobiMonicNorm n α β *
              (shiftedJacobiMonic k α β).eval (x j)) =
        (∑ j : Fin q,
            Lagrange.quadratureWeight
                (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j *
              (shiftedJacobiMonic n α β).eval (x j) *
              (shiftedJacobiMonic k α β).eval (x j)) /
            shiftedJacobiMonicNorm n α β := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, shiftedJacobiMonic_quadrature_orthogonality
    hq hα hβ x hx hroot]
  by_cases hnk : n = k
  · subst k
    simp only [↓reduceIte]
    rw [div_self (shiftedJacobiMonicNorm_pos hα hβ n).ne']
  · simp only [hnk, ↓reduceIte]
    rw [zero_div]

theorem jacobiEvaluationMatrix_mul_inv
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    jacobiEvaluationMatrix q α β x * jacobiEvaluationMatrixInv q α β x = 1 :=
  mul_eq_one_comm.mp
    (jacobiEvaluationMatrixInv_mul hq hα hβ x hx hroot)

/-- Columns of the evaluation matrix, divided by the signed collocation
scale, are eigenvectors of the symmetric collocation matrix. -/
def quasiJacobiEigenvectorMatrix (q : ℕ) (α β τ : ℝ)
    (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i n => (shiftedJacobiMonic n α β).eval (x i) /
    quasiJacobiCollocationScale q α β τ x i

/-- Explicit inverse of `quasiJacobiEigenvectorMatrix`. -/
def quasiJacobiEigenvectorMatrixInv (q : ℕ) (α β τ : ℝ)
    (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun n i => jacobiEvaluationMatrixInv q α β x n i *
    quasiJacobiCollocationScale q α β τ x i

theorem quasiJacobiEigenvectorMatrixInv_mul
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    quasiJacobiEigenvectorMatrixInv q α β τ x *
        quasiJacobiEigenvectorMatrix q α β τ x = 1 := by
  apply Matrix.ext
  intro n k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hinv := congrFun₂
    (jacobiEvaluationMatrixInv_mul hq hα hβ x hx hroot) n k
  rw [Matrix.mul_apply, Matrix.one_apply] at hinv
  rw [← hinv]
  apply Finset.sum_congr rfl
  intro i _
  simp only [quasiJacobiEigenvectorMatrixInv,
    quasiJacobiEigenvectorMatrix, jacobiEvaluationMatrix]
  field_simp [quasiJacobiCollocationScale_ne_zero
    hq hα hβ x hx hroot i]

theorem quasiJacobiEigenvectorMatrix_mul_inv
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    quasiJacobiEigenvectorMatrix q α β τ x *
        quasiJacobiEigenvectorMatrixInv q α β τ x = 1 :=
  mul_eq_one_comm.mp
    (quasiJacobiEigenvectorMatrixInv_mul hq hα hβ x hx hroot)

/-- The signed quasi-Jacobi collocation matrix is intertwined with the
diagonal matrix of the first `q` quadratic Jacobi eigenvalues. -/
theorem quasiJacobiCollocationMatrix_mul_eigenvectorMatrix
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    quasiJacobiCollocationMatrix q α β τ x *
        quasiJacobiEigenvectorMatrix q α β τ x =
      quasiJacobiEigenvectorMatrix q α β τ x *
        diagonal (fun n : Fin q => eigenvalue (α + β + 2) n) := by
  apply Matrix.ext
  intro i n
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have haction := congrFun
    (collocationMatrix_mulVec_shiftedJacobiMonic n.isLt hα hβ x hx) i
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at haction
  change (∑ j : Fin q,
      Lagrange.collocationMatrix (positiveJacobiOperator α β) x i j *
        (shiftedJacobiMonic n α β).eval (x j)) =
    eigenvalue (α + β + 2) n *
      (shiftedJacobiMonic n α β).eval (x i) at haction
  calc
    _ = (∑ j : Fin q,
        Lagrange.collocationMatrix (positiveJacobiOperator α β) x i j *
          (shiftedJacobiMonic n α β).eval (x j)) /
        quasiJacobiCollocationScale q α β τ x i := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      simp only [quasiJacobiCollocationMatrix,
        quasiJacobiEigenvectorMatrix]
      field_simp [quasiJacobiCollocationScale_ne_zero
        hq hα hβ x hx hroot j]
    _ = eigenvalue (α + β + 2) n *
        (shiftedJacobiMonic n α β).eval (x i) /
          quasiJacobiCollocationScale q α β τ x i :=
      congrArg (fun y => y / quasiJacobiCollocationScale q α β τ x i)
        haction
    _ = quasiJacobiEigenvectorMatrix q α β τ x i n *
        eigenvalue (α + β + 2) n := by
      simp only [quasiJacobiEigenvectorMatrix]
      ring

private theorem matrix_pow_mul_of_mul_eq_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B Q : Matrix n n ℝ) (hAQ : A * Q = Q * B) (k : ℕ) :
    A ^ k * Q = Q * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        A ^ (k + 1) * Q = A ^ k * (A * Q) := by rw [pow_succ, mul_assoc]
        _ = A ^ k * (Q * B) := by rw [hAQ]
        _ = (A ^ k * Q) * B := by rw [mul_assoc]
        _ = (Q * B ^ k) * B := by rw [ih]
        _ = Q * B ^ (k + 1) := by rw [pow_succ, mul_assoc]

/-- Polynomial functional calculus preserves an intertwining relation. -/
theorem aeval_mul_of_mul_eq_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B Q : Matrix n n ℝ) (hAQ : A * Q = Q * B) (p : ℝ[X]) :
    aeval A p * Q = Q * aeval B p := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, map_add, add_mul, mul_add, hp, hr]
  | monomial k a =>
      rw [aeval_monomial, aeval_monomial]
      have hpow := matrix_pow_mul_of_mul_eq_mul A B Q hAQ k
      have hscalar :
          algebraMap ℝ (Matrix n n ℝ) a * Q =
            Q * algebraMap ℝ (Matrix n n ℝ) a :=
        Algebra.commutes a Q
      calc
        (algebraMap ℝ (Matrix n n ℝ) a * A ^ k) * Q =
            algebraMap ℝ (Matrix n n ℝ) a * (A ^ k * Q) := by rw [mul_assoc]
        _ = algebraMap ℝ (Matrix n n ℝ) a * (Q * B ^ k) := by rw [hpow]
        _ = (algebraMap ℝ (Matrix n n ℝ) a * Q) * B ^ k := by rw [mul_assoc]
        _ = (Q * algebraMap ℝ (Matrix n n ℝ) a) * B ^ k := by rw [hscalar]
        _ = Q * (algebraMap ℝ (Matrix n n ℝ) a * B ^ k) := by rw [mul_assoc]

private theorem aeval_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (p : ℝ[X]) :
    aeval (diagonal d) p = diagonal (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, hp, hr]
      ext i j
      simp only [Matrix.add_apply, diagonal_apply, eval_add]
      by_cases hij : i = j <;> simp [hij]
  | monomial k a =>
      ext i j
      simp only [aeval_monomial, Matrix.mul_apply,
        Matrix.algebraMap_matrix_apply]
      rw [Matrix.diagonal_pow]
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal_apply]
      · simp [Matrix.diagonal_apply, hij]

/-- Functional calculus of the signed collocation matrix in its explicit
Jacobi evaluation eigenbasis. -/
theorem aeval_quasiJacobiCollocationMatrix_eq
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (p : ℝ[X]) :
    aeval (quasiJacobiCollocationMatrix q α β τ x) p =
      quasiJacobiEigenvectorMatrix q α β τ x *
        diagonal (fun n : Fin q => p.eval (eigenvalue (α + β + 2) n)) *
          quasiJacobiEigenvectorMatrixInv q α β τ x := by
  let A := quasiJacobiCollocationMatrix q α β τ x
  let Q := quasiJacobiEigenvectorMatrix q α β τ x
  let R := quasiJacobiEigenvectorMatrixInv q α β τ x
  let Λ := diagonal (fun n : Fin q => eigenvalue (α + β + 2) n)
  have hQR : Q * R = 1 :=
    quasiJacobiEigenvectorMatrix_mul_inv hq hα hβ x hx hroot
  have hAQ : A * Q = Q * Λ :=
    quasiJacobiCollocationMatrix_mul_eigenvectorMatrix hq hα hβ x hx hroot
  calc
    aeval A p = aeval A p * (Q * R) := by rw [hQR, mul_one]
    _ = (aeval A p * Q) * R := by rw [mul_assoc]
    _ = (Q * aeval Λ p) * R := by rw [aeval_mul_of_mul_eq_mul A Λ Q hAQ p]
    _ = Q * diagonal (fun n : Fin q => p.eval (eigenvalue (α + β + 2) n)) * R := by
      rw [aeval_diagonal]

/-- Raw entrywise form of the collocation spectral expansion. -/
theorem aeval_quasiJacobiCollocationMatrix_apply
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (p : ℝ[X]) (i j : Fin q) :
    (aeval (quasiJacobiCollocationMatrix q α β τ x) p) i j =
      ∑ n : Fin q,
        quasiJacobiEigenvectorMatrix q α β τ x i n *
          p.eval (eigenvalue (α + β + 2) n) *
          quasiJacobiEigenvectorMatrixInv q α β τ x n j := by
  rw [aeval_quasiJacobiCollocationMatrix_eq hq hα hβ x hx hroot]
  rw [mul_assoc]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [Matrix.diagonal_mul]
  ring

/-- The spectral kernel expansion of `Φ(A)`: the raw quadrature expansion
rewritten using the common
scale identity `w_j r_j² = h_{q-1}`. -/
theorem aeval_quasiJacobiCollocationMatrix_apply_eq_kernel_sum
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (p : ℝ[X]) (i j : Fin q) :
    (aeval (quasiJacobiCollocationMatrix q α β τ x) p) i j =
      shiftedJacobiMonicNorm (q - 1) α β /
          (quasiJacobiCollocationScale q α β τ x i *
            quasiJacobiCollocationScale q α β τ x j) *
        ∑ n : Fin q,
          p.eval (eigenvalue (α + β + 2) n) *
            (shiftedJacobiMonic n α β).eval (x i) *
            (shiftedJacobiMonic n α β).eval (x j) /
              shiftedJacobiMonicNorm n α β := by
  rw [aeval_quasiJacobiCollocationMatrix_apply hq hα hβ x hx hroot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  let ri := quasiJacobiCollocationScale q α β τ x i
  let rj := quasiJacobiCollocationScale q α β τ x j
  let wj := Lagrange.quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x j
  let hn := shiftedJacobiMonicNorm n α β
  let H := shiftedJacobiMonicNorm (q - 1) α β
  have hri : ri ≠ 0 :=
    quasiJacobiCollocationScale_ne_zero hq hα hβ x hx hroot i
  have hrj : rj ≠ 0 :=
    quasiJacobiCollocationScale_ne_zero hq hα hβ x hx hroot j
  have hhn : hn ≠ 0 := (shiftedJacobiMonicNorm_pos hα hβ n).ne'
  have hscale := quadratureWeight_mul_quasiJacobiCollocationScale_sq
    hq hα hβ x hx hroot j
  change wj * rj ^ 2 = H at hscale
  have hwj : wj * rj = H / rj := by
    apply (eq_div_iff hrj).2
    calc
      wj * rj * rj = wj * rj ^ 2 := by ring
      _ = H := hscale
  simp only [quasiJacobiEigenvectorMatrixInv,
    quasiJacobiEigenvectorMatrix, jacobiEvaluationMatrixInv]
  change
    (shiftedJacobiMonic n α β).eval (x i) / ri *
          p.eval (eigenvalue (α + β + 2) n) *
        (wj * (shiftedJacobiMonic n α β).eval (x j) / hn * rj) =
      H / (ri * rj) *
        (p.eval (eigenvalue (α + β + 2) n) *
          (shiftedJacobiMonic n α β).eval (x i) *
          (shiftedJacobiMonic n α β).eval (x j) / hn)
  rw [show wj * (shiftedJacobiMonic n α β).eval (x j) / hn * rj =
      (wj * rj) * (shiftedJacobiMonic n α β).eval (x j) / hn by ring,
    hwj]
  field_simp [hri, hrj, hhn]

/-- Characteristic polynomial of the signed collocation matrix. -/
theorem quasiJacobiCollocationMatrix_charpoly
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    (quasiJacobiCollocationMatrix q α β τ x).charpoly =
      ∏ n : Fin q, (X - C (eigenvalue (α + β + 2) n)) := by
  let A := quasiJacobiCollocationMatrix q α β τ x
  let Q := quasiJacobiEigenvectorMatrix q α β τ x
  let R := quasiJacobiEigenvectorMatrixInv q α β τ x
  let Λ := diagonal (fun n : Fin q => eigenvalue (α + β + 2) n)
  have hQR : Q * R = 1 :=
    quasiJacobiEigenvectorMatrix_mul_inv hq hα hβ x hx hroot
  have hRQ : R * Q = 1 :=
    quasiJacobiEigenvectorMatrixInv_mul hq hα hβ x hx hroot
  have hAQ : A * Q = Q * Λ :=
    quasiJacobiCollocationMatrix_mul_eigenvectorMatrix hq hα hβ x hx hroot
  have hA : A = (Q * Λ) * R := by
    calc
      A = A * 1 := by rw [mul_one]
      _ = A * (Q * R) := by rw [hQR]
      _ = (A * Q) * R := by rw [mul_assoc]
      _ = (Q * Λ) * R := by rw [hAQ]
  calc
    A.charpoly = ((Q * Λ) * R).charpoly := congrArg Matrix.charpoly hA
    _ = (R * (Q * Λ)).charpoly := Matrix.charpoly_mul_comm (Q * Λ) R
    _ = ((R * Q) * Λ).charpoly := by rw [mul_assoc]
    _ = Λ.charpoly := by rw [hRQ, one_mul]
    _ = ∏ n : Fin q, (X - C (eigenvalue (α + β + 2) n)) :=
      Matrix.charpoly_diagonal _

/-- Real symmetry supplies the Hermitian structure used by the ordered
spectrum API. -/
theorem quasiJacobiCollocationMatrix_isHermitian
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    (quasiJacobiCollocationMatrix q α β τ x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr
    (quasiJacobiCollocationMatrix_isSymm hq hα hβ x hx hroot)

/-- The increasing Hermitian spectrum is exactly the quadratic Jacobi
spectrum, with no ordering permutation left implicit. -/
theorem quasiJacobiCollocationMatrix_increasingEigenvalues
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (n : Fin q) :
    increasingEigenvalues (quasiJacobiCollocationMatrix q α β τ x)
        (quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot) n =
      eigenvalue (α + β + 2) n := by
  let A := quasiJacobiCollocationMatrix q α β τ x
  let hA : A.IsHermitian :=
    quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot
  let μ : Fin q → ℝ := fun k => eigenvalue (α + β + 2) k
  have hs : 0 < α + β + 2 := by linarith
  have hchar : A.charpoly = ∏ k : Fin q, (X - C (μ k)) :=
    quasiJacobiCollocationMatrix_charpoly hq hα hβ x hx hroot
  have hrootsA :
      (↑(List.ofFn fun k : Fin q => increasingEigenvalues A hA k) : Multiset ℝ) =
        A.charpoly.roots := by
    rw [sortedEigenvalues_charpoly_roots A hA, ← Fin.univ_val_map]
    conv_rhs =>
      rw [← Finset.map_univ_equiv (Fin.revPerm (n := q)), Finset.map_val,
        Multiset.map_map]
    rfl
  have hrootsμ :
      A.charpoly.roots =
        (↑(List.ofFn μ) : Multiset ℝ) := by
    rw [hchar, Polynomial.roots_prod]
    · simp [Fin.univ_val_map]
    · exact Finset.prod_ne_zero_iff.mpr fun k _ =>
        Polynomial.X_sub_C_ne_zero (μ k)
  have hpairA :
      (List.ofFn fun k : Fin q => increasingEigenvalues A hA k).Pairwise (· ≤ ·) :=
    List.pairwise_ofFn.2 fun _ _ hkl =>
      increasingEigenvalues_monotone A hA hkl.le
  have hpairμ : (List.ofFn μ).Pairwise (· ≤ ·) :=
    List.pairwise_ofFn.2 fun _ _ hkl =>
      (eigenvalue_strictMono hs hkl).le
  have hperm : List.Perm
      (List.ofFn fun k : Fin q => increasingEigenvalues A hA k) (List.ofFn μ) :=
    Multiset.coe_eq_coe.mp (hrootsA.trans hrootsμ)
  have hlists := List.Perm.eq_of_pairwise' hpairA hpairμ hperm
  exact congrFun (List.ofFn_inj.mp hlists) n

/-- The signed quasi-Jacobi collocation matrix has simple spectrum. -/
theorem quasiJacobiCollocationMatrix_sortedEigenvalues_strictAnti
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    StrictAnti (sortedEigenvalues (quasiJacobiCollocationMatrix q α β τ x)
      (quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot)) := by
  let A := quasiJacobiCollocationMatrix q α β τ x
  let hA : A.IsHermitian :=
    quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot
  have hs : 0 < α + β + 2 := by linarith
  have hinc : StrictMono (increasingEigenvalues A hA) := by
    intro i j hij
    rw [quasiJacobiCollocationMatrix_increasingEigenvalues
        hq hα hβ x hx hroot i,
      quasiJacobiCollocationMatrix_increasingEigenvalues
        hq hα hβ x hx hroot j]
    exact eigenvalue_strictMono hs hij
  intro i j hij
  simpa only [increasingEigenvalues, Fin.rev_rev] using
    hinc (Fin.rev_strictAnti hij)

/-- Every entry of the finite Jacobi kernel matrix is strictly positive in the
open Newton-parameter range.  The proof uses the collocation spectrum above,
not a caller-supplied spectral hypothesis. -/
theorem aeval_weightNewtonPolynomial_quasiJacobiCollocationMatrix_entry_pos
    {N : ℕ} (hN : 1 ≤ N) {α β τ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : Fin (N + 1) → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i,
      (quasiJacobiPolynomial (N + 1) α β τ).IsRoot (x i))
    (i j : Fin (N + 1)) :
    0 < (aeval (quasiJacobiCollocationMatrix (N + 1) α β τ x)
      (weightNewtonPolynomial (N + 1) δ (α + β + 2))) i j := by
  have hq : 2 ≤ N + 1 := by lia
  let A := quasiJacobiCollocationMatrix (N + 1) α β τ x
  let hA : A.IsHermitian :=
    quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot
  have hs : 0 < α + β + 2 := by linarith
  apply aeval_weightNewtonPolynomial_entry_pos A hA
    (fun a b =>
      (quasiJacobiCollocationMatrix_entry_pos hq hα hβ x hx hroot a b).le)
    (quasiJacobiCollocationMatrix_sortedEigenvalues_strictAnti
      hq hα hβ x hx hroot)
    hδ hδ1 hs
    (fun k => quasiJacobiCollocationMatrix_increasingEigenvalues
      hq hα hβ x hx hroot k)
    i j
  exact quasiJacobiCollocationMatrix_entry_pos hq hα hβ x hx hroot i j

/-! ## Weighted signs of the Jacobi spectral kernel

We specialize the dimension-restricted Newton sign to the quasi-Jacobi
collocation matrix, then transport it through its spectral kernel expansion.
-/

/-- A degree-`m` Newton weight has strictly positive entries on the
quasi-Jacobi collocation matrix whenever its degree is at least the matrix
dimension. -/
theorem aeval_weightNewtonPolynomial_quasiJacobiCollocationMatrix_entry_pos_of_le
    {N m : ℕ} (hN : 1 ≤ N) (hm : N + 1 ≤ m) {α β τ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : Fin (N + 1) → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial (N + 1) α β τ).IsRoot (x i))
    (i j : Fin (N + 1)) :
    0 < (aeval (quasiJacobiCollocationMatrix (N + 1) α β τ x)
      (weightNewtonPolynomial m δ (α + β + 2))) i j := by
  have hq : 2 ≤ N + 1 := by lia
  let A := quasiJacobiCollocationMatrix (N + 1) α β τ x
  let hA : A.IsHermitian :=
    quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot
  have hs : 0 < α + β + 2 := by linarith
  apply aeval_weightNewtonPolynomial_entry_pos_of_dimension_le A hA
    (fun a b =>
      (quasiJacobiCollocationMatrix_entry_pos hq hα hβ x hx hroot a b).le)
    (quasiJacobiCollocationMatrix_sortedEigenvalues_strictAnti
      hq hα hβ x hx hroot)
    hm hδ hδ1 hs
    (fun k => quasiJacobiCollocationMatrix_increasingEigenvalues
      hq hα hβ x hx hroot k)
    i j
  exact quasiJacobiCollocationMatrix_entry_pos hq hα hβ x hx hroot i j

private theorem eval_weightNewtonPolynomial_eq_kernelWeight_div_zero
    {m q : ℕ} {δ s : ℝ} (hm : q ≤ m) (hδ : 0 < δ) (hs : 0 < s)
    (n : Fin q) :
    (weightNewtonPolynomial m δ s).eval (eigenvalue s n) =
      kernelWeight m δ s n / kernelWeight m δ s 0 := by
  rw [eval_weightNewtonPolynomial_eq_sum_newtonExpansionTerm
    (show (n : ℕ) ≤ m by exact le_trans n.isLt.le hm)]
  exact sum_newtonExpansionTerm_eq_kernelWeight_div_kernelWeight_zero
    (le_trans n.isLt.le hm) hδ hs

/-- The weighted Jacobi spectral kernel is strictly positive after
division by the two preceding Jacobi evaluations.  The result allows the
Newton degree to exceed the collocation dimension. -/
theorem kernelWeight_quasiJacobi_sum_div_eval_prev_pos
    {N m : ℕ} (hN : 1 ≤ N) (hm : N + 1 ≤ m) {α β τ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : Fin (N + 1) → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial (N + 1) α β τ).IsRoot (x i))
    (i j : Fin (N + 1)) :
    0 <
      (∑ l : Fin (N + 1),
          kernelWeight m δ (α + β + 2) l *
            (shiftedJacobiMonic l α β).eval (x i) *
            (shiftedJacobiMonic l α β).eval (x j) /
              shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic N α β).eval (x i) *
          (shiftedJacobiMonic N α β).eval (x j)) := by
  have hq : 2 ≤ N + 1 := by lia
  have hs : 0 < α + β + 2 := by linarith
  let A := quasiJacobiCollocationMatrix (N + 1) α β τ x
  let H := shiftedJacobiMonicNorm N α β
  let wi := kernelWeight m δ (α + β + 2) 0
  let ηi := quasiJacobiEta (N + 1) α β τ x i
  let ηj := quasiJacobiEta (N + 1) α β τ x j
  let pi := (shiftedJacobiMonic N α β).eval (x i)
  let pj := (shiftedJacobiMonic N α β).eval (x j)
  let S := ∑ l : Fin (N + 1),
    kernelWeight m δ (α + β + 2) l *
      (shiftedJacobiMonic l α β).eval (x i) *
      (shiftedJacobiMonic l α β).eval (x j) /
        shiftedJacobiMonicNorm l α β
  let T := ∑ l : Fin (N + 1),
    (weightNewtonPolynomial m δ (α + β + 2)).eval
        (eigenvalue (α + β + 2) l) *
      (shiftedJacobiMonic l α β).eval (x i) *
      (shiftedJacobiMonic l α β).eval (x j) /
        shiftedJacobiMonicNorm l α β
  have hentry : 0 <
      (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j := by
    simpa only [A] using
      aeval_weightNewtonPolynomial_quasiJacobiCollocationMatrix_entry_pos_of_le
        hN hm hα hβ hδ hδ1 x hx hroot i j
  have hηi : 0 < ηi :=
    quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hηj : 0 < ηj :=
    quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j
  have hpi : pi ≠ 0 :=
    shiftedJacobiMonic_eval_prev_ne_zero_of_roots hq hα hβ x hx hroot i
  have hpj : pj ≠ 0 :=
    shiftedJacobiMonic_eval_prev_ne_zero_of_roots hq hα hβ x hx hroot j
  have hH : 0 < H := shiftedJacobiMonicNorm_pos hα hβ N
  have hwi : 0 < wi := kernelWeight_pos (j := 0) (by simp) hδ hs
  have hsum : T = S / wi := by
    dsimp only [T, S]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    rw [eval_weightNewtonPolynomial_eq_kernelWeight_div_zero hm hδ hs l]
    ring
  have hspectral := aeval_quasiJacobiCollocationMatrix_apply_eq_kernel_sum
    hq hα hβ x hx hroot (weightNewtonPolynomial m δ (α + β + 2)) i j
  change (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j = H /
      (quasiJacobiCollocationScale (N + 1) α β τ x i *
        quasiJacobiCollocationScale (N + 1) α β τ x j) * T at hspectral
  rw [hsum] at hspectral
  rw [quasiJacobiCollocationScale, quasiJacobiCollocationScale] at hspectral
  change (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j =
      H / ((Real.sqrt ηi * pi) * (Real.sqrt ηj * pj)) * (S / wi) at hspectral
  have hformula : S / (pi * pj) =
      (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j * wi *
        Real.sqrt ηi * Real.sqrt ηj / H := by
    field_simp [hpi, hpj, hwi.ne', hH.ne', (Real.sqrt_pos.2 hηi).ne',
      (Real.sqrt_pos.2 hηj).ne'] at hspectral ⊢
    ring_nf at hspectral ⊢
    nlinarith [hspectral]
  change 0 < S / (pi * pj)
  rw [hformula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos hentry hwi) (Real.sqrt_pos.2 hηi))
      (Real.sqrt_pos.2 hηj)) hH

end RealRooted.JacobiDeformation
