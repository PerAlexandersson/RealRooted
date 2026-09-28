import RealRooted.JacobiDeformation.Basic

/-!
# Finite Jacobi kernel weights and their Newton expansion

Put `s = c + d` and `λ_j = j (j + s - 1)`, the eigenvalues of the positive
shifted-Jacobi differential operator.  The Jacobi deformation is controlled by
the finite kernel

`K_δ(r, z) = ∑_{j ≤ m} w_j(δ) p_j(r) p_j(z) / h_j`

in the monic shifted-Jacobi basis `p_j` with squared norms `h_j`, whose
weights are

`w_j(δ) = m! / (m - j)! · (m + s - 1 + δ)_j (δ)_{m - j} / (s)_{m + j}`.

This file defines the eigenvalues `eigenvalue`, the Newton products
`Λ_k(t) = ∏_{l < k} (t - λ_l)` (`newtonPolynomial`), the weights
`kernelWeight`, and the Newton coefficients

`a_k(δ) = (1 - δ)_k / ((m + δ - 1)^{(k)} (m + s)_k k!)`

(`newtonCoefficient`, with a falling factorial in the denominator).  It proves
strict positivity of every in-range weight and Newton coefficient, including
the empty-product and `k = 1` boundaries, and records the finite coefficient
algebra that diagonalizes a kernel with respect to an eigenbasis.  The Newton
expansion `w_j / w_0 = ∑_{k ≤ j} a_k Λ_k(λ_j)` itself is proved in
`RealRooted.JacobiDeformation.NewtonIdentity`.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Eigenvalues, Newton products, and kernel weights -/

/-- The positive differential eigenvalue `j (j + s - 1)`.  The library's
shifted-Jacobi differential operator itself has the negative of this
eigenvalue. -/
def eigenvalue (s : ℝ) (j : ℕ) : ℝ :=
  j * (j + s - 1)

@[simp]
theorem eigenvalue_zero (s : ℝ) : eigenvalue s 0 = 0 := by
  simp [eigenvalue]

theorem eigenvalue_succ_sub (s : ℝ) (j : ℕ) :
    eigenvalue s (j + 1) - eigenvalue s j = 2 * j + s := by
  unfold eigenvalue
  push_cast
  ring

theorem eigenvalue_strictMono {s : ℝ} (hs : 0 < s) :
    StrictMono (eigenvalue s) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [← sub_pos, eigenvalue_succ_sub]
  positivity

/-- The Newton factor polynomial
`Λₖ(t) = ∏_{l < k} (t - λ_l)`. -/
def newtonPolynomial (s : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ l ∈ Finset.range k, (X - C (eigenvalue s l))

@[simp]
theorem newtonPolynomial_zero (s : ℝ) : newtonPolynomial s 0 = 1 := by
  simp [newtonPolynomial]

theorem newtonPolynomial_succ (s : ℝ) (k : ℕ) :
    newtonPolynomial s (k + 1) =
      newtonPolynomial s k * (X - C (eigenvalue s k)) := by
  simp [newtonPolynomial, Finset.prod_range_succ]

/-- Exact evaluation of the Newton factors on the quadratic Jacobi spectrum:
`Λₖ(λ_j) = j^{\underline k} (j+s-1)_k`. -/
theorem eval_newtonPolynomial (s : ℝ) (k j : ℕ) :
    (newtonPolynomial s k).eval (eigenvalue s j) =
      (descPochhammer ℝ k).eval (j : ℝ) *
        (ascPochhammer ℝ k).eval ((j : ℝ) + s - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [newtonPolynomial_succ, eval_mul, eval_sub, eval_X, eval_C, ih,
        descPochhammer_succ_eval, ascPochhammer_succ_eval]
      unfold eigenvalue
      ring

theorem eval_newtonPolynomial_eq_zero {s : ℝ} {j k : ℕ} (hjk : j < k) :
    (newtonPolynomial s k).eval (eigenvalue s j) = 0 := by
  rw [eval_newtonPolynomial,
    descPochhammer_eval_coe_nat_of_lt (R := ℝ) hjk, zero_mul]

theorem eval_newtonPolynomial_pos {s : ℝ} (hs : 0 < s)
    {j k : ℕ} (hkj : k ≤ j) :
    0 < (newtonPolynomial s k).eval (eigenvalue s j) := by
  cases k with
  | zero => simp
  | succ k =>
      rw [eval_newtonPolynomial]
      apply mul_pos
      · rw [descPochhammer_eval_eq_descFactorial]
        exact_mod_cast Nat.descFactorial_pos.mpr hkj
      · apply ascPochhammer_pos
        have hj : 1 ≤ j := by lia
        have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
        linarith

/-- The kernel weight `w_j(δ)`. -/
def kernelWeight (m : ℕ) (δ s : ℝ) (j : ℕ) : ℝ :=
  ((descPochhammer ℝ j).eval (m : ℝ)) *
    risingFactorial ((m : ℝ) + s - 1 + δ) j *
    risingFactorial δ (m - j) /
    risingFactorial s (m + j)

/-- The Newton coefficient `a_k(δ)`. -/
def newtonCoefficient (m : ℕ) (δ s : ℝ) (k : ℕ) : ℝ :=
  risingFactorial (1 - δ) k /
    ((descPochhammer ℝ k).eval ((m : ℝ) + δ - 1) *
      risingFactorial ((m : ℝ) + s) k * k.factorial)

theorem kernelWeight_pos {m j : ℕ} {δ s : ℝ}
    (hjm : j ≤ m) (hδ : 0 < δ) (hs : 0 < s) :
    0 < kernelWeight m δ s j := by
  cases j with
  | zero =>
      simp only [kernelWeight, descPochhammer_zero, eval_one,
        risingFactorial_zero, mul_one, one_mul, Nat.sub_zero]
      exact div_pos (risingFactorial_pos _ hδ) (risingFactorial_pos _ hs)
  | succ j =>
      have hfall : 0 < (descPochhammer ℝ (j + 1)).eval (m : ℝ) := by
        rw [descPochhammer_eval_eq_descFactorial]
        exact_mod_cast Nat.descFactorial_pos.mpr hjm
      have hm : 1 ≤ m := by lia
      have hbase : 0 < (m : ℝ) + s - 1 + δ := by
        have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      unfold kernelWeight
      exact div_pos
        (mul_pos (mul_pos hfall (risingFactorial_pos _ hbase))
          (risingFactorial_pos _ hδ))
        (risingFactorial_pos _ hs)

theorem newtonCoefficient_pos {m k : ℕ} {δ s : ℝ}
    (hkm : k ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    0 < newtonCoefficient m δ s k := by
  have hfall : 0 <
      (descPochhammer ℝ k).eval ((m : ℝ) + δ - 1) := by
    apply descPochhammer_pos
    have hcast : (k : ℝ) ≤ m := by exact_mod_cast hkm
    linarith
  have hms : 0 < (m : ℝ) + s := by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  unfold newtonCoefficient
  exact div_pos (risingFactorial_pos _ (sub_pos.mpr hδ1))
    (mul_pos (mul_pos hfall (risingFactorial_pos _ hms)) hfac)

@[simp]
theorem newtonCoefficient_zero (m : ℕ) (δ s : ℝ) :
    newtonCoefficient m δ s 0 = 1 := by
  simp [newtonCoefficient]

theorem newtonCoefficient_one (m : ℕ) (δ s : ℝ) :
    newtonCoefficient m δ s 1 =
      (1 - δ) / (((m : ℝ) + δ - 1) * ((m : ℝ) + s)) := by
  simp [newtonCoefficient, risingFactorial]

theorem newtonCoefficient_one_pos {m : ℕ} {δ s : ℝ}
    (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    0 < newtonCoefficient m δ s 1 := by
  exact newtonCoefficient_pos hm hδ hδ1 hs

/-- The finite Newton polynomial `∑_k a_k(δ) Λ_k` formed from the positive
Newton coefficients. -/
def weightNewtonPolynomial (m : ℕ) (δ s : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    C (newtonCoefficient m δ s k) * newtonPolynomial s k

/-- The `k`th summand in the finite Newton expansion of `w_j / w_0`, after
evaluating at the spectral node `λ_j`. -/
def newtonExpansionTerm (m : ℕ) (δ s : ℝ) (j k : ℕ) : ℝ :=
  newtonCoefficient m δ s k *
    (descPochhammer ℝ k).eval (j : ℝ) *
      risingFactorial ((j : ℝ) + s - 1) k

/-- Evaluation of the Newton polynomial reduces exactly to its nonvanishing
lower-triangular summands. -/
theorem eval_weightNewtonPolynomial_eq_sum_newtonExpansionTerm
    {m j : ℕ} (hjm : j ≤ m) (δ s : ℝ) :
    (weightNewtonPolynomial m δ s).eval (eigenvalue s j) =
      ∑ k ∈ Finset.range (j + 1), newtonExpansionTerm m δ s j k := by
  rw [weightNewtonPolynomial, eval_finsetSum]
  have hsubset : Finset.range (j + 1) ⊆ Finset.range (m + 1) := by
    exact Finset.range_mono (by lia)
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [eval_mul, eval_C, eval_newtonPolynomial]
    simp only [newtonExpansionTerm, risingFactorial]
    ring
  · intro k hkm hkj
    have hjk : j < k := by
      exact Nat.lt_of_not_ge (by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hkj)
    rw [eval_mul, eval_C, eval_newtonPolynomial_eq_zero hjk, mul_zero]

/-- The empty-product endpoint of the Newton expansion. -/
@[simp] theorem eval_weightNewtonPolynomial_eigenvalue_zero
    (m : ℕ) (δ s : ℝ) :
    (weightNewtonPolynomial m δ s).eval (eigenvalue s 0) = 1 := by
  rw [eval_weightNewtonPolynomial_eq_sum_newtonExpansionTerm
    (m := m) (j := 0) (by simp)]
  simp [newtonExpansionTerm]

/-- The Newton expansion at its `j = 0` boundary, with the normalizing weight
proved nonzero from the strict parameter hypotheses. -/
theorem kernelWeight_div_zero_eq_eval_weightNewtonPolynomial
    {m : ℕ} {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    kernelWeight m δ s 0 / kernelWeight m δ s 0 =
      (weightNewtonPolynomial m δ s).eval (eigenvalue s 0) := by
  rw [eval_weightNewtonPolynomial_eigenvalue_zero,
    div_self (kernelWeight_pos (j := 0) (by simp) hδ hs).ne']

theorem eval_weightNewtonPolynomial_pos {m j : ℕ} {δ s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    0 < (weightNewtonPolynomial m δ s).eval (eigenvalue s j) := by
  rw [weightNewtonPolynomial, eval_finsetSum]
  apply Finset.sum_pos'
  · intro k hk
    simp only [mem_range] at hk
    rw [eval_mul, eval_C]
    by_cases hkj : k ≤ j
    · exact (mul_pos (newtonCoefficient_pos (by lia) hδ hδ1 hs)
        (eval_newtonPolynomial_pos hs hkj)).le
    · rw [eval_newtonPolynomial_eq_zero (Nat.lt_of_not_ge hkj), mul_zero]
  · refine ⟨0, mem_range.mpr (Nat.zero_lt_succ m), ?_⟩
    simp

/-! ## Normalization of the Jacobi kernel weights -/

/-- The normalized Jacobi kernel weight has the finite Pochhammer quotient
needed by the Newton expansion. -/
theorem kernelWeight_div_kernelWeight_zero {m j : ℕ} {δ s : ℝ}
    (hjm : j ≤ m) (hδ : 0 < δ) (hs : 0 < s) :
    kernelWeight m δ s j / kernelWeight m δ s 0 =
      (descPochhammer ℝ j).eval (m : ℝ) *
          risingFactorial ((m : ℝ) + s - 1 + δ) j /
        ((descPochhammer ℝ j).eval ((m : ℝ) + δ - 1) *
          risingFactorial ((m : ℝ) + s) j) := by
  have htail_pos : 0 < risingFactorial δ (m - j) :=
    risingFactorial_pos _ hδ
  have hfall_pos : 0 < (descPochhammer ℝ j).eval ((m : ℝ) + δ - 1) := by
    apply descPochhammer_pos
    have hj : (j : ℝ) ≤ m := by exact_mod_cast hjm
    linarith
  have hsm_pos : 0 < (m : ℝ) + s := by
    positivity
  have hbase_pos : 0 < risingFactorial s m :=
    risingFactorial_pos _ hs
  have hhead_pos : 0 < risingFactorial ((m : ℝ) + s) j :=
    risingFactorial_pos _ hsm_pos
  have hsplit_delta := risingFactorial_sub_mul_descPochhammer δ hjm
  have hsplit_s := (risingFactorial_add s m j).symm
  simp only [kernelWeight, descPochhammer_zero, eval_one, risingFactorial_zero,
    mul_one, one_mul, Nat.sub_zero]
  rw [← hsplit_delta, ← hsplit_s]
  simp only [Nat.add_zero, add_comm s (m : ℝ)]
  field_simp [ne_of_gt htail_pos, ne_of_gt hfall_pos, ne_of_gt hbase_pos,
    ne_of_gt hhead_pos]

/-! ## Finite eigenbasis kernel diagonalization

This section records the finite coefficient algebra behind the diagonal part
of the Jacobi kernel expansion; no collocation matrix or spectral
decomposition is involved.  Two operator actions on a kernel written in a
finite eigenbasis agree exactly when the off-diagonal coefficients vanish for
distinct eigenvalues.
-/

/-- The coefficient relation obtained by comparing two diagonal operator
actions on a finite eigenbasis. -/
def EigenCoefficientCondition {n : ℕ} (eigenvalue : Fin n → ℝ)
    (coefficient : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, (eigenvalue i - eigenvalue j) * coefficient i j = 0

/-- Distinct eigenvalues force every off-diagonal coefficient satisfying the
eigenvalue-difference relation to vanish. -/
theorem eigenCoefficient_eq_zero_of_ne {n : ℕ} {eigenvalue : Fin n → ℝ}
    {coefficient : Fin n → Fin n → ℝ} (heigenvalue : Function.Injective eigenvalue)
    (hcoefficient : EigenCoefficientCondition eigenvalue coefficient)
    {i j : Fin n} (hij : i ≠ j) :
    coefficient i j = 0 := by
  have hne : eigenvalue i - eigenvalue j ≠ 0 := by
    exact sub_ne_zero.mpr fun h => hij (heigenvalue h)
  exact (mul_eq_zero.mp (hcoefficient i j)).resolve_left hne

/-- A finite coefficient array satisfying the distinct-eigenvalue relation is
diagonal. -/
theorem eigenCoefficient_diagonal {n : ℕ} {eigenvalue : Fin n → ℝ}
    {coefficient : Fin n → Fin n → ℝ} (heigenvalue : Function.Injective eigenvalue)
    (hcoefficient : EigenCoefficientCondition eigenvalue coefficient) :
    ∀ i j, i ≠ j → coefficient i j = 0 := by
  intro i j hij
  exact eigenCoefficient_eq_zero_of_ne heigenvalue hcoefficient hij

/-- Apply an operator to the first variable of a finite separable polynomial
kernel, represented only by its finite coefficient array. -/
def eigenKernelActionLeft {n : ℕ} (coefficient : Fin n → Fin n → ℝ)
    (basis : Fin n → ℝ[X]) (operator : ℝ[X] →ₗ[ℝ] ℝ[X]) (r z : ℝ) : ℝ :=
  ∑ i, ∑ j,
    coefficient i j * (operator (basis i)).eval r * (basis j).eval z

/-- Apply an operator to the second variable of a finite separable polynomial
kernel, represented only by its finite coefficient array. -/
def eigenKernelActionRight {n : ℕ} (coefficient : Fin n → Fin n → ℝ)
    (basis : Fin n → ℝ[X]) (operator : ℝ[X] →ₗ[ℝ] ℝ[X]) (r z : ℝ) : ℝ :=
  ∑ i, ∑ j,
    coefficient i j * (basis i).eval r * (operator (basis j)).eval z

/-- A diagonal finite eigenbasis kernel has identical first- and
second-variable operator actions. -/
theorem eigenKernelAction_eq_of_diagonal {n : ℕ} {coefficient : Fin n → Fin n → ℝ}
    {basis : Fin n → ℝ[X]} {operator : ℝ[X] →ₗ[ℝ] ℝ[X]}
    {eigenvalue : Fin n → ℝ}
    (hdiagonal : ∀ i j, i ≠ j → coefficient i j = 0)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (r z : ℝ) :
    eigenKernelActionLeft coefficient basis operator r z =
      eigenKernelActionRight coefficient basis operator r z := by
  classical
  unfold eigenKernelActionLeft eigenKernelActionRight
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [hoperator i]
    simp only [eval_mul, eval_C]
    ring
  · rw [hdiagonal i j hij]
    ring

/-- Distinct eigenvalues turn the coefficient relation into equality of the
two finite eigenbasis operator actions. -/
theorem eigenKernelAction_eq_of_distinct {n : ℕ} {coefficient : Fin n → Fin n → ℝ}
    {basis : Fin n → ℝ[X]} {operator : ℝ[X] →ₗ[ℝ] ℝ[X]}
    {eigenvalue : Fin n → ℝ} (heigenvalue : Function.Injective eigenvalue)
    (hcoefficient : EigenCoefficientCondition eigenvalue coefficient)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (r z : ℝ) :
    eigenKernelActionLeft coefficient basis operator r z =
      eigenKernelActionRight coefficient basis operator r z := by
  exact eigenKernelAction_eq_of_diagonal
    (eigenCoefficient_diagonal heigenvalue hcoefficient) hoperator r z

/-! ### Coefficient extraction

For a linearly independent eigenbasis, equality of the two operator actions
forces the eigenvalue-difference coefficient relation.
-/

/-- Equality of the two finite eigenbasis actions forces the
eigenvalue-difference coefficient relation. -/
theorem eigenCoefficientCondition_of_action_eq {n : ℕ}
    {coefficient : Fin n → Fin n → ℝ} {basis : Fin n → ℝ[X]}
    {operator : ℝ[X] →ₗ[ℝ] ℝ[X]} {eigenvalue : Fin n → ℝ}
    (hbasis : LinearIndependent ℝ basis)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (haction : ∀ r z,
      eigenKernelActionLeft coefficient basis operator r z =
        eigenKernelActionRight coefficient basis operator r z) :
    EigenCoefficientCondition eigenvalue coefficient := by
  classical
  intro i j
  have houter (z : ℝ) (i : Fin n) :
      ∑ j, (eigenvalue i - eigenvalue j) * coefficient i j * (basis j).eval z = 0 := by
    have hsum : ∑ i,
        (∑ j, (eigenvalue i - eigenvalue j) * coefficient i j * (basis j).eval z) •
          basis i = 0 := by
      apply Polynomial.funext
      intro r
      rw [eval_finsetSum]
      simp only [eval_smul]
      have hrewrite :
          (∑ i, (∑ j,
              (eigenvalue i - eigenvalue j) * coefficient i j * (basis j).eval z) *
                (basis i).eval r) =
            eigenKernelActionLeft coefficient basis operator r z -
              eigenKernelActionRight coefficient basis operator r z := by
        unfold eigenKernelActionLeft eigenKernelActionRight
        simp_rw [hoperator]
        simp only [eval_mul, eval_C]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simpa only [smul_eq_mul, eval_zero] using
        hrewrite.trans (sub_eq_zero.mpr (haction r z))
    exact Fintype.linearIndependent_iff.mp hbasis _ hsum i
  have hinner (i : Fin n) :
      ∑ j, ((eigenvalue i - eigenvalue j) * coefficient i j) • basis j = 0 := by
    apply Polynomial.funext
    intro z
    rw [eval_finsetSum]
    simpa only [eval_smul, smul_eq_mul, eval_zero] using houter z i
  exact Fintype.linearIndependent_iff.mp hbasis _ (hinner i) j

/-- With distinct eigenvalues, equality of the two finite eigenbasis actions
forces every off-diagonal coefficient to vanish. -/
theorem eigenCoefficient_diagonal_of_action_eq {n : ℕ}
    {coefficient : Fin n → Fin n → ℝ} {basis : Fin n → ℝ[X]}
    {operator : ℝ[X] →ₗ[ℝ] ℝ[X]} {eigenvalue : Fin n → ℝ}
    (heigenvalue : Function.Injective eigenvalue)
    (hbasis : LinearIndependent ℝ basis)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (haction : ∀ r z,
      eigenKernelActionLeft coefficient basis operator r z =
        eigenKernelActionRight coefficient basis operator r z) :
    ∀ i j, i ≠ j → coefficient i j = 0 := by
  exact eigenCoefficient_diagonal heigenvalue
    (eigenCoefficientCondition_of_action_eq hbasis hoperator haction)

end RealRooted.JacobiDeformation
