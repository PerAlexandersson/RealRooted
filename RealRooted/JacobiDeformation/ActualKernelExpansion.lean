import RealRooted.JacobiDeformation.BoundaryProjection
import RealRooted.JacobiDeformation.Collocation
import RealRooted.JacobiDeformation.JacobiFiniteExpansion
import RealRooted.JacobiDeformation.JacobiNormalizationBridge
import RealRooted.JacobiDeformation.KernelDiagonalizationForward

/-!
# Actual finite Appell--Jacobi kernel expansion

This module expands the concrete Appell kernel in the finite monic Jacobi
basis, uses equality of its two differential actions to kill all off-diagonal
coefficients, and identifies the remaining diagonal coefficients by the
checked boundary projection.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The Bernstein monomial, truncated to the degree triangle of the Appell
kernel. -/
def truncatedJacobiBernstein (m i j : ℕ) : ℝ[X] :=
  if i + j ≤ m then jacobiBernstein i j else 0

private theorem natDegree_jacobiBernstein_le (i j : ℕ) :
    (jacobiBernstein i j).natDegree ≤ i + j := by
  have hX : (X ^ i : ℝ[X]).natDegree ≤ i := by
    simpa using Polynomial.natDegree_pow_le_of_le i Polynomial.natDegree_X_le
  have hOneSubX : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    simp [sub_eq_add_neg]
  have hOneSubXPow : ((1 - X : ℝ[X]) ^ j).natDegree ≤ j := by
    simpa using Polynomial.natDegree_pow_le_of_le j hOneSubX
  exact natDegree_mul_le.trans (Nat.add_le_add hX hOneSubXPow)

private theorem natDegree_truncatedJacobiBernstein_le (m i j : ℕ) :
    (truncatedJacobiBernstein m i j).natDegree ≤ m := by
  rw [truncatedJacobiBernstein]
  split_ifs with hij
  · exact (natDegree_jacobiBernstein_le i j).trans hij
  · simp

/-- Chosen coordinates of a truncated Bernstein monomial in the first
`m + 1` monic shifted-Jacobi polynomials. -/
def jacobiBernsteinCoefficient (m i j : ℕ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) : Fin (m + 1) → ℝ :=
  Classical.choose (exists_sum_C_mul_shiftedJacobiMonic_of_natDegree_le
    (c - 1) (d - 1) (by linarith) (by linarith) m
    (truncatedJacobiBernstein m i j)
    (natDegree_truncatedJacobiBernstein_le m i j))

theorem truncatedJacobiBernstein_eq_sum (m i j : ℕ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    truncatedJacobiBernstein m i j =
      ∑ a, C (jacobiBernsteinCoefficient m i j c d hc hd a) *
        shiftedJacobiMonic a (c - 1) (d - 1) :=
  Classical.choose_spec (exists_sum_C_mul_shiftedJacobiMonic_of_natDegree_le
    (c - 1) (d - 1) (by linarith) (by linarith) m
    (truncatedJacobiBernstein m i j)
    (natDegree_truncatedJacobiBernstein_le m i j))

/-- The concrete coefficient matrix obtained by expanding both Bernstein
factors of the actual Appell kernel. -/
def actualKernelCoefficientMatrix (m : ℕ) (b c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (a e : Fin (m + 1)) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellKernelCoefficient m b c d i j *
      jacobiBernsteinCoefficient m i j c d hc hd a *
      jacobiBernsteinCoefficient m i j c d hc hd e

private theorem coefficient_mul_eval_truncated (m i j : ℕ) (b c d x : ℝ) :
    appellKernelCoefficient m b c d i j * (jacobiBernstein i j).eval x =
      appellKernelCoefficient m b c d i j *
        (truncatedJacobiBernstein m i j).eval x := by
  by_cases hij : i + j ≤ m
  · rw [truncatedJacobiBernstein, if_pos hij]
  · rw [appellKernelCoefficient, if_neg hij]
    ring

private theorem coefficient_mul_eval_truncated_two
    (m i j : ℕ) (b c d r z : ℝ) :
    appellKernelCoefficient m b c d i j * (jacobiBernstein i j).eval r *
        (jacobiBernstein i j).eval z =
      appellKernelCoefficient m b c d i j *
        (truncatedJacobiBernstein m i j).eval r *
        (truncatedJacobiBernstein m i j).eval z := by
  rw [coefficient_mul_eval_truncated m i j b c d r]
  by_cases hij : i + j ≤ m
  · rw [truncatedJacobiBernstein, if_pos hij]
  · rw [appellKernelCoefficient, if_neg hij]
    ring

private theorem appellKernelSummand_eq_truncated
    (m i j : ℕ) (b c d r z : ℝ) :
    appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
        (jacobiBernstein i j).eval r =
      appellKernelCoefficient m b c d i j *
        (truncatedJacobiBernstein m i j).eval r *
        (truncatedJacobiBernstein m i j).eval z := by
  by_cases hij : i + j ≤ m
  · rw [truncatedJacobiBernstein, if_pos hij]
    simp only [jacobiBernstein, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    ring
  · rw [appellKernelCoefficient, if_neg hij]
    ring

private theorem sum_comm_four {α β γ ε : Type*}
    (sα : Finset α) (sβ : Finset β) (sγ : Finset γ) (sε : Finset ε)
    (f : α → β → γ → ε → ℝ) :
    (∑ a ∈ sα, ∑ b ∈ sβ, ∑ g ∈ sγ, ∑ e ∈ sε, f a b g e) =
      ∑ g ∈ sγ, ∑ e ∈ sε, ∑ a ∈ sα, ∑ b ∈ sβ, f a b g e := by
  calc
    _ = ∑ a ∈ sα, ∑ g ∈ sγ, ∑ b ∈ sβ, ∑ e ∈ sε, f a b g e := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ g ∈ sγ, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ e ∈ sε, f a b g e := by
      rw [Finset.sum_comm]
    _ = ∑ g ∈ sγ, ∑ a ∈ sα, ∑ e ∈ sε, ∑ b ∈ sβ, f a b g e := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ g ∈ sγ, ∑ e ∈ sε, ∑ a ∈ sα, ∑ b ∈ sβ, f a b g e := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]

private theorem sum_rank_one {α β γ ε : Type*}
    (sα : Finset α) (sβ : Finset β) (sγ : Finset γ) (sε : Finset ε)
    (w : α → β → ℝ) (u : α → β → γ → ℝ) (v : α → β → ε → ℝ)
    (p : γ → ℝ) (q : ε → ℝ) :
    (∑ a ∈ sα, ∑ b ∈ sβ,
      w a b * (∑ g ∈ sγ, u a b g * p g) * (∑ e ∈ sε, v a b e * q e)) =
      ∑ g ∈ sγ, ∑ e ∈ sε,
        (∑ a ∈ sα, ∑ b ∈ sβ, w a b * u a b g * v a b e) * p g * q e := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine (sum_comm_four sα sβ sε sγ (fun a b e g =>
    w a b * (u a b g * p g) * (v a b e * q e))).trans ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Pointwise finite monic-Jacobi expansion of the actual Appell kernel. -/
theorem eval_appellJacobiKernel_eq_actualKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (r z : ℝ) :
    (appellJacobiKernel m b c d z).eval r =
      ∑ a, ∑ e,
        actualKernelCoefficientMatrix m b c d hc hd a e *
          (shiftedJacobiMonic a (c - 1) (d - 1)).eval r *
          (shiftedJacobiMonic e (c - 1) (d - 1)).eval z := by
  classical
  unfold appellJacobiKernel
  simp_rw [eval_finsetSum, eval_mul, eval_C]
  simp_rw [appellKernelSummand_eq_truncated]
  simp_rw [truncatedJacobiBernstein_eq_sum m _ _ hc hd, eval_finsetSum,
    eval_mul, eval_C]
  simpa only [actualKernelCoefficientMatrix] using
    sum_rank_one (Finset.range (m + 1)) (Finset.range (m + 1))
      (Finset.univ : Finset (Fin (m + 1))) (Finset.univ : Finset (Fin (m + 1)))
      (fun i j => appellKernelCoefficient m b c d i j)
      (fun i j a => jacobiBernsteinCoefficient m i j c d hc hd a)
      (fun i j e => jacobiBernsteinCoefficient m i j c d hc hd e)
      (fun a => (shiftedJacobiMonic a (c - 1) (d - 1)).eval r)
      (fun e => (shiftedJacobiMonic e (c - 1) (d - 1)).eval z)

/-- Polynomial-valued form of the concrete finite kernel expansion. -/
theorem appellJacobiKernel_eq_actualKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m b c d z =
      ∑ a, ∑ e,
        C (actualKernelCoefficientMatrix m b c d hc hd a e *
          (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) *
          shiftedJacobiMonic a (c - 1) (d - 1) := by
  apply Polynomial.funext
  intro r
  rw [eval_appellJacobiKernel_eq_actualKernelCoefficientMatrix m b hc hd]
  simp_rw [eval_finsetSum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem actualKernelCoefficientMatrix_comm (m : ℕ) (b c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (a e : Fin (m + 1)) :
    actualKernelCoefficientMatrix m b c d hc hd a e =
      actualKernelCoefficientMatrix m b c d hc hd e a := by
  unfold actualKernelCoefficientMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem appellJacobiKernel_eq_actualKernelCoefficientMatrix_swapped
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m b c d z =
      ∑ a, ∑ e,
        C (actualKernelCoefficientMatrix m b c d hc hd a e *
          (shiftedJacobiMonic a (c - 1) (d - 1)).eval z) *
          shiftedJacobiMonic e (c - 1) (d - 1) := by
  rw [appellJacobiKernel_eq_actualKernelCoefficientMatrix m b hc hd z,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  rw [actualKernelCoefficientMatrix_comm m b c d hc hd]

private theorem eigenKernelActionLeft_actualKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (r z : ℝ) :
    eigenKernelActionLeft (actualKernelCoefficientMatrix m b c d hc hd)
        (fun a : Fin (m + 1) => shiftedJacobiMonic a (c - 1) (d - 1))
        (jacobiDifferentialOperatorLinearMap c (c + d)) r z =
      (jacobiDifferentialOperator c (c + d)
        (appellJacobiKernel m b c d z)).eval r := by
  rw [appellJacobiKernel_eq_actualKernelCoefficientMatrix m b hc hd z]
  unfold eigenKernelActionLeft
  change _ = ((jacobiDifferentialOperatorLinearMap c (c + d))
    (∑ a, ∑ e,
      C (actualKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic a (c - 1) (d - 1))).eval r
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro e _
  rw [show C (actualKernelCoefficientMatrix m b c d hc hd a e *
      (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic a (c - 1) (d - 1) =
      (actualKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) •
          shiftedJacobiMonic a (c - 1) (d - 1) by
    rw [smul_eq_C_mul]]
  rw [map_smul, eval_smul]
  ring

private theorem eigenKernelActionRight_actualKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (r z : ℝ) :
    eigenKernelActionRight (actualKernelCoefficientMatrix m b c d hc hd)
        (fun a : Fin (m + 1) => shiftedJacobiMonic a (c - 1) (d - 1))
        (jacobiDifferentialOperatorLinearMap c (c + d)) r z =
      (jacobiDifferentialOperator c (c + d)
        (appellJacobiKernel m b c d r)).eval z := by
  rw [appellJacobiKernel_eq_actualKernelCoefficientMatrix_swapped m b hc hd r]
  unfold eigenKernelActionRight
  change _ = ((jacobiDifferentialOperatorLinearMap c (c + d))
    (∑ a, ∑ e,
      C (actualKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval r) *
        shiftedJacobiMonic e (c - 1) (d - 1))).eval z
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro e _
  rw [show C (actualKernelCoefficientMatrix m b c d hc hd a e *
      (shiftedJacobiMonic a (c - 1) (d - 1)).eval r) *
        shiftedJacobiMonic e (c - 1) (d - 1) =
      (actualKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval r) •
          shiftedJacobiMonic e (c - 1) (d - 1) by
    rw [smul_eq_C_mul]]
  rw [map_smul, eval_smul]
  ring

private theorem jacobiDifferentialOperatorLinearMap_shiftedJacobiMonic
    (c d : ℝ) (a : Fin (m + 1)) :
    jacobiDifferentialOperatorLinearMap c (c + d)
        (shiftedJacobiMonic a (c - 1) (d - 1)) =
      C (-eigenvalue (c + d) a) * shiftedJacobiMonic a (c - 1) (d - 1) := by
  have h := positiveJacobiOperator_shiftedJacobiMonic a (c - 1) (d - 1)
  simp only [positiveJacobiOperator, LinearMap.neg_apply] at h
  rw [show c - 1 + 1 = c by ring,
    show c - 1 + (d - 1) + 2 = c + d by ring] at h
  apply neg_injective
  rw [h, C_neg]
  ring

/-- The coefficient matrix of the actual Appell kernel is diagonal in the
positive Jacobi parameter range. -/
theorem actualKernelCoefficientMatrix_offDiagonal_eq_zero
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ a e : Fin (m + 1), a ≠ e →
      actualKernelCoefficientMatrix m b c d hc hd a e = 0 := by
  let basis : Fin (m + 1) → ℝ[X] := fun a =>
    shiftedJacobiMonic a (c - 1) (d - 1)
  let operator := jacobiDifferentialOperatorLinearMap c (c + d)
  let eigen : Fin (m + 1) → ℝ := fun a => -eigenvalue (c + d) a
  have heigen : Function.Injective eigen := by
    intro a e hae
    apply Fin.ext
    apply (eigenvalue_strictMono (by linarith : 0 < c + d)).injective
    exact neg_injective hae
  have hbasis : LinearIndependent ℝ basis :=
    shiftedJacobiMonic_linearIndependent_fin (c - 1) (d - 1)
      (by linarith) (by linarith) m
  have hoperator : ∀ a, operator (basis a) = C (eigen a) * basis a := by
    intro a
    exact jacobiDifferentialOperatorLinearMap_shiftedJacobiMonic c d a
  apply eigenCoefficient_diagonal_of_action_eq heigen hbasis hoperator
  intro r z
  rw [eigenKernelActionLeft_actualKernelCoefficientMatrix m b hc hd,
    eigenKernelActionRight_actualKernelCoefficientMatrix m b hc hd]
  exact eval_jacobiDifferentialOperator_appellJacobiKernel_eq m b hc hd

/-- Diagonal form of the actual Appell kernel before the boundary coefficients
are identified. -/
theorem appellJacobiKernel_eq_diagonal_monic_sum
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m b c d z =
      ∑ a : Fin (m + 1),
        C (actualKernelCoefficientMatrix m b c d hc hd a a *
          (shiftedJacobiMonic a (c - 1) (d - 1)).eval z) *
          shiftedJacobiMonic a (c - 1) (d - 1) := by
  rw [appellJacobiKernel_eq_actualKernelCoefficientMatrix m b hc hd z]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · intro e _ hea
    rw [actualKernelCoefficientMatrix_offDiagonal_eq_zero m b hc hd a e (Ne.symm hea)]
    simp
  · simp

private theorem normalizedJacobiFunctional_sum' {ι : Type*} (c d : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    normalizedJacobiFunctional c d (∑ x ∈ s, p x) =
      ∑ x ∈ s, normalizedJacobiFunctional c d (p x) := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_sum, Finset.sum_div]

private theorem normalizedJacobiFunctional_C_mul' (c d a : ℝ) (p : ℝ[X]) :
    normalizedJacobiFunctional c d (C a * p) =
      a * normalizedJacobiFunctional c d p := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_C_mul]
  ring

private theorem normalizedJacobiFunctional_normalized_mul_monic
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j k : ℕ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * shiftedJacobiMonic k (c - 1) (d - 1)) =
      if j = k then
        (shiftedJacobiMonic k (c - 1) (d - 1)).eval 0 *
          normalizedJacobiNorm c d k
      else 0 := by
  rw [← C_eval_zero_mul_normalizedShiftedJacobi hc hd k]
  rw [show normalizedShiftedJacobi j c d *
      (C ((shiftedJacobiMonic k (c - 1) (d - 1)).eval 0) *
        normalizedShiftedJacobi k c d) =
    C ((shiftedJacobiMonic k (c - 1) (d - 1)).eval 0) *
      (normalizedShiftedJacobi j c d * normalizedShiftedJacobi k c d) by ring,
    normalizedJacobiFunctional_C_mul']
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    simp only [eval_mul, eval_C]
    rw [normalizedShiftedJacobi_eval_zero hc]
    simp only [normalizedJacobiNorm]
    ring
  · rw [if_neg hjk,
      normalizedJacobiFunctional_pairwise_orthogonal hc hd hjk]
    ring

private theorem normalizedJacobiFunctional_diagonal_term
    {m : ℕ} (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (j k : Fin (m + 1)) (z : ℝ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d *
          (C (actualKernelCoefficientMatrix m b c d hc hd k k *
              (shiftedJacobiMonic k (c - 1) (d - 1)).eval z) *
            shiftedJacobiMonic k (c - 1) (d - 1))) =
      if j = k then
        actualKernelCoefficientMatrix m b c d hc hd k k *
          (shiftedJacobiMonic k (c - 1) (d - 1)).eval z *
          (shiftedJacobiMonic k (c - 1) (d - 1)).eval 0 *
          normalizedJacobiNorm c d k
      else 0 := by
  rw [show normalizedShiftedJacobi j c d *
      (C (actualKernelCoefficientMatrix m b c d hc hd k k *
          (shiftedJacobiMonic k (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic k (c - 1) (d - 1)) =
    C (actualKernelCoefficientMatrix m b c d hc hd k k *
      (shiftedJacobiMonic k (c - 1) (d - 1)).eval z) *
      (normalizedShiftedJacobi j c d *
        shiftedJacobiMonic k (c - 1) (d - 1)) by ring,
    normalizedJacobiFunctional_C_mul',
    normalizedJacobiFunctional_normalized_mul_monic hc hd]
  by_cases hjk : j = k
  · subst k
    simp
    ring
  · have hval : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    rw [if_neg hjk, if_neg hval]
    ring

/-- The diagonal monic coefficient is determined by the concrete boundary
weight, with all normalization factors retained explicitly. -/
theorem actualKernelCoefficientMatrix_diagonal_weight
    {m : ℕ} (δ : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (a : Fin (m + 1)) :
    actualKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ) c d hc hd a a *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval 0 ^ 2 *
        normalizedJacobiNorm c d a =
      kernelWeight m δ (c + d) a := by
  have hprojection := normalizedJacobiFunctional_appellJacobiKernel_zero
    (m := m) (j := a) (Nat.le_of_lt_succ a.isLt) hc hd δ
  rw [appellJacobiKernel_eq_diagonal_monic_sum m
    ((m : ℝ) + c + d - 1 + δ) hc hd 0, Finset.mul_sum,
    normalizedJacobiFunctional_sum'] at hprojection
  simp_rw [normalizedJacobiFunctional_diagonal_term
    ((m : ℝ) + c + d - 1 + δ) hc hd a] at hprojection
  rw [Finset.sum_eq_single a] at hprojection
  · simpa only [if_pos, eval_zero, pow_two, mul_assoc] using hprojection
  · intro k _ hka
    rw [if_neg (Ne.symm hka)]
  · simp

private theorem diagonal_monic_term_eq_normalized
    {m : ℕ} (δ : ℝ) {c d z : ℝ} (hc : 0 < c) (hd : 0 < d)
    (a : Fin (m + 1)) :
    C (actualKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
          c d hc hd a a *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic a (c - 1) (d - 1) =
      C (kernelWeight m δ (c + d) a / normalizedJacobiNorm c d a *
        (normalizedShiftedJacobi a c d).eval z) *
        normalizedShiftedJacobi a c d := by
  let p0 := (shiftedJacobiMonic a (c - 1) (d - 1)).eval 0
  let H := normalizedJacobiNorm c d a
  have hH : H ≠ 0 := (normalizedJacobiNorm_pos hc hd a).ne'
  have hp := C_eval_zero_mul_normalizedShiftedJacobi hc hd a
  have hweight := actualKernelCoefficientMatrix_diagonal_weight δ hc hd a
  change actualKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
      c d hc hd a a * p0 ^ 2 * H = kernelWeight m δ (c + d) a at hweight
  rw [← hp]
  simp only [eval_mul, eval_C]
  rw [← mul_assoc, ← C_mul]
  congr 1
  rw [Polynomial.C_inj]
  change actualKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
      c d hc hd a a * (p0 * (normalizedShiftedJacobi a c d).eval z) * p0 =
    kernelWeight m δ (c + d) a / H * (normalizedShiftedJacobi a c d).eval z
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hH).2
  calc
    actualKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
          c d hc hd a a * (p0 * (normalizedShiftedJacobi a c d).eval z) * p0 * H =
        (actualKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
          c d hc hd a a * p0 ^ 2 * H) *
            (normalizedShiftedJacobi a c d).eval z := by ring
    _ = kernelWeight m δ (c + d) a *
          (normalizedShiftedJacobi a c d).eval z := by rw [hweight]

/-- Concrete equation-(4) spectral expansion of the actual finite Appell
kernel in value-one shifted-Jacobi polynomials. -/
theorem appellJacobiKernel_eq_normalizedShiftedJacobi_sum
    (m : ℕ) (δ : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d z =
      ∑ a : Fin (m + 1),
        C (kernelWeight m δ (c + d) a / normalizedJacobiNorm c d a *
          (normalizedShiftedJacobi a c d).eval z) *
          normalizedShiftedJacobi a c d := by
  rw [appellJacobiKernel_eq_diagonal_monic_sum m
    ((m : ℝ) + c + d - 1 + δ) hc hd z]
  apply Finset.sum_congr rfl
  intro a _
  exact diagonal_monic_term_eq_normalized δ hc hd a

end RealRooted.JacobiDeformation
