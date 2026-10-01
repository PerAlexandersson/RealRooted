import RealRooted.Jacobi.Favard
import RealRooted.JacobiDeformation.Appell
import RealRooted.JacobiDeformation.BoundaryProjection
import RealRooted.JacobiDeformation.Moment
import RealRooted.JacobiDeformation.SpectralKernel

/-!
# The diagonal Jacobi kernel expansion

The Appell--Jacobi kernel has the finite spectral expansion

`K_δ(r, z) = ∑_{j ≤ m} w_j(δ) p_j(r) p_j(z) / h_j`

in the monic shifted-Jacobi polynomials `p_j` with raw squared norms `h_j`.
We expand both Bernstein factors of the Appell kernel in the finite monic
Jacobi basis; equality of the two Jacobi operator actions kills every
off-diagonal coefficient because the eigenvalues are distinct, and the
boundary projection identifies the diagonal coefficients with the weights
`w_j(δ)`.  The last two sections pass between the value-one and monic
normalizations and express the Jacobi deformation at an image value through
the raw kernel; this is the scalar interface of every critical-point case.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Finite expansions in the monic shifted-Jacobi family

These are finite restrictions of the monic Favard polynomial sequence; no
separate basis construction is introduced.
-/

/-- Any finite initial segment of the monic shifted-Jacobi Favard family is
linearly independent. -/
theorem shiftedJacobiMonic_linearIndependent_fin
    (alpha beta : ℝ) (halpha : -1 < alpha) (hbeta : -1 < beta) (m : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin (m + 1) => shiftedJacobiMonic i alpha beta) := by
  let hrec := shiftedJacobiMonic_satisfiesFavardRecurrence alpha beta halpha hbeta
  change LinearIndependent ℝ (fun i : Fin (m + 1) => hrec.toSequence i)
  exact hrec.toSequence.linearIndependent.comp Fin.val Fin.val_injective

/-- Every polynomial of natural degree at most `m` has a finite expansion in
the first `m + 1` monic shifted-Jacobi polynomials. -/
theorem exists_sum_C_mul_shiftedJacobiMonic_of_natDegree_le
    (alpha beta : ℝ) (halpha : -1 < alpha) (hbeta : -1 < beta) (m : ℕ)
    (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∃ a : Fin (m + 1) → ℝ,
      p = ∑ i, C (a i) * shiftedJacobiMonic i alpha beta := by
  let hrec := shiftedJacobiMonic_satisfiesFavardRecurrence alpha beta halpha hbeta
  let S := hrec.toSequence
  have hCoeff : ∀ i ≤ m, IsUnit (S i).leadingCoeff := by
    intro i _
    simpa only [S, SatisfiesFavardRecurrence.toSequence_apply,
      (hrec.monic i).leadingCoeff] using (isUnit_one : IsUnit (1 : ℝ))
  have hspan : Submodule.span ℝ (S '' Set.Iic m) = Polynomial.degreeLE ℝ m :=
    S.span_degreeLE hCoeff
  have himage : Set.range (fun i : Fin (m + 1) => S i) = S '' Set.Iic m := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, Set.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, Nat.lt_succ_iff.mpr (Set.mem_Iic.mp hi)⟩, rfl⟩
  have hp_span : p ∈ Submodule.span ℝ (Set.range (fun i : Fin (m + 1) => S i)) := by
    rw [himage, hspan]
    exact Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hp)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp_span
  refine ⟨a, ?_⟩
  simpa only [S, SatisfiesFavardRecurrence.toSequence_apply,
    Polynomial.smul_eq_C_mul] using ha.symm

/-! ## Finite Appell--Jacobi kernel expansion -/

/-- The Bernstein monomial, truncated to the degree triangle of the Appell
kernel. -/
def truncatedJacobiBernstein (m i j : ℕ) : ℝ[X] :=
  if i + j ≤ m then jacobiBernstein i j else 0

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
factors of the Appell kernel. -/
def appellKernelCoefficientMatrix (m : ℕ) (b c d : ℝ)
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
  · rw [truncatedJacobiBernstein, ite_eq_left hij]
  · rw [appellKernelCoefficient, ite_eq_right hij]
    ring

private theorem appellKernelSummand_eq_truncated
    (m i j : ℕ) (b c d r z : ℝ) :
    appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
        (jacobiBernstein i j).eval r =
      appellKernelCoefficient m b c d i j *
        (truncatedJacobiBernstein m i j).eval r *
        (truncatedJacobiBernstein m i j).eval z := by
  by_cases hij : i + j ≤ m
  · rw [truncatedJacobiBernstein, ite_eq_left hij]
    simp only [jacobiBernstein, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    ring
  · rw [appellKernelCoefficient, ite_eq_right hij]
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

/-- Pointwise finite monic-Jacobi expansion of the Appell kernel. -/
theorem eval_appellJacobiKernel_eq_appellKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (r z : ℝ) :
    (appellJacobiKernel m b c d z).eval r =
      ∑ a, ∑ e,
        appellKernelCoefficientMatrix m b c d hc hd a e *
          (shiftedJacobiMonic a (c - 1) (d - 1)).eval r *
          (shiftedJacobiMonic e (c - 1) (d - 1)).eval z := by
  classical
  unfold appellJacobiKernel
  simp_rw [eval_finsetSum, eval_mul, eval_C]
  simp_rw [appellKernelSummand_eq_truncated]
  simp_rw [truncatedJacobiBernstein_eq_sum m _ _ hc hd, eval_finsetSum,
    eval_mul, eval_C]
  simpa only [appellKernelCoefficientMatrix] using
    sum_rank_one (Finset.range (m + 1)) (Finset.range (m + 1))
      (Finset.univ : Finset (Fin (m + 1))) (Finset.univ : Finset (Fin (m + 1)))
      (fun i j => appellKernelCoefficient m b c d i j)
      (fun i j a => jacobiBernsteinCoefficient m i j c d hc hd a)
      (fun i j e => jacobiBernsteinCoefficient m i j c d hc hd e)
      (fun a => (shiftedJacobiMonic a (c - 1) (d - 1)).eval r)
      (fun e => (shiftedJacobiMonic e (c - 1) (d - 1)).eval z)

/-- Polynomial-valued form of the concrete finite kernel expansion. -/
theorem appellJacobiKernel_eq_appellKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m b c d z =
      ∑ a, ∑ e,
        C (appellKernelCoefficientMatrix m b c d hc hd a e *
          (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) *
          shiftedJacobiMonic a (c - 1) (d - 1) := by
  apply Polynomial.funext
  intro r
  rw [eval_appellJacobiKernel_eq_appellKernelCoefficientMatrix m b hc hd]
  simp_rw [eval_finsetSum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem appellKernelCoefficientMatrix_comm (m : ℕ) (b c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (a e : Fin (m + 1)) :
    appellKernelCoefficientMatrix m b c d hc hd a e =
      appellKernelCoefficientMatrix m b c d hc hd e a := by
  unfold appellKernelCoefficientMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem appellJacobiKernel_eq_appellKernelCoefficientMatrix_swapped
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m b c d z =
      ∑ a, ∑ e,
        C (appellKernelCoefficientMatrix m b c d hc hd a e *
          (shiftedJacobiMonic a (c - 1) (d - 1)).eval z) *
          shiftedJacobiMonic e (c - 1) (d - 1) := by
  rw [appellJacobiKernel_eq_appellKernelCoefficientMatrix m b hc hd z,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  rw [appellKernelCoefficientMatrix_comm m b c d hc hd]

private theorem eigenKernelActionLeft_appellKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (r z : ℝ) :
    eigenKernelActionLeft (appellKernelCoefficientMatrix m b c d hc hd)
        (fun a : Fin (m + 1) => shiftedJacobiMonic a (c - 1) (d - 1))
        (jacobiDifferentialOperatorLinearMap c (c + d)) r z =
      (jacobiDifferentialOperator c (c + d)
        (appellJacobiKernel m b c d z)).eval r := by
  rw [appellJacobiKernel_eq_appellKernelCoefficientMatrix m b hc hd z]
  unfold eigenKernelActionLeft
  change _ = ((jacobiDifferentialOperatorLinearMap c (c + d))
    (∑ a, ∑ e,
      C (appellKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic a (c - 1) (d - 1))).eval r
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro e _
  rw [show C (appellKernelCoefficientMatrix m b c d hc hd a e *
      (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic a (c - 1) (d - 1) =
      (appellKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic e (c - 1) (d - 1)).eval z) •
          shiftedJacobiMonic a (c - 1) (d - 1) by
    rw [smul_eq_C_mul]]
  rw [map_smul, eval_smul]
  ring

private theorem eigenKernelActionRight_appellKernelCoefficientMatrix
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (r z : ℝ) :
    eigenKernelActionRight (appellKernelCoefficientMatrix m b c d hc hd)
        (fun a : Fin (m + 1) => shiftedJacobiMonic a (c - 1) (d - 1))
        (jacobiDifferentialOperatorLinearMap c (c + d)) r z =
      (jacobiDifferentialOperator c (c + d)
        (appellJacobiKernel m b c d r)).eval z := by
  rw [appellJacobiKernel_eq_appellKernelCoefficientMatrix_swapped m b hc hd r]
  unfold eigenKernelActionRight
  change _ = ((jacobiDifferentialOperatorLinearMap c (c + d))
    (∑ a, ∑ e,
      C (appellKernelCoefficientMatrix m b c d hc hd a e *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval r) *
        shiftedJacobiMonic e (c - 1) (d - 1))).eval z
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro e _
  rw [show C (appellKernelCoefficientMatrix m b c d hc hd a e *
      (shiftedJacobiMonic a (c - 1) (d - 1)).eval r) *
        shiftedJacobiMonic e (c - 1) (d - 1) =
      (appellKernelCoefficientMatrix m b c d hc hd a e *
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

/-- The coefficient matrix of the Appell kernel is diagonal in the
positive Jacobi parameter range. -/
theorem appellKernelCoefficientMatrix_offDiagonal_eq_zero
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ a e : Fin (m + 1), a ≠ e →
      appellKernelCoefficientMatrix m b c d hc hd a e = 0 := by
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
  have hoperator : ∀ a, operator (basis a) = C (eigen a) * basis a :=
    fun a => jacobiDifferentialOperatorLinearMap_shiftedJacobiMonic c d a
  apply eigenCoefficient_diagonal_of_action_eq heigen hbasis hoperator
  intro r z
  rw [eigenKernelActionLeft_appellKernelCoefficientMatrix m b hc hd,
    eigenKernelActionRight_appellKernelCoefficientMatrix m b hc hd]
  exact eval_jacobiDifferentialOperator_appellJacobiKernel_eq m b hc hd

/-- Diagonal form of the Appell kernel before the boundary coefficients
are identified. -/
theorem appellJacobiKernel_eq_diagonal_monic_sum
    (m : ℕ) (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (z : ℝ) :
    appellJacobiKernel m b c d z =
      ∑ a : Fin (m + 1),
        C (appellKernelCoefficientMatrix m b c d hc hd a a *
          (shiftedJacobiMonic a (c - 1) (d - 1)).eval z) *
          shiftedJacobiMonic a (c - 1) (d - 1) := by
  rw [appellJacobiKernel_eq_appellKernelCoefficientMatrix m b hc hd z]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · intro e _ hea
    rw [appellKernelCoefficientMatrix_offDiagonal_eq_zero m b hc hd a e (Ne.symm hea)]
    simp
  · simp

private theorem normalizedJacobiFunctional_normalized_mul_monic
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j k : ℕ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * shiftedJacobiMonic k (c - 1) (d - 1)) =
      if j = k then
        (shiftedJacobiMonic k (c - 1) (d - 1)).eval 0 *
          normalizedJacobiNorm c d k
      else 0 := by
  rw [← C_eval_zero_mul_normalizedShiftedJacobi (d := d) hc k]
  rw [show normalizedShiftedJacobi j c d *
      (C ((shiftedJacobiMonic k (c - 1) (d - 1)).eval 0) *
        normalizedShiftedJacobi k c d) =
    C ((shiftedJacobiMonic k (c - 1) (d - 1)).eval 0) *
      (normalizedShiftedJacobi j c d * normalizedShiftedJacobi k c d) by ring,
    normalizedJacobiFunctional_C_mul]
  by_cases hjk : j = k
  · subst k
    rw [ite_eq_left rfl]
    simp only [eval_mul, eval_C]
    rw [normalizedShiftedJacobi_eval_zero hc]
    simp only [normalizedJacobiNorm]
    ring
  · rw [ite_eq_right hjk,
      normalizedJacobiFunctional_pairwise_orthogonal hc hd hjk]
    ring

private theorem normalizedJacobiFunctional_diagonal_term
    {m : ℕ} (b : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (j k : Fin (m + 1)) (z : ℝ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d *
          (C (appellKernelCoefficientMatrix m b c d hc hd k k *
              (shiftedJacobiMonic k (c - 1) (d - 1)).eval z) *
            shiftedJacobiMonic k (c - 1) (d - 1))) =
      if j = k then
        appellKernelCoefficientMatrix m b c d hc hd k k *
          (shiftedJacobiMonic k (c - 1) (d - 1)).eval z *
          (shiftedJacobiMonic k (c - 1) (d - 1)).eval 0 *
          normalizedJacobiNorm c d k
      else 0 := by
  rw [show normalizedShiftedJacobi j c d *
      (C (appellKernelCoefficientMatrix m b c d hc hd k k *
          (shiftedJacobiMonic k (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic k (c - 1) (d - 1)) =
    C (appellKernelCoefficientMatrix m b c d hc hd k k *
      (shiftedJacobiMonic k (c - 1) (d - 1)).eval z) *
      (normalizedShiftedJacobi j c d *
        shiftedJacobiMonic k (c - 1) (d - 1)) by ring,
    normalizedJacobiFunctional_C_mul,
    normalizedJacobiFunctional_normalized_mul_monic hc hd]
  by_cases hjk : j = k
  · subst k
    simp
    ring
  · have hval : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    rw [ite_eq_right hjk, ite_eq_right hval]
    ring

/-- The diagonal monic coefficient is determined by the concrete boundary
weight, with all normalization factors retained explicitly. -/
theorem appellKernelCoefficientMatrix_diagonal_weight
    {m : ℕ} (δ : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (a : Fin (m + 1)) :
    appellKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ) c d hc hd a a *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval 0 ^ 2 *
        normalizedJacobiNorm c d a =
      kernelWeight m δ (c + d) a := by
  have hprojection := normalizedJacobiFunctional_appellJacobiKernel_zero
    (m := m) (j := a) (Nat.le_of_lt_succ a.isLt) hc hd δ
  rw [appellJacobiKernel_eq_diagonal_monic_sum m
    ((m : ℝ) + c + d - 1 + δ) hc hd 0, Finset.mul_sum,
    normalizedJacobiFunctional_sum] at hprojection
  simp_rw [normalizedJacobiFunctional_diagonal_term
    ((m : ℝ) + c + d - 1 + δ) hc hd a] at hprojection
  rw [Finset.sum_eq_single a] at hprojection
  · simpa only [ite_eq_left, eval_zero, pow_two, mul_assoc] using hprojection
  · intro k _ hka
    rw [ite_eq_right (Ne.symm hka)]
  · simp

private theorem diagonal_monic_term_eq_normalized
    {m : ℕ} (δ : ℝ) {c d z : ℝ} (hc : 0 < c) (hd : 0 < d)
    (a : Fin (m + 1)) :
    C (appellKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
          c d hc hd a a *
        (shiftedJacobiMonic a (c - 1) (d - 1)).eval z) *
        shiftedJacobiMonic a (c - 1) (d - 1) =
      C (kernelWeight m δ (c + d) a / normalizedJacobiNorm c d a *
        (normalizedShiftedJacobi a c d).eval z) *
        normalizedShiftedJacobi a c d := by
  let p0 := (shiftedJacobiMonic a (c - 1) (d - 1)).eval 0
  let H := normalizedJacobiNorm c d a
  have hH : H ≠ 0 := (normalizedJacobiNorm_pos hc hd a).ne'
  have hp := C_eval_zero_mul_normalizedShiftedJacobi (d := d) hc a
  have hweight := appellKernelCoefficientMatrix_diagonal_weight δ hc hd a
  change appellKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
      c d hc hd a a * p0 ^ 2 * H = kernelWeight m δ (c + d) a at hweight
  rw [← hp]
  simp only [eval_mul, eval_C]
  rw [← mul_assoc, ← C_mul]
  congr 1
  rw [Polynomial.C_inj]
  change appellKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
      c d hc hd a a * (p0 * (normalizedShiftedJacobi a c d).eval z) * p0 =
    kernelWeight m δ (c + d) a / H * (normalizedShiftedJacobi a c d).eval z
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hH).2
  calc
    appellKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
          c d hc hd a a * (p0 * (normalizedShiftedJacobi a c d).eval z) * p0 * H =
        (appellKernelCoefficientMatrix m ((m : ℝ) + c + d - 1 + δ)
          c d hc hd a a * p0 ^ 2 * H) *
            (normalizedShiftedJacobi a c d).eval z := by ring
    _ = kernelWeight m δ (c + d) a *
          (normalizedShiftedJacobi a c d).eval z := by rw [hweight]

/-- The diagonal spectral expansion of the finite Appell
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

/-! ## Raw and value-one Jacobi kernel normalizations

The finite kernel signs use monic shifted-Jacobi polynomials and their raw
spectral norms.  The boundary projection uses the value-one normalization and
the corresponding normalized functional.  We transport individual terms and
finite weighted sums between those two conventions.
-/

/-- The raw squared norm of a monic shifted-Jacobi polynomial is its
value-one squared norm, multiplied by the zeroth moment and the square of the
monic polynomial's value at zero. -/
theorem shiftedJacobiMonicNorm_eq_moment_zero_mul_eval_zero_sq_mul_normalized
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    shiftedJacobiMonicNorm j (c - 1) (d - 1) =
      shiftedJacobiMoment (c - 1) (d - 1) 0 *
        ((shiftedJacobiMonic j (c - 1) (d - 1)).eval 0) ^ 2 *
          normalizedJacobiNorm c d j := by
  let p := shiftedJacobiMonic j (c - 1) (d - 1)
  let φ := normalizedShiftedJacobi j c d
  let p0 := p.eval 0
  let H0 := shiftedJacobiMoment (c - 1) (d - 1) 0
  have hp : C p0 * φ = p := by
    simpa only [p0, φ, p] using
      C_eval_zero_mul_normalizedShiftedJacobi (d := d) hc j
  have hH0 : H0 ≠ 0 := by
    dsimp only [H0]
    exact (shiftedJacobiMoment_zero_pos (by linarith) (by linarith)).ne'
  change shiftedJacobiInner (c - 1) (d - 1) p p =
    H0 * p0 ^ 2 * normalizedJacobiNorm c d j
  calc
    shiftedJacobiInner (c - 1) (d - 1) p p =
        shiftedJacobiInner (c - 1) (d - 1) (C p0 * φ) (C p0 * φ) := by
      rw [hp]
    _ = p0 * p0 * shiftedJacobiInner (c - 1) (d - 1) φ φ := by
      rw [shiftedJacobiInner_C_mul_left, shiftedJacobiInner_C_mul_right]
      ring
    _ = H0 * p0 ^ 2 * normalizedJacobiNorm c d j := by
      change p0 * p0 * shiftedJacobiFunctional (c - 1) (d - 1) (φ * φ) =
        H0 * p0 ^ 2 *
          (shiftedJacobiFunctional (c - 1) (d - 1) (φ * φ) / H0)
      field_simp [hH0]

/-- One value-one normalized Jacobi kernel term is the corresponding raw
monic kernel term, multiplied by the zeroth raw moment. -/
theorem normalizedJacobi_kernel_term_eq_moment_zero_mul_raw
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) (r z : ℝ) :
    (normalizedShiftedJacobi j c d).eval r *
        (normalizedShiftedJacobi j c d).eval z /
      normalizedJacobiNorm c d j =
        shiftedJacobiMoment (c - 1) (d - 1) 0 *
          (shiftedJacobiMonic j (c - 1) (d - 1)).eval r *
            (shiftedJacobiMonic j (c - 1) (d - 1)).eval z /
          shiftedJacobiMonicNorm j (c - 1) (d - 1) := by
  let p := shiftedJacobiMonic j (c - 1) (d - 1)
  let φ := normalizedShiftedJacobi j c d
  let p0 := p.eval 0
  let H0 := shiftedJacobiMoment (c - 1) (d - 1) 0
  have hp : C p0 * φ = p := by
    simpa only [p0, φ, p] using
      C_eval_zero_mul_normalizedShiftedJacobi (d := d) hc j
  have hp0 : p0 ≠ 0 := by
    dsimp only [p0, p]
    exact shiftedJacobiMonic_eval_zero_ne_zero hc hd j
  have hH0 : H0 ≠ 0 := by
    dsimp only [H0]
    exact (shiftedJacobiMoment_zero_pos (by linarith) (by linarith)).ne'
  have hnorm : normalizedJacobiNorm c d j ≠ 0 :=
    (normalizedJacobiNorm_pos hc hd j).ne'
  have hraw :=
    shiftedJacobiMonicNorm_eq_moment_zero_mul_eval_zero_sq_mul_normalized
      hc hd j
  change shiftedJacobiMonicNorm j (c - 1) (d - 1) =
    H0 * p0 ^ 2 * normalizedJacobiNorm c d j at hraw
  have heval (x : ℝ) : p.eval x = p0 * φ.eval x := by
    rw [← hp]
    simp
  change φ.eval r * φ.eval z / normalizedJacobiNorm c d j =
    H0 * p.eval r * p.eval z /
      shiftedJacobiMonicNorm j (c - 1) (d - 1)
  rw [heval r, heval z, hraw]
  field_simp [hp0, hH0, hnorm]

/-- The literal value-one finite Jacobi kernel sum equals the raw monic
finite kernel sum times the zeroth raw moment.  No sign condition on `δ` is
needed, so this also applies when `δ = 0`. -/
theorem kernelWeight_normalizedJacobi_sum_eq_moment_zero_mul_raw
    {m : ℕ} (δ : ℝ) {c d r z : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (∑ j : Fin (m + 1),
        kernelWeight m δ (c + d) j *
            (normalizedShiftedJacobi j c d).eval r *
              (normalizedShiftedJacobi j c d).eval z /
          normalizedJacobiNorm c d j) =
      shiftedJacobiMoment (c - 1) (d - 1) 0 *
        ∑ j : Fin (m + 1),
          kernelWeight m δ (c + d) j *
              (shiftedJacobiMonic j (c - 1) (d - 1)).eval r *
                (shiftedJacobiMonic j (c - 1) (d - 1)).eval z /
            shiftedJacobiMonicNorm j (c - 1) (d - 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show
      kernelWeight m δ (c + d) j *
          (normalizedShiftedJacobi j c d).eval r *
            (normalizedShiftedJacobi j c d).eval z /
          normalizedJacobiNorm c d j =
        kernelWeight m δ (c + d) j *
          ((normalizedShiftedJacobi j c d).eval r *
            (normalizedShiftedJacobi j c d).eval z /
              normalizedJacobiNorm c d j) by ring,
    normalizedJacobi_kernel_term_eq_moment_zero_mul_raw hc hd j r z]
  ring

/-! ## The deformation and the raw Jacobi kernel

This combines the Appell coordinate substitution, the spectral expansion, and
the normalization bridge.
-/

/-- The raw monic finite Jacobi kernel occurring in the scalar sign lemmas. -/
def rawJacobiKernel (m : ℕ) (δ α β r z : ℝ) : ℝ :=
  ∑ l : Fin (m + 1),
    kernelWeight m δ (α + β + 2) l *
        (shiftedJacobiMonic l α β).eval r *
          (shiftedJacobiMonic l α β).eval z /
      shiftedJacobiMonicNorm l α β

/-- At an image-coordinate pair, the deformation is a strictly
positive moment-and-power factor times the raw finite Jacobi kernel. -/
theorem polynomial_eval_eq_coordinateFactor_mul_rawJacobiKernel
    (m : ℕ) {δ c d U V xi r z : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    (polynomial m δ c d U V).eval xi =
      ((-1 : ℝ) ^ m * xi ^ m * shiftedJacobiMoment (c - 1) (d - 1) 0) *
        rawJacobiKernel m δ (c - 1) (d - 1) r z := by
  rw [polynomial_eval_eq_appellJacobiKernel_coordinates m δ c d U V xi r z
      hprod hcomp,
    appellJacobiKernel_eq_normalizedShiftedJacobi_sum m δ hc hd z,
    eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hsum :
      (∑ l : Fin (m + 1),
          kernelWeight m δ (c + d) l / normalizedJacobiNorm c d l *
            (normalizedShiftedJacobi l c d).eval z *
              (normalizedShiftedJacobi l c d).eval r) =
        shiftedJacobiMoment (c - 1) (d - 1) 0 *
          rawJacobiKernel m δ (c - 1) (d - 1) r z := by
    calc
      _ = ∑ l : Fin (m + 1),
          kernelWeight m δ (c + d) l *
              (normalizedShiftedJacobi l c d).eval z *
                (normalizedShiftedJacobi l c d).eval r /
            normalizedJacobiNorm c d l := by
              apply Finset.sum_congr rfl
              intro l _
              ring
      _ = shiftedJacobiMoment (c - 1) (d - 1) 0 *
          ∑ l : Fin (m + 1),
            kernelWeight m δ (c + d) l *
                (shiftedJacobiMonic l (c - 1) (d - 1)).eval z *
                  (shiftedJacobiMonic l (c - 1) (d - 1)).eval r /
              shiftedJacobiMonicNorm l (c - 1) (d - 1) :=
        kernelWeight_normalizedJacobi_sum_eq_moment_zero_mul_raw
          (m := m) δ hc hd
      _ = _ := by
        unfold rawJacobiKernel
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        ring_nf
  rw [hsum]
  ring

/-- The coordinate factor in the raw-kernel identity is positive at every
negative image coordinate. -/
theorem coordinateFactor_pos (m : ℕ) {c d xi : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hxi : xi < 0) :
    0 < (-1 : ℝ) ^ m * xi ^ m * shiftedJacobiMoment (c - 1) (d - 1) 0 := by
  have hpower : 0 < (-1 : ℝ) ^ m * xi ^ m := by
    rw [← mul_pow]
    exact pow_pos (by linarith) m
  exact mul_pos hpower (shiftedJacobiMoment_zero_pos (by linarith) (by linarith))

end RealRooted.JacobiDeformation
