import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance

/-!
# Perron-Frobenius for general nonnegative matrices

The ported Perron-Frobenius development proves that the Perron root of an
*irreducible* nonnegative matrix is an eigenvalue.  This file removes the
irreducibility hypothesis, which is what the Gantmacher-Krein route needs:
compound matrices of totally nonnegative matrices are entrywise nonnegative
but need not be irreducible.

* `Matrix.isIrreducible_of_pos`: an entrywise positive matrix is irreducible.
* `Matrix.perronRoot_le_perronRoot_of_le`: the Perron root is monotone in the
  matrix, entrywise, over nonnegative vectors' Collatz-Wielandt values.
* `Matrix.norm_le_perronRoot_of_eigenvalue`: every complex eigenvalue of a
  nonnegative real matrix has modulus at most the Perron root - no
  irreducibility needed, straight from the subinvariance inequalities.
* `Matrix.exists_nonneg_mulVec_eq_perronRoot_smul`: **the general
  Perron-Frobenius theorem**: a nonnegative matrix attains its Perron root as
  an eigenvalue with a nonnegative eigenvector.  Proof: perturb to the
  positive matrix `A + ((k : ℝ) + 1)⁻¹ • J`, apply the irreducible theorem,
  normalize the eigenvectors to the standard simplex, and pass to a convergent
  subsequence by compactness.
-/

open Filter Topology Finset

namespace Matrix

open CollatzWielandt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An entrywise positive matrix is irreducible. -/
lemma isIrreducible_of_pos {A : Matrix n n ℝ} (hA : ∀ i j, 0 < A i j) :
    A.IsIrreducible := by
  refine ⟨fun i j => (hA i j).le, fun i j => ?_⟩
  letI : Quiver n := toQuiver A
  exact ⟨(show i ⟶ j from ⟨hA i j⟩).toPath, by simp [Quiver.Hom.toPath]⟩

/-- `mulVec` is monotone in the matrix on nonnegative vectors. -/
private lemma mulVec_le_mulVec_of_le {A B : Matrix n n ℝ} (hAB : ∀ i j, A i j ≤ B i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : A *ᵥ x ≤ B *ᵥ x := by
  intro i
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hx j)

/-- The Perron root is monotone in the matrix over nonnegative matrices. -/
lemma perronRoot_le_perronRoot_of_le [Nonempty n] {A B : Matrix n n ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hAB : ∀ i j, A i j ≤ B i j) :
    perronRoot A ≤ perronRoot B := by
  apply csSup_le (Set.Nonempty.image _ ⟨_, nonnegNeZero_mem_const_one⟩)
  rintro y ⟨x, ⟨hx_nonneg, hx_ne⟩, rfl⟩
  have h_sub : collatzWielandtFn A x • x ≤ B *ᵥ x :=
    (le_mulVec hA_nonneg hx_nonneg hx_ne).trans (mulVec_le_mulVec_of_le hAB hx_nonneg)
  exact (le_of_subinvariant hB_nonneg hx_nonneg hx_ne h_sub).trans
    (collatzWielandtFn_le_perronRoot hB_nonneg hx_nonneg hx_ne)

/-- Every complex eigenvalue of a nonnegative real matrix has modulus at most the
Perron root.  No irreducibility is needed. -/
theorem norm_le_perronRoot_of_eigenvalue [Nonempty n] {A : Matrix n n ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {μ : ℂ} {x : n → ℂ} (hx : x ≠ 0)
    (h_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) :
    ‖μ‖ ≤ perronRoot A := by
  have h_sub := eigenvalue_abs_subinvariant hA_nonneg h_eig
  have h_nn : ∀ i, 0 ≤ ‖x i‖ := fun i => norm_nonneg _
  have h_ne : (fun i => ‖x i‖) ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx
  exact (le_of_subinvariant hA_nonneg h_nn h_ne h_sub).trans
    (collatzWielandtFn_le_perronRoot hA_nonneg h_nn h_ne)

omit [DecidableEq n] in
/-- **Perron-Frobenius for general nonnegative matrices.**  A nonnegative real
matrix attains its Perron root as an eigenvalue with a nonnegative eigenvector. -/
theorem exists_nonneg_mulVec_eq_perronRoot_smul [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ v : n → ℝ, (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ A *ᵥ v = perronRoot A • v := by
  classical
  set J : Matrix n n ℝ := of fun _ _ => (1 : ℝ) with hJ
  have hAk_pos : ∀ k : ℕ, ∀ i j, 0 < (A + ((k : ℝ) + 1)⁻¹ • J) i j := by
    intro k i j
    have h1 : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    simpa [hJ] using add_pos_of_nonneg_of_pos (hA_nonneg i j) h1
  set M : ℝ := ∑ i : n, ∑ j : n, (A i j + 1) with hM
  -- eigen-data for each perturbation, normalized to the standard simplex
  have key : ∀ k : ℕ, ∃ (r : ℝ) (v : n → ℝ), v ∈ stdSimplex ℝ n ∧
      perronRoot A ≤ r ∧ r ≤ M ∧
      ∀ i, (A *ᵥ v) i + ((k : ℝ) + 1)⁻¹ = r * v i := by
    intro k
    set Ak : Matrix n n ℝ := A + ((k : ℝ) + 1)⁻¹ • J with hAk
    have hAk_nonneg : ∀ i j, 0 ≤ Ak i j := fun i j => (hAk_pos k i j).le
    obtain ⟨r, w, hr_pos, hw_pos, h_eig, h_perron⟩ :=
      perron_root_eq_positive_eigenvalue (isIrreducible_of_pos (hAk_pos k)) hAk_nonneg
    set s : ℝ := ∑ i, w i with hs
    have hs_pos : 0 < s := Finset.sum_pos (fun i _ => hw_pos i) Finset.univ_nonempty
    set v : n → ℝ := s⁻¹ • w with hv
    have hv_sum : ∑ i, v i = 1 := by
      simp only [hv, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hs]
      exact inv_mul_cancel₀ hs_pos.ne'
    have hv_mem : v ∈ stdSimplex ℝ n := by
      refine ⟨fun i => ?_, hv_sum⟩
      have := (hw_pos i).le
      simp only [hv, Pi.smul_apply, smul_eq_mul]
      positivity
    have h_eig_v : Ak *ᵥ v = r • v := by
      rw [hv, mulVec_smul, h_eig, smul_comm]
    have h_ge : perronRoot A ≤ r := by
      rw [← h_perron]
      exact perronRoot_le_perronRoot_of_le hA_nonneg hAk_nonneg
        (fun i j => by
          have h1 : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹ := by positivity
          simp [hJ]
          linarith)
    have hv_le_one : ∀ j, v j ≤ 1 := by
      intro j
      calc v j ≤ ∑ i, v i := Finset.single_le_sum (fun i _ => hv_mem.1 i) (Finset.mem_univ j)
        _ = 1 := hv_sum
    have h_le_M : r ≤ M := by
      have h_sum : r = ∑ i, (Ak *ᵥ v) i := by
        rw [h_eig_v]
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv_sum, mul_one]
      rw [h_sum, hM]
      apply Finset.sum_le_sum
      intro i _
      simp only [mulVec, dotProduct]
      apply Finset.sum_le_sum
      intro j _
      have h1 : Ak i j ≤ A i j + 1 := by
        have h2 : ((k : ℝ) + 1)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          linarith [Nat.cast_nonneg (α := ℝ) k]
        simp [hAk, hJ]
        linarith
      calc Ak i j * v j ≤ (A i j + 1) * v j :=
            mul_le_mul_of_nonneg_right h1 (hv_mem.1 j)
        _ ≤ (A i j + 1) * 1 := by
            have := hA_nonneg i j
            exact mul_le_mul_of_nonneg_left (hv_le_one j) (by linarith)
        _ = A i j + 1 := mul_one _
    refine ⟨r, v, hv_mem, h_ge, h_le_M, fun i => ?_⟩
    have h1 : (Ak *ᵥ v) i = (A *ᵥ v) i + ((k : ℝ) + 1)⁻¹ := by
      rw [hAk, add_mulVec, smul_mulVec]
      have hJv : (J *ᵥ v) i = 1 := by
        simp only [hJ, mulVec, dotProduct, of_apply, one_mul]
        exact hv_sum
      simp [hJv]
    have h2 := congrFun h_eig_v i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [← h1, h2]
  choose r v hmem hge hle heq using key
  -- pass to a convergent subsequence by compactness
  have hcompact : IsCompact (Set.Icc (perronRoot A) M ×ˢ stdSimplex ℝ n) :=
    isCompact_Icc.prod (_root_.isCompact_stdSimplex ℝ n)
  have hmemK : ∀ k, (r k, v k) ∈ Set.Icc (perronRoot A) M ×ˢ stdSimplex ℝ n :=
    fun k => ⟨⟨hge k, hle k⟩, hmem k⟩
  obtain ⟨⟨r₀, v₀⟩, hK, φ, hφ, hconv⟩ := hcompact.tendsto_subseq hmemK
  have hr_lim : Tendsto (fun m => r (φ m)) atTop (𝓝 r₀) :=
    (continuous_fst.tendsto _).comp hconv
  have hv_lim : Tendsto (fun m => v (φ m)) atTop (𝓝 v₀) :=
    (continuous_snd.tendsto _).comp hconv
  have hv_lim_i : ∀ i, Tendsto (fun m => v (φ m) i) atTop (𝓝 (v₀ i)) :=
    fun i => (tendsto_pi_nhds.1 hv_lim) i
  have heps : Tendsto (fun m : ℕ => ((φ m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h_upper : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
      (fun m => by positivity) (fun m => ?_)
    apply inv_anti₀ (by positivity)
    have h : m ≤ φ m := hφ.le_apply
    have h2 : (m : ℝ) ≤ (φ m : ℝ) := Nat.cast_le.2 h
    linarith
  -- the limit eigen-equation
  have h_eig₀ : A *ᵥ v₀ = r₀ • v₀ := by
    funext i
    have hAv : Tendsto (fun m => (A *ᵥ v (φ m)) i) atTop (𝓝 ((A *ᵥ v₀) i)) := by
      simp only [mulVec, dotProduct]
      exact tendsto_finsetSum _ fun j _ => (hv_lim_i j).const_mul (A i j)
    have hLHS : Tendsto (fun m => (A *ᵥ v (φ m)) i + ((φ m : ℝ) + 1)⁻¹) atTop
        (𝓝 ((A *ᵥ v₀) i)) := by
      simpa using hAv.add heps
    have hRHS : Tendsto (fun m => r (φ m) * v (φ m) i) atTop (𝓝 (r₀ * v₀ i)) :=
      hr_lim.mul (hv_lim_i i)
    have hfun : (fun m => (A *ᵥ v (φ m)) i + ((φ m : ℝ) + 1)⁻¹)
        = fun m => r (φ m) * v (φ m) i :=
      funext fun m => heq (φ m) i
    have := tendsto_nhds_unique (hfun ▸ hLHS) hRHS
    simpa using this
  -- identify the limit eigenvalue with the Perron root
  have hv₀_mem : v₀ ∈ stdSimplex ℝ n := hK.2
  have hv₀_ne : v₀ ≠ 0 := ne_zero_of_mem_stdSimplex hv₀_mem
  have h_le : r₀ ≤ perronRoot A :=
    (le_of_subinvariant hA_nonneg hv₀_mem.1 hv₀_ne (le_of_eq h_eig₀.symm)).trans
      (collatzWielandtFn_le_perronRoot hA_nonneg hv₀_mem.1 hv₀_ne)
  have h_eq : r₀ = perronRoot A := le_antisymm h_le hK.1.1
  exact ⟨v₀, hv₀_mem.1, hv₀_ne, h_eq ▸ h_eig₀⟩

end Matrix
