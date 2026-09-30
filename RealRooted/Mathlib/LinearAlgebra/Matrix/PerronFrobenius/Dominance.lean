/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.  Original path: MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/Dominance.lean
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CStarClasses

-- Ported third-party code; keep original line layout.
set_option linter.style.longLine false

open Quiver.Path
namespace Matrix
open CollatzWielandt

open Quiver
open Matrix Complex
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [Fintype n] [DecidableEq n] in
/-- A complex number with norm `1` is nonzero. -/
lemma _root_.Complex.ne_zero_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : c ≠ 0 := by
  rintro rfl
  norm_num at hc

omit [Fintype n] [DecidableEq n] in
/-- Cancel a nonzero scalar multiplying two dependent functions over a division ring. -/
lemma _root_.Pi.smul_left_cancel₀ {ι 𝕜 : Type*} [DivisionRing 𝕜] {c : 𝕜}
    (hc : c ≠ 0) {v w : ι → 𝕜} (h : c • v = c • w) :
    v = w := by
  ext i
  exact mul_left_cancel₀ hc <| by
    simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h i

omit [Fintype n] [DecidableEq n] in
/-- If `x : n → ℂ` is nonzero, then `fun i ↦ ‖x i‖` is nonzero as a dependent function. -/
lemma normFun_complex_ne_zero_of_ne_zero {x : n → ℂ} (hx : x ≠ 0) : (fun i ↦ ‖x i‖) ≠ 0 := by
  contrapose! hx
  ext i
  exact norm_eq_zero.mp (congr_fun hx i)

/-- Reconstruct `z : ℂ` from its phase `z / ‖z‖` and its modulus `‖z‖` (as a real coercion). -/
lemma eq_mul_div_ofReal_norm_complex (z : ℂ) (hz : ‖z‖ ≠ 0) :
    z = (z / (↑‖z‖ : ℂ)) * (↑‖z‖ : ℂ) := by
  have hn : (↑‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz
  exact (div_mul_cancel₀ z hn).symm

/-! ### Norm sums

`Finset`/`Fintype` vanishing for sums of complex norms, and a consequence of global
triangle equality. -/

lemma norm_eq_zero_of_finset_sum_norm_eq_zero {ι : Type*} {s : Finset ι} (v : ι → ℂ)
    (h : ∑ i ∈ s, ‖v i‖ = 0) (i : ι) (hi : i ∈ s) : ‖v i‖ = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg (v j))).1 h i hi

omit [DecidableEq n] in
/-- If the dot product of a non-negative vector `v` and a strictly positive vector `w` is zero,
    then `v` must be the zero vector. -/
lemma eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos
    {v w : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hw_pos : ∀ i, 0 < w i)
    (h_dot : v ⬝ᵥ w = 0) :
    v = 0 := by
  rw [dotProduct] at h_dot
  funext i
  have hi := forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
    (fun j => mul_nonneg (hv_nonneg j) (hw_pos j).le) h_dot i
  rw [mul_eq_zero] at hi
  exact hi.resolve_right (hw_pos i).ne'

/--
If a scalar `μ` is in the spectrum of a complex matrix `A`, then there exists a non-zero
eigenvector `x` for that eigenvalue.
-/
theorem exists_eigenvector_of_mem_spectrum
    {A' : Matrix n n ℝ} {μ : ℂ} (h : μ ∈ spectrum ℂ (A'.map (algebraMap ℝ ℂ))) :
    ∃ x, x ≠ 0 ∧ (A'.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x := by
  let B := A'.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by
    rwa [spectrum.Matrix_toLin'_eq_spectrum]
  rcases Module.End.exists_eigenvector_of_mem_spectrum h_spec with ⟨x, hx_ne_zero, hx_eig⟩
  refine ⟨x, hx_ne_zero, ?_⟩
  have h_mul_eq := hx_eig
  rw [toLin'_apply] at h_mul_eq
  exact h_mul_eq

variable [Nonempty n]

omit [Nonempty n] in
lemma sum_component_norms_eq_perron_power_norm
    {A : Matrix n n ℝ} {x : n → ℂ}
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) • (fun i ↦ ‖x i‖))
    (k : ℕ) (m : n) (hAk_pos : ∀ i j, 0 < (A ^ k) i j) :
    ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = (perronRoot A) ^ k * ‖x m‖ := by
  have h_pow_eig : (A ^ k) *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) ^ k • (fun i ↦ ‖x i‖) :=
    mulVec_pow_eq_smul_pow_of_mulVec_smul h_x_abs_eig k
  calc ∑ l, ‖((A ^ k) m l : ℂ) * x l‖
    = ∑ l, |(A ^ k) m l| * ‖x l‖ := by
        simp_rw [norm_mul, Complex.norm_ofReal]
    _ = ∑ l, (A ^ k) m l * ‖x l‖ := by
      simp_rw [abs_of_pos (hAk_pos m _)]
    _ = ((A ^ k) *ᵥ (fun i ↦ ‖x i‖)) m := by
      rfl
    _ = ((perronRoot A) ^ k • (fun i ↦ ‖x i‖)) m := by rw [h_pow_eig]
    _ = (perronRoot A) ^ k * ‖x m‖ := by simp [Pi.smul_apply, smul_eq_mul]

omit [DecidableEq n] [Nonempty n] in
/--
For an eigenvalue μ of a nonnegative matrix A with eigenvector x,
the absolute value |μ| satisfies the sub-invariant relation: |μ|⋅|x| ≤ A⋅|x|.
This is the fundamental inequality in spectral analysis of nonnegative matrices.
-/
theorem eigenvalue_abs_subinvariant
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) :
    (‖μ‖ : ℝ) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
  intro i
  calc
    (‖μ‖ : ℝ) * ‖x i‖ = ‖μ * x i‖ := by rw [← norm_mul]
    _ = ‖(μ • x) i‖ := by simp [Pi.smul_apply]
    _ = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by rw [← hx_eig]
    _ = ‖∑ j, (A i j : ℂ) * x j‖ := by simp; rfl
    _ ≤ ∑ j, ‖(A i j : ℂ) * x j‖ := by apply norm_sum_le
    _ = ∑ j, A i j * ‖x j‖ := by
      simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hA_nonneg _ _)]
    _ = (A *ᵥ fun i => ‖x i‖) i := by
      rfl

omit [DecidableEq n] in
open scoped Classical in
theorem eigenvalue_is_perron_root_of_positive_eigenvector
    {r : ℝ} {v : n → ℝ}
    (_ : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hr_pos : 0 < r)
    (hv_pos : ∀ i, 0 < v i)
    (h_eig : A *ᵥ v = r • v) :
    r = perronRoot A := by
  have h_ge : perronRoot A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector
      (A := A) hA_nonneg hr_pos hv_pos h_eig
  have h_le : r ≤ perronRoot A := by
    rw [← eq_eigenvalue_of_positive_eigenvector hv_pos h_eig]
    have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
    have hv_ne_zero : v ≠ 0 := Pi.ne_zero_of_pos hv_pos
    apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
    rw [@Set.mem_image]
    exact ⟨v, ⟨hv_nonneg, hv_ne_zero⟩, rfl⟩
  exact le_antisymm h_le h_ge

omit [DecidableEq n] in
open scoped Classical in
/-- Positive right and left eigenvectors for a matrix have the same eigenvalue. -/
lemma eigenvalue_eq_of_positive_right_left_eigenvectors
    {A : Matrix n n ℝ} {r s : ℝ} {v u : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (hu_pos : ∀ i, 0 < u i)
    (hv_eig : A *ᵥ v = r • v) (hu_left_eig : u ᵥ* A = s • u) :
    r = s := by
  have h_dot_pos : 0 < u ⬝ᵥ v :=
    dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos (fun i => (hv_pos i).le)
      (Pi.ne_zero_of_pos hv_pos)
  apply (mul_left_inj' h_dot_pos.ne').mp
  calc
    r * (u ⬝ᵥ v) = u ⬝ᵥ (A *ᵥ v) := by simp [hv_eig, dotProduct_smul, smul_eq_mul]
    _ = (u ᵥ* A) ⬝ᵥ v := by simpa using dotProduct_mulVec u A v
    _ = s * (u ⬝ᵥ v) := by simp [hu_left_eig, smul_dotProduct, smul_eq_mul]

omit [DecidableEq n] in
open scoped Classical in
theorem perronRoot_transpose_eq
    (A : Matrix n n ℝ) (hA_irred : A.IsIrreducible) :
    perronRoot A = perronRoot Aᵀ := by
  obtain ⟨r, v, hr_pos, hv_pos, hv_eig⟩ :=
    exists_positive_eigenvector_of_irreducible hA_irred
  have hr_eq_perron : r = perronRoot A :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hA_irred hA_irred.nonneg hr_pos hv_pos hv_eig
  have hAT_irred : Aᵀ.IsIrreducible :=
    Matrix.IsIrreducible.transpose hA_irred
  obtain ⟨r', u, hr'_pos, hu_pos, hu_eig_T⟩ :=
    exists_positive_eigenvector_of_irreducible hAT_irred
  have hr'_eq_perron : r' = perronRoot Aᵀ :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hAT_irred (fun i j ↦ hA_irred.nonneg j i) hr'_pos hu_pos hu_eig_T
  have hu_eig_left : u ᵥ* A = r' • u := by
    have : Aᵀ *ᵥ u = r' • u := hu_eig_T
    simpa [vecMul_eq_mulVec_transpose] using this
  have hr_eq_r' : r = r' :=
    eigenvalue_eq_of_positive_right_left_eigenvectors hv_pos hu_pos hv_eig hu_eig_left
  calc
    perronRoot A   = r   := by symm; simpa using hr_eq_perron
    _                  = r'  := hr_eq_r'
    _                  = perronRoot Aᵀ := hr'_eq_perron

omit [DecidableEq n] in
open scoped Classical in
/-- An irreducible nonnegative matrix has a positive left Perron eigenvector. -/
lemma exists_positive_left_perron_eigenvector
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ u : n → ℝ, (∀ i, 0 < u i) ∧ u ᵥ* A = perronRoot A • u := by
  have hAT_irred : Aᵀ.IsIrreducible := Matrix.IsIrreducible.transpose hA_irred
  obtain ⟨r, u, hr_pos, hu_pos, hu_eig⟩ := exists_positive_eigenvector_of_irreducible hAT_irred
  have hr_eq : r = perronRoot A := by
    calc
      r = perronRoot Aᵀ :=
        eigenvalue_is_perron_root_of_positive_eigenvector
          hAT_irred (fun i j => hA_nonneg j i) hr_pos hu_pos hu_eig
      _ = perronRoot A := (perronRoot_transpose_eq A hA_irred).symm
  exact ⟨u, hu_pos, by simpa [hr_eq, vecMul_eq_mulVec_transpose] using hu_eig⟩

omit [Nonempty n] [DecidableEq n] in
/-- A positive left Perron eigenvector annihilates `A *ᵥ y - r • y` in the dot product. -/
lemma dotProduct_left_perron_sub_eq_zero
    {A : Matrix n n ℝ} {u y : n → ℝ}
    (hu_left_eig : u ᵥ* A = perronRoot A • u) :
    u ⬝ᵥ (A *ᵥ y - perronRoot A • y) = 0 := by
  rw [dotProduct_sub, dotProduct_mulVec, hu_left_eig, dotProduct_smul_left,
    dotProduct_smul, smul_eq_mul, sub_self]

omit [DecidableEq n] in
open scoped Classical in
/-- If equality holds in the subinvariance inequality `r • v ≤ A *ᵥ v` for the Perron root `r`,
    then `v` must be an eigenvector. -/
lemma subinvariant_equality_implies_eigenvector
    (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (_ : ∀ i, 0 ≤ v i) (_ : v ≠ 0)
    (h_subinv : perronRoot A • v ≤ A *ᵥ v) :
    A *ᵥ v = perronRoot A • v := by
  let r := perronRoot A
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg, z]
    exact h_subinv i
  by_cases hz_zero : z = 0
  · simp only [sub_eq_zero, z] at hz_zero
    exact hz_zero
  · obtain ⟨u, hu_pos, hu_left_eig⟩ :=
      exists_positive_left_perron_eigenvector hA_irred hA_nonneg
    have h_dot_z : u ⬝ᵥ z = 0 := by
      simpa [z, r] using dotProduct_left_perron_sub_eq_zero (u := u) (y := v) hu_left_eig
    have h_z_eq_zero : z = 0 :=
      eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos hz_nonneg hu_pos (by rwa [dotProduct_comm])
    exact (hz_zero h_z_eq_zero).elim

omit [DecidableEq n] in
open scoped Classical in
/--
The value of the Collatz-Wielandt function for any non-negative, non-zero vector
is less than or equal to the Perron root.
-/
lemma collatzWielandtFn_le_perronRoot
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    collatzWielandtFn A x ≤ perronRoot A := by
  apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
  rw [Set.mem_image]
  exact ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩

/--
Any eigenvalue μ of a nonnegative irreducible matrix A has absolute value
at most equal to the Perron root.
-/
theorem eigenvalue_abs_le_perron_root
    {A : Matrix n n ℝ} (_ : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    ‖μ‖ ≤ perronRoot A := by
  let B := A.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by rwa [spectrum.Matrix_toLin'_eq_spectrum]
  rcases Module.End.exists_eigenvector_of_mem_spectrum h_spec with ⟨x, hx_ne_zero, hx_eig_lin⟩
  have hx_eig : B *ᵥ x = μ • x := by rwa [toLin'_apply] at hx_eig_lin
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_subinv : (‖μ‖ : ℝ) • x_abs ≤ A *ᵥ x_abs :=
    eigenvalue_abs_subinvariant hA_nonneg hx_eig
  have h_le_collatz : (‖μ‖ : ℝ) ≤ collatzWielandtFn A x_abs :=
    le_of_subinvariant hA_nonneg hx_abs_nonneg hx_abs_ne_zero h_subinv
  have h_le_perron : collatzWielandtFn A x_abs ≤ perronRoot A :=
    collatzWielandtFn_le_perronRoot hA_nonneg hx_abs_nonneg hx_abs_ne_zero
  exact le_trans h_le_collatz h_le_perron

omit [DecidableEq n] in
open scoped Classical in
/-- For an irreducible, non-negative matrix, the Perron root (defined as the Collatz-Wielandt
supremum) is equal to the unique positive eigenvalue `r` from the existence theorem. -/
lemma perron_root_eq_positive_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ r v, 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v ∧ perronRoot A = r := by
  obtain ⟨r, v, hr_pos, hv_pos, h_eig⟩ := exists_positive_eigenvector_of_irreducible hA_irred
  have h_le : perronRoot A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_ge : r ≤ perronRoot A :=
    eigenvalue_le_perron_root_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_eq : perronRoot A = r := le_antisymm h_le h_ge
  exact ⟨r, v, hr_pos, hv_pos, h_eig, h_eq⟩

/--
If a matrix `A` has an eigenvector `v` for an eigenvalue `μ`, then `μ` is in the spectrum of `A`.
This is a direct consequence of the definition of an eigenvalue and the spectrum.
-/
lemma mem_spectrum_of_hasEigenvector {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : V →ₗ[K] V} {μ : K} {v : V} (h : Module.End.HasEigenvector f μ v) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector h

lemma mem_spectrum_of_eigenvalue
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} {μ : K} {v : n → K}
    (hv_ne_zero : v ≠ 0) (h_eig : A *ᵥ v = μ • v) :
    μ ∈ spectrum K A := by
  let f := toLin' A
  have h_eig_f : f v = μ • v := by
    simpa [toLin'_apply, f] using h_eig
  have h_has_eigvec : Module.End.HasEigenvector f μ v :=
    ⟨by
      rwa [← Module.End.mem_eigenspace_iff] at h_eig_f,
      hv_ne_zero⟩
  have h_mem_f : μ ∈ spectrum K f :=
    mem_spectrum_of_hasEigenvector h_has_eigvec
  simpa [f, spectrum.Matrix_toLin'_eq_spectrum] using h_mem_f

/-- The Perron root of an irreducible, non-negative matrix is an eigenvalue. -/
theorem perron_root_is_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    perronRoot A ∈ spectrum ℝ A := by
  obtain ⟨r', v, _, hv_pos, h_eig, h_eq⟩ := perron_root_eq_positive_eigenvalue hA_irred hA_nonneg
  have hv_ne_0 : v ≠ 0 := Pi.ne_zero_of_pos hv_pos
  rw [h_eq]
  exact mem_spectrum_of_eigenvalue hv_ne_0 h_eig

/-- **Perron-Frobenius Theorem (Dominance)**: The Perron root of an irreducible, non-negative
matrix is an eigenvalue and its modulus is greater than or equal to the modulus of any other
eigenvalue. It is the spectral radius. -/
theorem perron_root_is_spectral_radius (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    let r := perronRoot A
    r ∈ spectrum ℝ A ∧ ∀ μ ∈ spectrum ℝ A, |μ| ≤ r := by
  constructor
  · exact perron_root_is_eigenvalue hA_irred hA_nonneg
  · intro μ hμ
    have hμ_complex : (μ : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
      have hμ_lin : μ ∈ spectrum ℝ (toLin' A) := by
        simpa [spectrum.Matrix_toLin'_eq_spectrum] using hμ
      obtain ⟨v, hv_ne_zero, hv_eig⟩ :=
        Module.End.exists_eigenvector_of_mem_spectrum hμ_lin
      let v_complex : n → ℂ := fun i => (v i : ℂ)
      have hvc_ne_zero : v_complex ≠ 0 := by
        intro h
        have : v = 0 := by
          ext i
          have : (v i : ℂ) = 0 := congr_fun h i
          exact_mod_cast this
        exact hv_ne_zero this
      have hv_eig_vec : A *ᵥ v = μ • v := by
        simpa [toLin'_apply] using hv_eig
      have hvc_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ v_complex = (μ : ℂ) • v_complex := by
        ext i
        have h_eq : (A *ᵥ v) i = μ * v i := by
          simpa using congr_fun hv_eig_vec i
        simpa [v_complex, smul_eq_mul, mulVec, dotProduct, map_apply] using
          congrArg (fun x : ℝ => (x : ℂ)) h_eq
      exact mem_spectrum_of_eigenvalue hvc_ne_zero hvc_eig
    have h_bound := eigenvalue_abs_le_perron_root hA_irred hA_nonneg hμ_complex
    rwa [Complex.norm_ofReal] at h_bound

/- The two `spectralRadius` bridge theorems from the original file are omitted:
they were `sorry`d upstream and are not needed by the Gantmacher-Krein route,
which works directly with `perronRoot`. -/

/--
**Perron–Frobenius at the spectral radius:** an irreducible nonnegative matrix admits a strictly
positive right eigenvector for `(spectralRadius ℝ A).toReal`, the common value of the spectral radius
and the Perron root. (From https://lean-lang.org/eval/problems/irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius/)
-/
theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
      (∀ i, 0 < v i) := by
  have hA_nonneg : ∀ i j, 0 ≤ A i j := hA.nonneg
  have h_r_pos := perronRoot_pos_of_irreducible hA hA_nonneg
  have h_r_in_spec := perron_root_is_eigenvalue hA hA_nonneg
  have h_r_is_max := (perron_root_is_spectral_radius hA hA_nonneg).2
  -- Prove spectral radius equals nnnorm of Perron root
  have h_spectral_le : spectralRadius ℝ A ≤ ‖(perronRoot A : ℝ)‖₊ := by
    rw [spectralRadius_eq_of_unital]
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    simp only [ENNReal.coe_le_coe]
    have h := h_r_is_max μ hμ
    rw [Real.nnnorm_of_nonneg h_r_pos.le, ← NNReal.coe_le_coe, NNReal.coe_mk]
    calc (‖μ‖₊ : ℝ) = ‖μ‖ := rfl
      _ = |μ| := Real.norm_eq_abs μ
      _ ≤ perronRoot A := h
  have h_spectral_ge : ‖(perronRoot A : ℝ)‖₊ ≤ spectralRadius ℝ A := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂_of_le (perronRoot A) h_r_in_spec le_rfl
  have h_spectral_eq : spectralRadius ℝ A = ‖(perronRoot A : ℝ)‖₊ := le_antisymm h_spectral_le h_spectral_ge
  have h_toReal_eq : (spectralRadius ℝ A).toReal = perronRoot A := by
    simp [h_spectral_eq, Real.norm_of_nonneg h_r_pos.le]
  rw [h_toReal_eq]
  obtain ⟨r, v, hr_pos, hv_pos, h_eig, h_eq⟩ := perron_root_eq_positive_eigenvalue hA hA_nonneg
  refine ⟨v, ?_, hv_pos⟩
  rw [h_eq]
  exact ⟨by rw [Module.End.mem_eigenspace_iff, toLin'_apply]; exact h_eig,
         Pi.ne_zero_of_pos hv_pos⟩

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- If `A i j > 0` and `x j ≠ 0`, then the term `(A i j : ℂ) * x j` is non-zero. -/
lemma term_ne_zero_of_pos_entry {A : Matrix n n ℝ} {x : n → ℂ}
    {i j : n} (hAij_pos : 0 < A i j) (hxj_ne_zero : x j ≠ 0) :
    (A i j : ℂ) * x j ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr hAij_pos.ne') hxj_ne_zero

/-! ### Triangle equality and phases

Further lemmas building on norm-sum layer (`aligned_term_of_triangle_eq`, etc.). -/

lemma aligned_term_of_triangle_eq {ι : Type*} {s : Finset ι} {v : ι → ℂ}
    (h_sum : ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖)
    {j : ι} (h_j : j ∈ s) (h_vj_ne_zero : v j ≠ 0) :
    let sum := ∑ i ∈ s, v i
    v j / ↑‖v j‖ = sum / ↑‖sum‖ := by
  intro sum
  have h_sum_ne_zero : sum ≠ 0 := by
    intro h_sum_zero
    have h_norm_sum : ‖sum‖ = 0 := by rw [h_sum_zero, norm_zero]
    have h_sum_norms : ∑ i ∈ s, ‖v i‖ = 0 := by rw [← h_sum, h_norm_sum]
    have h_vj_zero : ‖v j‖ = 0 := norm_eq_zero_of_finset_sum_norm_eq_zero v h_sum_norms j h_j
    exact h_vj_ne_zero (norm_eq_zero.mp h_vj_zero)
  have h_aligned := Complex.aligned_of_triangle_eq rfl h_sum h_sum_ne_zero j h_j h_vj_ne_zero
  exact h_aligned

/-- Nonzero terms in a global triangle equality share the phase of the total sum. -/
lemma Complex.phase_eq_of_fintype_triangle_eq {ι : Type*} [Fintype ι] {v : ι → ℂ}
    (hτ : ‖∑ i, v i‖ = ∑ i, ‖v i‖) {i j : ι} (hi : v i ≠ 0) (hj : v j ≠ 0) :
    v i / ↑‖v i‖ = v j / ↑‖v j‖ :=
    (aligned_term_of_triangle_eq hτ (Finset.mem_univ i) hi).trans
    (aligned_term_of_triangle_eq hτ (Finset.mem_univ j) hj).symm

/--
If an eigenvalue `μ` of a primitive matrix `A` has norm equal to the Perron root,
then the vector of norms of its eigenvector `x`, `|x|`, is strictly positive.
-/
lemma eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (_ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (_ : ‖μ‖ = perronRoot A)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0) (_ : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖)) :
    ∀ i, 0 < ‖x i‖ := by
  have h_x_abs_ne_zero : (fun j => ‖x j‖) ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_x_abs_nonneg : ∀ j, 0 ≤ ‖x j‖ := fun j => norm_nonneg _
  have h_r_pos : 0 < perronRoot A :=
    perronRoot_pos_of_irreducible (Matrix.IsPrimitive.isIrreducible hA_prim) hA_nonneg
  exact eigenvector_of_primitive_is_positive hA_prim h_r_pos h_x_abs_eig h_x_abs_nonneg h_x_abs_ne_zero

omit [Nonempty n] in
/-- The norm of a matrix-vector product equals the perron root to the kth power times the norm of the vector component. -/
lemma norm_matrix_power_vec_eq_perron_power_norm
    {A : Matrix n n ℝ} {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_norm_eq_r : ‖μ‖ = perronRoot A)
    (k : ℕ) (m : n) :
    ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖ = (perronRoot A) ^ k * ‖x m‖ := by
  have h_k_power : ((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x = (μ ^ k) • x :=
    mulVec_map_pow_eq_smul_pow_of_mulVec_map_smul (algebraMap ℝ ℂ) hx_eig k
  have h_component : ((μ ^ k) • x) m = (μ ^ k) * x m := by simp [Pi.smul_apply]
  calc ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖
    = ‖((μ ^ k) • x) m‖ := by rw [h_k_power]
    _ = ‖(μ ^ k) * x m‖ := by rw [h_component]
    _ = ‖μ ^ k‖ * ‖x m‖ := by rw [norm_mul]
    _ = ‖μ‖ ^ k * ‖x m‖ := by rw [norm_pow]
    _ = (perronRoot A) ^ k * ‖x m‖ := by rw [h_norm_eq_r]

omit [Nonempty n] in
/-- For a primitive matrix power, triangle equality holds for the eigenvector equation. -/
lemma triangle_equality_for_primitive_power
    {A : Matrix n n ℝ} (_ : IsPrimitive A)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) • (fun i ↦ ‖x i‖))
    (h_norm_eq_r : ‖μ‖ = perronRoot A)
    (m : n) (k : ℕ) (hAk_pos : ∀ i j, 0 < (A ^ k) i j) :
    ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ := by
  have h_left : ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = (perronRoot A) ^ k * ‖x m‖ := by
    have h_eq : ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖ := by
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [h_eq]
    exact norm_matrix_power_vec_eq_perron_power_norm hx_eig h_norm_eq_r k m
  have h_right : ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = (perronRoot A) ^ k * ‖x m‖ :=
    sum_component_norms_eq_perron_power_norm h_x_abs_eig k m hAk_pos
  rw [h_left, h_right]

omit [Nonempty n] in
/-- Components align with their weighted versions under positive scaling. -/
lemma component_phase_alignment
    {A : Matrix n n ℝ} {x : n → ℂ} {k : ℕ} {m i : n}
    (hAk_pos : 0 < (A ^ k) m i)
    (hx_abs_pos : 0 < ‖x i‖) :
    x i / ‖x i‖ = ((A ^ k) m i : ℂ) * x i / ‖((A ^ k) m i : ℂ) * x i‖ := by
  have h_ne : x i ≠ 0 := norm_pos_iff.mp hx_abs_pos
  exact (Complex.aligned_of_mul_of_real_pos hAk_pos rfl h_ne).symm

/-- Phase propagation along a strictly-positive power of a primitive matrix. -/
lemma entries_share_phase_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) =
                     (perronRoot A) • (fun i ↦ ‖x i‖))
    (h_norm_eq_r : ‖μ‖ = perronRoot A)
    (hx_abs_pos : ∀ i, 0 < ‖x i‖) :
    ∀ i j : n, x i / ‖x i‖ = x j / ‖x j‖ := by
  obtain ⟨k, _hk_pos, hAk_pos⟩ := hA_prim.2
  intro i j
  obtain ⟨m⟩ := ‹Nonempty n›
  let v l := ((A ^ k) m l : ℂ) * x l
  have hτ := triangle_equality_for_primitive_power hA_prim hx_eig h_x_abs_eig h_norm_eq_r m k hAk_pos
  have hi := term_ne_zero_of_pos_entry (hAk_pos m i) (norm_pos_iff.mp (hx_abs_pos i))
  have hj := term_ne_zero_of_pos_entry (hAk_pos m j) (norm_pos_iff.mp (hx_abs_pos j))
  calc
    x i / ‖x i‖ = v i / ‖v i‖ := component_phase_alignment (hAk_pos m i) (hx_abs_pos i)
    _ = v j / ‖v j‖ := Complex.phase_eq_of_fintype_triangle_eq hτ hi hj
    _ = x j / ‖x j‖ := (component_phase_alignment (hAk_pos m j) (hx_abs_pos j)).symm

lemma eigenvector_phase_aligned_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (_ : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_norm_eq_r : ‖μ‖ = perronRoot A)
    {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) • (fun i ↦ ‖x i‖))
    (hx_abs_pos : ∀ i, 0 < ‖x i‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ x = fun i ↦ c * ‖x i‖ := by
  obtain ⟨i₀⟩ := ‹Nonempty n›
  let c   : ℂ := x i₀ / ‖x i₀‖
  have hc_norm : ‖c‖ = 1 := by
    have h_pos : 0 < ‖x i₀‖ := hx_abs_pos i₀
    simp [c, h_pos.ne']
  have h_same_phase : ∀ j : n, x j / ‖x j‖ = c := by
    intro j
    simp_rw [c]
    exact entries_share_phase_of_primitive hA_prim hx_eig h_x_abs_eig h_norm_eq_r hx_abs_pos j i₀
  refine ⟨c, hc_norm, ?_⟩
  funext j
  have hnorm_ne_zero : ‖x j‖ ≠ 0 := (hx_abs_pos j).ne'
  calc
    x j = (x j / ‖x j‖) * ‖x j‖ := by
      simpa using eq_mul_div_ofReal_norm_complex (x j) hnorm_ne_zero
    _ = c * ‖x j‖ := by rw [h_same_phase j]

omit [Nonempty n] [DecidableEq n] in
/-- Cancel a nonzero scalar from a scalar multiple eigenvector equation. -/
lemma mulVec_eq_smul_of_smul_eigenvector
    {B : Matrix n n ℂ} {μ c : ℂ} {x y : n → ℂ} (hc : c ≠ 0)
    (hx : x = c • y) (h_eig : B *ᵥ x = μ • x) :
    B *ᵥ y = μ • y := by
  apply Pi.smul_left_cancel₀ hc
  simpa [hx, Matrix.mulVec_smul, smul_comm μ c y] using h_eig

omit [Nonempty n] [DecidableEq n] in
/-- Read a real `mulVec` eigenvector equation after complexifying the matrix and vector. -/
lemma mulVec_map_complex_apply_of_real_eigenvector
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : A *ᵥ v = r • v) (i : n) :
    ((A.map (algebraMap ℝ ℂ)) *ᵥ (fun j => (v j : ℂ))) i = (r : ℂ) * (v i : ℂ) := by
  simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) (congr_fun h i)

omit [Nonempty n] [DecidableEq n] in
/--
If an eigenvector `x` is phase‐aligned, i.e. `x i = c * ‖x i‖` for every `i`,
then its eigenvalue `μ` is real and coincides with the eigenvalue `r`
of the real vector `‖x‖`.
-/
lemma eigenvalue_eq_of_phase_aligned
    {A : Matrix n n ℝ} {μ : ℂ} {c : ℂ} (hc_norm : ‖c‖ = 1)
    {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_phase : ∀ i, x i = c * ‖x i‖)
    {r : ℝ} (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = r • (fun i ↦ ‖x i‖))
    {i : n} (hx_abs_pos_i : 0 < ‖x i‖) :
    μ = r := by
  let xAbs : n → ℝ := fun j => ‖x j‖
  let xAbsC : n → ℂ := fun j => (xAbs j : ℂ)
  have hx_repr : x = c • xAbsC := by
    funext j
    change x j = c * xAbsC j
    rw [h_phase j]
  have h_cancelled :
      (A.map (algebraMap ℝ ℂ)) *ᵥ xAbsC = μ • xAbsC := by
    exact mulVec_eq_smul_of_smul_eigenvector
      (Complex.ne_zero_of_norm_eq_one hc_norm) hx_repr hx_eig
  have h_real_C :
      ((A.map (algebraMap ℝ ℂ)) *ᵥ xAbsC) i = (r : ℂ) * xAbsC i := by
    simpa [xAbs, xAbsC] using
      mulVec_map_complex_apply_of_real_eigenvector h_x_abs_eig i
  have h_norm_ne_zero : xAbsC i ≠ 0 := by
    change ((‖x i‖ : ℝ) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr hx_abs_pos_i.ne'
  exact (mul_right_cancel₀ h_norm_ne_zero (by
    rw [← h_real_C]
    simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h_cancelled i)).symm

lemma norm_eigenvector_is_perron_eigenvector_of_primitive_boundary
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_norm_eq_r : ‖μ‖ = perronRoot A) :
    A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖) := by
  have h_subinv :
      (perronRoot A) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
    simpa [h_norm_eq_r] using eigenvalue_abs_subinvariant hA_nonneg hx_eig
  exact subinvariant_equality_implies_eigenvector
    (Matrix.IsPrimitive.isIrreducible (A := A) hA_prim)
    hA_nonneg
    (fun _ => norm_nonneg _)
    (normFun_complex_ne_zero_of_ne_zero hx_ne_zero)
    h_subinv

theorem spectral_dominance_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_norm_eq_r : ‖μ‖ = perronRoot A) :
    μ = perronRoot A := by
  obtain ⟨x, hx_ne_zero, hx_eig⟩ := exists_eigenvector_of_mem_spectrum h_is_eigenvalue
  have h_x_abs_eig :
      A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖) :=
    norm_eigenvector_is_perron_eigenvector_of_primitive_boundary
      hA_prim hA_nonneg hx_ne_zero hx_eig h_norm_eq_r
  have hx_abs_pos : ∀ i, 0 < ‖x i‖ :=
    eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root
      hA_prim hA_nonneg h_is_eigenvalue h_norm_eq_r
      hx_ne_zero hx_eig h_x_abs_eig
  obtain ⟨c, hc_norm, h_phase⟩ :=
    eigenvector_phase_aligned_of_primitive
      hA_prim hA_nonneg h_norm_eq_r
      hx_eig h_x_abs_eig hx_abs_pos
  obtain ⟨i⟩ := ‹Nonempty n›
  exact eigenvalue_eq_of_phase_aligned
    hc_norm hx_eig (fun i => congrFun h_phase i) h_x_abs_eig (hx_abs_pos i)

/--
**Spectral Dominance for Primitive Matrices**
(Seneta 1.1 (c)).
If `A` is primitive with Perron root `r`, every eigenvalue `μ ≠ r`
satisfies `‖μ‖ < r`.
-/
theorem spectral_dominance_of_primitive'
    (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (μ : ℂ) (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_ne_perron : μ ≠ perronRoot A) :
    ‖μ‖ < perronRoot A := by
  have hA_irred : A.IsIrreducible := Matrix.IsPrimitive.isIrreducible (A := A) hA_prim
  have h_le : ‖μ‖ ≤ perronRoot A := by
    exact @eigenvalue_abs_le_perron_root n _ _ _ A hA_irred hA_nonneg μ h_is_eigenvalue
  exact lt_of_le_of_ne h_le fun h_eq =>
    h_ne_perron <| @spectral_dominance_of_primitive n _ _ _ A hA_prim hA_nonneg μ h_is_eigenvalue h_eq

end Matrix
