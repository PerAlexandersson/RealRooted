/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.  Original path: MCMC/PF/LinearAlgebra/Matrix/Spectrum.lean
-/
import Mathlib.Algebra.Lie.OfAssociative
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Simplex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleRing.Principal

-- Ported third-party code; keep original line layout.
set_option linter.style.longLine false

/-! # Perron-Frobenius Theory for Matrices

This file develops the essential Perron-Frobenius theory needed for MCMC convergence proofs.

I. Core Algebraic Structures & Utilities

Rings/Fields:
CommRing R, DivisionRing K, Field K
Nontrivial R: Typeclass asserting R has at least two distinct elements.
Modules/Vector Spaces:
Module R M: Standard R-module structure on M.
VectorSpace K V: Alias for Module K V when K is a field.
Algebras:
Algebra R A: A is an R-algebra.
algebraMap R A : R →+* A: The structural ring homomorphism.
Polynomials (R[X] or Polynomial R):
Polynomial.eval (μ : R) (p : R[X]) : R: Evaluation of polynomial p at scalar μ.
Polynomial.aeval (a : A) (p : R[X]) : A: Evaluation of p at an element a in an R-algebra A.
Polynomial.IsRoot p μ : Prop := Polynomial.eval μ p = 0.
Polynomial.coeff p n : R: The n-th coefficient of p.
Polynomial.leadingCoeff p : R.
Polynomial.monic p : Prop.
Polynomial.natDegree p : ℕ.
Polynomial.natTrailingDegree p : ℕ.
minpoly K a : K[X]: Minimal polynomial of a : A over a field K.
minpoly.aeval K a : aeval a (minpoly K a) = 0.
minpoly.dvd K a p (hp : aeval a p = 0) : minpoly K a ∣ p.
Polynomial.annIdealGenerator_eq_minpoly {𝕜 A} [Field 𝕜] [Ring A] [Algebra 𝕜 A] (a : A) : Polynomial.annIdealGenerator 𝕜 a = minpoly 𝕜 a.

II. Linear Algebra: Maps, Submodules, Basis, Dimension

Linear Maps (M →ₗ[R] N):
LinearMap.ker : Submodule R M, LinearMap.range : Submodule R N.
LinearMap.id : M →ₗ[R] M, LinearMap.comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) : M →ₗ[R] P.
Function.Injective, Function.Surjective, Function.Bijective.
LinearMap.quotKerEquivRange (f : M →ₗ[R] N) : M ⧸ LinearMap.ker f ≃ₗ[R] LinearMap.range f.
Linear Equivalences (M ≃ₗ[R] N).
Submodules (Submodule R M):
⊥ (zero submodule), ⊤ (entire module).
Submodule.span R (s : Set M) : Submodule R M.
Submodule.mkQ (p : Submodule R M) : M →ₗ[R] M ⧸ p (quotient map).
Basis (Basis ι R M):
b i : M: The i-th basis vector.
repr : M ≃ₗ[R] (ι →₀ R): The isomorphism to the module of finitely supported functions (coordinates).
Basis.mk (hli : LinearIndependent R v) (hsp : Submodule.span R (Set.range v) = ⊤) : Basis ι R M.
Basis.linearIndependent : LinearIndependent R b.
Basis.span_eq : Submodule.span R (Set.range b) = ⊤.
Basis.ofVectorSpace K V : Basis (Basis.ofVectorSpaceIndex K V) K V (existence of a basis for vector spaces over a field K).
Pi.basisFun R n : Basis (Fin n) R (Fin n → R).
Linear Independence (LinearIndependent R v):
linearIndependent_iff.
LinearIndependent.cardinal_le_rank : #ι ≤ Module.rank R M (if Nontrivial R).
Rank (Cardinal-valued dimension): Module.rank R M : Cardinal.
Basis.mk_eq_rank'' (b : Basis ι R M) : #ι = Module.rank R M (for rings with Strong Rank Condition).
LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] N') (hf : Injective f).
LinearMap.rank_le_of_surjective (f : M →ₗ[R] N) (hf : Surjective f).
LinearMap.rank_range_add_rank_ker (f : M →ₗ[R] N) : Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ker f) = Module.rank R M (for rings with HasRankNullity, e.g., division rings).
rank_quotient_add_rank_of_divisionRing (p : Submodule K V).
Finrank (Nat-valued dimension): Module.finrank R M : ℕ.
finrank_eq_rank : ↑(finrank R M) = Module.rank R M (if Module.Finite R M and StrongRankCondition R).
FiniteDimensional K V: Typeclass, equivalent to Module.Finite K V for division rings.
FiniteDimensional.of_fintype_basis (b : Basis ι K V) [Fintype ι].
finrank_eq_card_basis [Fintype ι] (b : Basis ι K V) : finrank K V = Fintype.card ι (for StrongRankCondition R).
LinearMap.injective_iff_surjective [FiniteDimensional K V] (f : End K V).
Submodule.finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s ≠ ⊤) : finrank K s < finrank K V.
Submodule.finrank_quotient_add_finrank [FiniteDimensional K V] (N : Submodule K V).

III. Matrices

Matrix n n R (Square matrices, often n is a Fintype).
Matrix.det (A : Matrix n n R) : R.
Matrix.det_mul, Matrix.det_one, Matrix.det_transpose.
Matrix.isUnit_iff_isUnit_det.
Matrix.det_smul_sub_eq_eval_charpoly (A : Matrix n n ℝ) (μ : ℝ) : det (μ • 1 - A) = (Matrix.charpoly A).eval μ.
Matrix.toLin' (A : Matrix n n R) : (Fin n → R) →ₗ[R] (Fin n → R) (matrix as a linear map on Fin n → R).
LinearMap.toMatrix (b₁ : Basis ι R M) (b₂ : Basis ι' R N) (f : M →ₗ[R] N) : Matrix ι' ι R.
Matrix.toLinAlgEquiv (b : Basis ι R M) [Fintype ι] [DecidableEq ι] : End R M ≃ₐ[R] Matrix ι ι R.
Matrix.charpoly (A : Matrix n n R) : R[X].
Matrix.aeval_self_charpoly A : Polynomial.aeval A (Matrix.charpoly A) = 0 (Cayley-Hamilton for matrices).
Matrix.charpoly_transpose A : Matrix.charpoly Aᵀ = Matrix.charpoly A.

IV. Endomorphisms, Eigenvalues, Eigenspaces, Spectrum

Module.End R M := M →ₗ[R] M.
LinearMap.det (f : End R M) : R.
LinearMap.det_toMatrix (b : Basis ι R M) f : Matrix.det (LinearMap.toMatrix b b f) = LinearMap.det f.
LinearMap.isUnit_iff_isUnit_det.
LinearMap.det_eq_sign_charpoly_coeff {R M} [CommRing R] [Module.Free R M] [Module.Finite R M] (f : End R M) : LinearMap.det f = (-1) ^ Module.finrank R M * (LinearMap.charpoly f).coeff 0.
LinearMap.charpoly (f : End R M) : R[X] (where M is finite and free).
LinearMap.aeval_self_charpoly f : Polynomial.aeval f (LinearMap.charpoly f) = 0 (Cayley-Hamilton for endomorphisms).
LinearMap.charpoly_toMatrix (b : Basis ι R M) f : (Matrix.toMatrix b b f).charpoly = LinearMap.charpoly f.
LinearMap.minpoly_dvd_charpoly {K V} [Field K] [FiniteDimensional K V] (f : End K V).
spectrum R a (for a : A in an R-algebra A).
spectrum.mem_iff : μ ∈ spectrum R a ↔ ¬IsUnit (algebraMap R A μ - a).
Matrix.spectrum_eq_spectrum_toLin' (A : Matrix n n ℝ).
Module.End.hasEigenvalue_iff_mem_spectrum {f : End K V} {μ : K}.
Matrix.mem_spectrum_iff_isRoot_charpoly (A : Matrix n n ℝ) (μ : ℝ).
Module.End.HasEigenvalue (f : End R M) (μ : R) : Prop.
Module.End.HasEigenvector (f : End R M) (μ : R) (x : M) : Prop.
Module.End.HasEigenvector.apply_eq_smul (h : HasEigenvector f μ x) : f x = μ • x.
Module.End.eigenspace (f : End R M) (μ : R) : Submodule R M.
Module.End.eigenspace_def : eigenspace f μ = LinearMap.ker (f - μ • LinearMap.id).
Module.End.mem_eigenspace_iff : x ∈ eigenspace f μ ↔ f x = μ • x.
Module.End.genEigenspace (f : End R M) (μ : R) (k : ℕ∞).
Module.End.maxGenEigenspace (f : End R M) (μ : R) := ⨆ k, genEigenspace f μ k.
Module.End.iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V).
Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace (hf : f.IsFinitelySemisimple).
Module.End.isRoot_of_hasEigenvalue {f : End K V} {μ : K} (h : HasEigenvalue f μ) : (minpoly K f).IsRoot μ.
Module.End.hasEigenvalue_of_isRoot {f : End K V} {μ : K} (h : (minpoly K f).IsRoot μ) : HasEigenvalue f μ.
LinearMap.hasEigenvalue_zero_tfae (φ : End K M): List of equivalent conditions for 0 being an eigenvalue (e.g., det φ = 0, ker φ ≠ ⊥).
Matrix.hasEigenvalue_toLin'_iff_det_sub_eq_zero (A : Matrix n n ℝ) (μ : ℝ).
Module.End.exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V).
Module.End.eigenvectors_linearIndependent [NoZeroSMulDivisors R M] (f : End R M) (μs : Set R) (xs : μs → M) (h_eigenvec).

-/

namespace Matrix
open LinearMap Polynomial Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## The Standard Simplex
-/

omit [DecidableEq n] in
lemma stdSimplex_nonempty [Nonempty n] : (RealRooted.standardSimplex ℝ n).Nonempty :=
  ⟨(Fintype.card n : ℝ)⁻¹ • 1, by simp [RealRooted.standardSimplex, Finset.sum_const, nsmul_eq_mul]⟩

/-!
## Spectral Properties of Matrices
-/

/-- The spectrum of a matrix `A` is equal to the spectrum of its corresponding linear map
`Matrix.toLin' A`. -/
lemma spectrum_eq_spectrum_toLin' (A : Matrix n n ℝ) :
    spectrum ℝ A = spectrum ℝ (Matrix.toLin' A) := by
  exact Eq.symm (AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (Pi.basisFun ℝ n)) A)

/-- The determinant of `μ • 1 - A` is the evaluation of the characteristic polynomial of `A` at `μ`. -/
lemma det_smul_sub_eq_eval_charpoly (A : Matrix n n ℝ) (μ : ℝ) :
    det (μ • 1 - A) = (Matrix.charpoly A).eval μ := by
  have h : μ • 1 = Matrix.scalar n μ := by
    ext i j
    simp [Matrix.scalar, Matrix.one_apply, smul_apply]
    rfl
  rw [h]
  rw [← eval_charpoly A μ]


/-!
## Determinant, Kernel, and Invertibility
-/
open Module

/-!
# Perron-Frobenius Theory for Matrices

This file provides core lemmas and theorems related to the Perron-Frobenius theory for non-negative,
irreducible matrices.
-/

open LinearMap

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- If the kernel of a linear endomorphism on a finite-dimensional vector space is non-trivial,
    then its determinant is zero. -/
lemma det_eq_zero_of_ker_ne_bot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : V →ₗ[K] V} (h : LinearMap.ker f ≠ ⊥) :
    LinearMap.det f = 0 := by
  by_contra h_det_ne_zero
  have h_det_unit : IsUnit (LinearMap.det f) := IsUnit.mk0 _ h_det_ne_zero
  have h_f_is_unit : IsUnit f := by
    let b := Module.Basis.ofVectorSpace K V
    classical
    have h_det_matrix_unit : IsUnit (Matrix.det (LinearMap.toMatrix b b f)) := by
      rw [LinearMap.det_toMatrix b f]
      exact h_det_unit
    have h_toMatrix_unit : IsUnit (LinearMap.toMatrix b b f) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr h_det_matrix_unit
    rw [← isUnit_map_iff ((Matrix.toLinAlgEquiv b).symm) f]
    exact h_toMatrix_unit
  have h_ker_eq_bot : LinearMap.ker f = ⊥ := by
    rw [← LinearMap.isUnit_iff_ker_eq_bot]
    exact h_f_is_unit
  exact h h_ker_eq_bot

/-- A real number `μ` is an eigenvalue of a matrix `A` if and only if `det(μ • 1 - A) = 0`. -/
lemma hasEigenvalue_toLin'_iff_det_sub_eq_zero (A : Matrix n n ℝ) (μ : ℝ) :
    Module.End.HasEigenvalue (toLin' A) μ ↔ det (μ • 1 - A) = 0 := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, ← spectrum_eq_spectrum_toLin',
    mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, det_smul_sub_eq_eval_charpoly]

/-! ## Spectral Radius Theory for Matrices -/

lemma LinearMap.bijective_iff_ker_eq_bot_and_range_eq_top {R : Type*} [Field R] {M : Type*}
    [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) :
    Function.Bijective f ↔ LinearMap.ker f = ⊥ ∧ LinearMap.range f = ⊤ := by
  constructor
  · intro h
    constructor
    · exact LinearMap.ker_eq_bot_of_injective h.1
    · exact LinearMap.range_eq_top_of_surjective _ h.2
  · intro ⟨h_ker, h_range⟩
    constructor
    · exact LinearMap.ker_eq_bot.mp h_ker
    · exact LinearMap.range_eq_top.mp h_range

lemma ker_ne_bot_of_det_eq_zero (A : Matrix n n ℝ) :
    LinearMap.det (Matrix.toLin' A) = 0 → LinearMap.ker (Matrix.toLin' A) ≠ ⊥ := by
  contrapose!
  intro h_ker_bot
  have h_inj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot]
    exact h_ker_bot
  have h_isUnit : IsUnit (LinearMap.det (Matrix.toLin' A)) :=
    LinearMap.isUnit_det (Matrix.toLin' A) ((LinearMap.isUnit_iff_ker_eq_bot
      (toLin' A)).mpr h_ker_bot)
  exact IsUnit.ne_zero h_isUnit

-- Basic kernel-injectivity relationship
lemma ker_eq_bot_iff_injective_toLin' (A : Matrix n n ℝ) :
    LinearMap.ker (Matrix.toLin' A) = ⊥ ↔ Function.Injective (Matrix.toLin' A) := by
  exact LinearMap.ker_eq_bot

-- For finite dimensions, injective endomorphisms are bijective
lemma injective_iff_bijective_toLin' (A : Matrix n n ℝ) :
    Function.Injective (Matrix.toLin' A) ↔ Function.Bijective (Matrix.toLin' A) := by
  constructor
  · intro h_inj
    exact IsArtinian.bijective_of_injective_endomorphism (toLin' A) h_inj
  · exact fun h_bij => h_bij.1

-- Bijective linear maps are units
lemma bijective_iff_isUnit_toLin' (A : Matrix n n ℝ) :
    Function.Bijective (Matrix.toLin' A) ↔ IsUnit (Matrix.toLin' A) := by
  rw [LinearMap.bijective_iff_ker_eq_bot_and_range_eq_top]
  have h_equiv : LinearMap.range (Matrix.toLin' A) = ⊤ ↔ LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    Iff.symm LinearMap.ker_eq_bot_iff_range_eq_top
  rw [h_equiv, and_self]
  rw [LinearMap.isUnit_iff_ker_eq_bot]

lemma isUnit_of_det_ne_zero (A : Matrix n n ℝ) (h_det_ne_zero : LinearMap.det (Matrix.toLin' A) ≠ 0) :
    IsUnit (Matrix.toLin' A) := by
  rw [← bijective_iff_isUnit_toLin', ← injective_iff_bijective_toLin', ← ker_eq_bot_iff_injective_toLin']
  by_contra h_ker_ne_bot
  have h_det_zero : LinearMap.det (Matrix.toLin' A) = 0 := by
    exact det_eq_zero_of_ker_ne_bot h_ker_ne_bot
  exact h_det_ne_zero h_det_zero


-- An algebra equivalence preserves the property of being a unit.
lemma AlgEquiv.isUnit_map_iff {R A B : Type*} [CommSemiring R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (x : A) :
    IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h_ex_unit
    simp_all only [MulEquiv.isUnit_map]
  · intro h_x_unit
    simp_all only [MulEquiv.isUnit_map]

lemma spectrum.nnnorm_le_nnnorm_of_mem {𝕜 A : Type*}
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]
    (a : A) {k : 𝕜} (hk : k ∈ spectrum 𝕜 a) : ‖k‖₊ ≤ ‖a‖₊ := by
  have h_subset : spectrum 𝕜 a ⊆ Metric.closedBall 0 ‖a‖ :=
    spectrum.subset_closedBall_norm a
  have hk_in_ball : k ∈ Metric.closedBall 0 ‖a‖ := h_subset hk
  have h_norm_le : ‖k‖ ≤ ‖a‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hk_in_ball
    exact hk_in_ball
  exact h_norm_le



lemma vecMul_eq_mulVec_transpose {n : Type*} [Fintype n] (A : Matrix n n ℝ) (v : n → ℝ) :
    v ᵥ* A = Aᵀ *ᵥ v := by
  ext j
  change v ⬝ᵥ (fun i => A i j) = (fun i => A i j) ⬝ᵥ v
  rw [@dotProduct_comm]

lemma Module.End.exists_eigenvector_of_mem_spectrum {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : V →ₗ[K] V} {μ : K} (h_is_eigenvalue : μ ∈ spectrum K f) :
  ∃ v, v ≠ 0 ∧ f v = μ • v := by
  rw [spectrum.mem_iff, LinearMap.isUnit_iff_ker_eq_bot] at h_is_eigenvalue
  obtain ⟨v, hv_mem, hv_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_is_eigenvalue
  use v, hv_ne_zero
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv_mem
  exact (sub_eq_zero.mp hv_mem).symm

-- Core lemma: spectral radius is bounded by the operator norm
lemma spectralRadius_le_nnnorm {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
     [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]
    (a : A) :
    spectralRadius 𝕜 a ≤ ↑‖a‖₊ := by
  rw [spectralRadius_eq_of_unital]
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  have h_nnnorm_le : ‖μ‖₊ ≤ ‖a‖₊ := spectrum.nnnorm_le_nnnorm_of_mem a hμ
  exact ENNReal.coe_le_coe.mpr h_nnnorm_le

-- Specialized version for continuous linear maps

/-! ## Core Perron-Frobenius Theory -/

noncomputable def supportFinset (v : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => v i > 0)

/-- If a scalar `μ` is an eigenvalue of a matrix `A`, then it is a root of its
characteristic polynomial. -/
lemma isRoot_of_hasEigenvalue {A : Matrix n n ℝ} {μ : ℝ}
    (h_eig : Module.End.HasEigenvalue (toLin' A) μ) :
    (charpoly A).IsRoot μ := by
  rw [← mem_spectrum_iff_isRoot_charpoly, spectrum_eq_spectrum_toLin']
  exact Module.End.hasEigenvalue_iff_mem_spectrum.mp h_eig

/-- The spectrum of a matrix `A` is equal to the spectrum of its corresponding linear map
`Matrix.toLin' A`. -/
theorem spectrum.Matrix_toLin'_eq_spectrum {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    spectrum R (Matrix.toLin' A) = spectrum R A := by
  exact AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (Pi.basisFun R n)) A
end Matrix

/-- If a linear map `f` has an eigenvector `v` for an eigenvalue `μ`, then `μ` is in the spectrum of `f`. -/
lemma Module.End.mem_spectrum_of_hasEigenvector {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : V →ₗ[K] V} {μ : K} {v : V} (h : HasEigenvector f μ v) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector h
