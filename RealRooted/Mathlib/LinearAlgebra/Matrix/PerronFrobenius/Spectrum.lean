/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Simplex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleRing.Principal

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
Polynomial.annIdealGenerator_eq_minpoly {𝕜 A} [Field 𝕜] [Ring A] [Algebra 𝕜 A] (a : A) :
  Polynomial.annIdealGenerator 𝕜 a = minpoly 𝕜 a.

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
repr : M ≃ₗ[R] (ι →₀ R): The isomorphism to the module of finitely supported functions
  (coordinates).
Basis.mk (hli : LinearIndependent R v) (hsp : Submodule.span R (Set.range v) = ⊤) : Basis ι R M.
Basis.linearIndependent : LinearIndependent R b.
Basis.span_eq : Submodule.span R (Set.range b) = ⊤.
Basis.ofVectorSpace K V : Basis (Basis.ofVectorSpaceIndex K V) K V (existence of a basis for vector
  spaces over a field K).
Pi.basisFun R n : Basis (Fin n) R (Fin n → R).
Linear Independence (LinearIndependent R v):
linearIndependent_iff.
LinearIndependent.cardinal_le_rank : #ι ≤ Module.rank R M (if Nontrivial R).
Rank (Cardinal-valued dimension): Module.rank R M : Cardinal.
Basis.mk_eq_rank'' (b : Basis ι R M) : #ι = Module.rank R M (for rings with Strong Rank Condition).
LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] N') (hf : Injective f).
LinearMap.rank_le_of_surjective (f : M →ₗ[R] N) (hf : Surjective f).
LinearMap.rank_range_add_rank_ker (f : M →ₗ[R] N) :
  Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ker f) = Module.rank R M
  (for rings with HasRankNullity, e.g., division rings).
rank_quotient_add_rank_of_divisionRing (p : Submodule K V).
Finrank (Nat-valued dimension): Module.finrank R M : ℕ.
finrank_eq_rank : ↑(finrank R M) = Module.rank R M (if Module.Finite R M and StrongRankCondition R).
FiniteDimensional K V: Typeclass, equivalent to Module.Finite K V for division rings.
FiniteDimensional.of_fintype_basis (b : Basis ι K V) [Fintype ι].
finrank_eq_card_basis [Fintype ι] (b : Basis ι K V) : finrank K V = Fintype.card ι
  (for StrongRankCondition R).
LinearMap.injective_iff_surjective [FiniteDimensional K V] (f : End K V).
Submodule.finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s ≠ ⊤) :
  finrank K s < finrank K V.
Submodule.finrank_quotient_add_finrank [FiniteDimensional K V] (N : Submodule K V).

III. Matrices

Matrix n n R (Square matrices, often n is a Fintype).
Matrix.det (A : Matrix n n R) : R.
Matrix.det_mul, Matrix.det_one, Matrix.det_transpose.
Matrix.isUnit_iff_isUnit_det.
Matrix.toLin' (A : Matrix n n R) : (Fin n → R) →ₗ[R] (Fin n → R)
  (matrix as a linear map on Fin n → R).
LinearMap.toMatrix (b₁ : Basis ι R M) (b₂ : Basis ι' R N) (f : M →ₗ[R] N) : Matrix ι' ι R.
Matrix.toLinAlgEquiv (b : Basis ι R M) [Fintype ι] [DecidableEq ι] : End R M ≃ₐ[R] Matrix ι ι R.
Matrix.charpoly (A : Matrix n n R) : R[X].
Matrix.aeval_self_charpoly A : Polynomial.aeval A (Matrix.charpoly A) = 0 (Cayley-Hamilton for
  matrices).
Matrix.charpoly_transpose A : Matrix.charpoly Aᵀ = Matrix.charpoly A.

IV. Endomorphisms, Eigenvalues, Eigenspaces, Spectrum

Module.End R M := M →ₗ[R] M.
LinearMap.det (f : End R M) : R.
LinearMap.det_toMatrix (b : Basis ι R M) f :
  Matrix.det (LinearMap.toMatrix b b f) = LinearMap.det f.
LinearMap.isUnit_iff_isUnit_det.
LinearMap.det_eq_sign_charpoly_coeff {R M} [CommRing R] [Module.Free R M] [Module.Finite R M]
  (f : End R M) : LinearMap.det f = (-1) ^ Module.finrank R M * (LinearMap.charpoly f).coeff 0.
LinearMap.charpoly (f : End R M) : R[X] (where M is finite and free).
LinearMap.aeval_self_charpoly f : Polynomial.aeval f (LinearMap.charpoly f) = 0 (Cayley-Hamilton for
  endomorphisms).
LinearMap.charpoly_toMatrix (b : Basis ι R M) f : (Matrix.toMatrix b b f).charpoly =
  LinearMap.charpoly f.
LinearMap.minpoly_dvd_charpoly {K V} [Field K] [FiniteDimensional K V] (f : End K V).
spectrum R a (for a : A in an R-algebra A).
spectrum.mem_iff : μ ∈ spectrum R a ↔ ¬IsUnit (algebraMap R A μ - a).
Matrix.spectrum_toLin' (A : Matrix n n R).
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
Module.End.hasEigenvalue_of_isRoot {f : End K V} {μ : K} (h : (minpoly K f).IsRoot μ) :
  HasEigenvalue f μ.
LinearMap.hasEigenvalue_zero_tfae (φ : End K M): List of equivalent conditions for 0 being an
  eigenvalue (e.g., det φ = 0, ker φ ≠ ⊥).
Module.End.exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V).
Module.End.eigenvectors_linearIndependent [NoZeroSMulDivisors R M] (f : End R M) (μs : Set R)
  (xs : μs → M) (h_eigenvec).


Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.
Declarations that RealRooted does not use were removed (2026-10-07).
Original path: MCMC/PF/LinearAlgebra/Matrix/Spectrum.lean
-/

public section

namespace Matrix
open LinearMap Polynomial Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## The Standard Simplex
-/

omit [DecidableEq n] in
lemma stdSimplex_nonempty [Nonempty n] : (RealRooted.standardSimplex ℝ n).Nonempty :=
  ⟨(Fintype.card n : ℝ)⁻¹ • 1, by simp [RealRooted.standardSimplex, Finset.sum_const, nsmul_eq_mul]⟩

end Matrix
