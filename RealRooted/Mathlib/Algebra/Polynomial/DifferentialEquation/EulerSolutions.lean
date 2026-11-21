/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.ResidueSolutions
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic

/-!
# Polynomial kernels of Euler operators followed by derivatives

The operator `U(θ) D^r - V(θ)` has one descending coefficient diagonal and one
ordinary diagonal. We reduce its full kernel to independent residue systems.
Source: unpublished proof notes, RealRooted issue #2345 and the comment of
2026-11-01, equations (1) and (2).
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- Polynomial functional calculus of the Euler operator `θ = X D`.
The monomial `X^k` is multiplied by `U(k)`. -/
@[expose] noncomputable def eulerPolynomialOperator (U : K[X]) : K[X] →ₗ[K] K[X] :=
  lsum fun k => U.eval (k : K) • monomial k

/-- Coefficient diagonal of polynomial Euler functional calculus. -/
theorem coeff_eulerPolynomialOperator (U p : K[X]) (k : ℕ) :
    (eulerPolynomialOperator U p).coeff k = U.eval (k : K) * p.coeff k := by
  classical
  simp only [eulerPolynomialOperator, lsum_apply, LinearMap.smul_apply,
    coeff_sum, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeff_monomial]
  rw [sum_def, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hk
    simp [notMem_support_iff.mp hk]

/-- At the polynomial `X`, functional calculus is the usual Euler operator. -/
theorem eulerPolynomialOperator_X (p : K[X]) :
    eulerPolynomialOperator X p = X * p.derivative := by
  ext k
  rw [coeff_eulerPolynomialOperator]
  cases k with
  | zero => simp
  | succ k =>
      rw [coeff_X_mul, coeff_derivative]
      simp [mul_comm]

/-- Multiplication of parameter polynomials is composition of Euler operators. -/
theorem eulerPolynomialOperator_mul (U V : K[X]) :
    eulerPolynomialOperator (U * V) =
      (eulerPolynomialOperator U).comp (eulerPolynomialOperator V) := by
  ext p k
  simp only [LinearMap.comp_apply, coeff_eulerPolynomialOperator, eval_mul]
  ring

/-- Powers of the Euler operator multiply the degree-`k` coefficient by `k^n`. -/
private theorem coeff_euler_power (n : ℕ) (p : K[X]) (k : ℕ) :
    (((eulerPolynomialOperator (X : K[X])) ^ n) p).coeff k =
      (k : K) ^ n * p.coeff k := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (((eulerPolynomialOperator (X : K[X])) ^ n)
        (eulerPolynomialOperator X p)).coeff k = _
      rw [ih, coeff_eulerPolynomialOperator, eval_X, pow_succ]
      ring

/-- The diagonal definition is exactly polynomial functional calculus in `θ`.
Together with `eulerPolynomialOperator_X`, this identifies it with `U(X D)`. -/
theorem eulerPolynomialOperator_eq_aeval (U : K[X]) :
    eulerPolynomialOperator U = aeval (eulerPolynomialOperator (X : K[X])) U := by
  induction U using Polynomial.induction_on' with
  | add U V hU hV =>
      rw [aeval_add, ← hU, ← hV]
      apply LinearMap.ext
      intro p
      ext k
      simp [coeff_eulerPolynomialOperator, add_mul]
  | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, aeval_mul, aeval_C, aeval_X_pow]
      apply LinearMap.ext
      intro p
      ext k
      change _ = (c • (((eulerPolynomialOperator (X : K[X])) ^ n) p)).coeff k
      rw [AddMonoidAlgebra.coeff_smul_apply, coeff_eulerPolynomialOperator, coeff_euler_power]
      simp [smul_eq_mul, mul_assoc]

/-- Apply `r` derivatives first, then `U(θ)`, and subtract `V(θ)`. -/
@[expose] noncomputable def eulerDerivativeOperator (U V : K[X]) (r : ℕ) : K[X] →ₗ[K] K[X] :=
  (eulerPolynomialOperator U).comp (derivative ^ r) - eulerPolynomialOperator V

/-- The arbitrary-order coefficient identity, with the full nonzero factorial factor. -/
theorem coeff_eulerDerivativeOperator (U V p : K[X]) (r k : ℕ) :
    (eulerDerivativeOperator U V r p).coeff k =
      ((k + r).descFactorial r : K) * U.eval (k : K) * p.coeff (k + r) -
        V.eval (k : K) * p.coeff k := by
  simp only [eulerDerivativeOperator, LinearMap.sub_apply, LinearMap.comp_apply,
    coeff_sub, coeff_eulerPolynomialOperator, pow_apply_eq_iterate,
    coeff_iterate_derivative, nsmul_eq_mul]
  ring

/-- The entire Euler-derivative kernel is exactly the residue coefficient space. -/
theorem ker_eulerDerivativeOperator (U V : K[X]) (r : ℕ) :
    LinearMap.ker (eulerDerivativeOperator U V r) =
      residueSolutions (fun k => ((k + r).descFactorial r : K) * U.eval (k : K))
        (fun k => V.eval (k : K)) r := by
  ext p
  constructor
  · intro hp k
    have h := congrArg (fun q : K[X] => q.coeff k) hp
    rw [coeff_eulerDerivativeOperator, coeff_zero] at h
    exact sub_eq_zero.mp h
  · intro hp
    ext k
    rw [coeff_eulerDerivativeOperator, coeff_zero, sub_eq_zero]
    exact hp k

/-- For one derivative, the finite two-diagonal classification applies directly. -/
theorem ker_eulerDerivativeOperator_one (U V : K[X]) :
    LinearMap.ker (eulerDerivativeOperator U V 1) =
      twoDiagonalSolutions (fun k => ((k : K) + 1) * U.eval (k : K))
        (fun k => V.eval (k : K)) := by
  rw [ker_eulerDerivativeOperator]
  congr 1
  funext k
  simp

/-- The leading coefficient of a nonzero solution is a natural root of `V`. -/
theorem eval_natDegree_eq_zero_of_eulerDerivativeOperator_eq_zero
    (U V : K[X]) {r : ℕ} (hr : 0 < r) {p : K[X]} (hp : p ≠ 0)
    (hode : eulerDerivativeOperator U V r p = 0) : V.eval (p.natDegree : K) = 0 := by
  have h := congrArg (fun q : K[X] => q.coeff p.natDegree) hode
  rw [coeff_eulerDerivativeOperator, coeff_zero,
    coeff_eq_zero_of_natDegree_lt (by lia), mul_zero, zero_sub, neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_right (leadingCoeff_ne_zero.mpr hp)

/-- No natural diagonal roots means no nonzero polynomial solutions. -/
theorem eq_zero_of_eulerDerivativeOperator_eq_zero
    (U V : K[X]) {r : ℕ} (hr : 0 < r)
    (hV : ∀ k : ℕ, V.eval (k : K) ≠ 0) {p : K[X]}
    (hode : eulerDerivativeOperator U V r p = 0) : p = 0 := by
  by_contra hp
  exact hV _ (eval_natDegree_eq_zero_of_eulerDerivativeOperator_eq_zero U V hr hp hode)

/-- Every one-derivative solution degree is characterized by interval zeros of `U`. -/
theorem exists_eulerDerivativeSolution_natDegree_iff [CharZero K]
    (U V : K[X]) (n : ℕ) :
    (∃ p : K[X], eulerDerivativeOperator U V 1 p = 0 ∧ p ≠ 0 ∧ p.natDegree = n) ↔
      V.eval (n : K) = 0 ∧ ∀ k < n, V.eval (k : K) = 0 →
        ∃ j ∈ Finset.Ico k n, U.eval (j : K) = 0 := by
  change (∃ p ∈ LinearMap.ker (eulerDerivativeOperator U V 1), p ≠ 0 ∧ p.natDegree = n) ↔ _
  rw [ker_eulerDerivativeOperator_one, exists_twoDiagonalSolution_natDegree_iff]
  unfold TwoDiagonalDegree
  congr! 4 with k hkn hk
  rw [Finset.prod_eq_zero_iff]
  apply exists_congr
  intro j
  have hpos : (j : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  simp [hpos]

open Classical in
/-- Natural diagonal roots in one residue class, indexed by the section exponent. -/
@[expose] noncomputable def eulerResidueRoots [CharZero K] (V : K[X])
    {r : ℕ} (hr : 0 < r) (i : Fin r) : Finset ℕ :=
  V.roots.toFinset.preimage (fun k : ℕ => (((i : ℕ) + r * k : ℕ) : K))
    (by
      intro j _ k _ h
      have heq : (i : ℕ) + r * j = (i : ℕ) + r * k := Nat.cast_injective h
      nlinarith)

/-- The residue-root set is exact when `V` is nonzero. -/
theorem mem_eulerResidueRoots_iff [CharZero K] (V : K[X]) (hV : V ≠ 0)
    {r : ℕ} (hr : 0 < r) (i : Fin r) (k : ℕ) :
    k ∈ eulerResidueRoots V hr i ↔ V.eval (((i : ℕ) + r * k : ℕ) : K) = 0 := by
  classical
  simp [eulerResidueRoots, mem_roots hV, IsRoot.def]

/-- Admissibility in a residue class depends only on integer zeros of `U`,
since all descending-factorial factors are nonzero in characteristic zero. -/
theorem twoDiagonalDegree_euler_residue_iff [CharZero K] (U V : K[X])
    (r i n : ℕ) :
    TwoDiagonalDegree
      (fun k => (((i + r * k + r).descFactorial r : ℕ) : K) * U.eval ((i + r * k : ℕ) : K))
      (fun k => V.eval ((i + r * k : ℕ) : K)) n ↔
      V.eval ((i + r * n : ℕ) : K) = 0 ∧
        ∀ k < n, V.eval ((i + r * k : ℕ) : K) = 0 →
          ∃ j ∈ Finset.Ico k n, U.eval ((i + r * j : ℕ) : K) = 0 := by
  unfold TwoDiagonalDegree
  congr! 4 with k hkn hk
  rw [Finset.prod_eq_zero_iff]
  apply exists_congr
  intro j
  have hfac : (((i + r * j + r).descFactorial r : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by lia : r ≤ i + r * j + r)).ne'
  simp [hfac]

/-- Complete coordinates for arbitrary derivative order. Each coordinate index
is exactly an admissible root in its residue class. -/
noncomputable def eulerSolutionCoordinates [CharZero K] (U V : K[X]) (hV : V ≠ 0)
    {r : ℕ} (hr : 0 < r) :
    LinearMap.ker (eulerDerivativeOperator U V r) ≃ₗ[K]
      ∀ i : Fin r, twoDiagonalDegrees
        (fun k => (((i + r * k + r).descFactorial r : ℕ) : K) * U.eval ((i + r * k : ℕ) : K))
        (fun k => V.eval ((i + r * k : ℕ) : K)) (eulerResidueRoots V hr i) → K :=
  (LinearEquiv.ofEq _ _ (ker_eulerDerivativeOperator U V r)).trans
    (residueSolutionCoordinates _ _ hr (eulerResidueRoots V hr)
      (fun i k hk => (mem_eulerResidueRoots_iff V hV hr i k).mpr hk))

/-- The complete dimension formula for `U(θ)D^r - V(θ)`: count the admissible
roots in each residue class. The preceding theorem removes the factorial factors
and the nearest-zero lemma reduces all interval tests to consecutive roots. -/
theorem finrank_ker_eulerDerivativeOperator [CharZero K] (U V : K[X]) (hV : V ≠ 0)
    {r : ℕ} (hr : 0 < r) :
    Module.finrank K (LinearMap.ker (eulerDerivativeOperator U V r)) =
      ∑ i : Fin r, (twoDiagonalDegrees
        (fun k => (((i + r * k + r).descFactorial r : ℕ) : K) * U.eval ((i + r * k : ℕ) : K))
        (fun k => V.eval ((i + r * k : ℕ) : K)) (eulerResidueRoots V hr i)).card := by
  rw [(eulerSolutionCoordinates U V hV hr).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Possible degrees for arbitrary derivative order, expressed solely using
integer roots of `U` and `V` within the relevant residue class. -/
theorem exists_eulerDerivativeSolution_natDegree_iff_residue [CharZero K]
    (U V : K[X]) {r : ℕ} (hr : 0 < r) (d : ℕ) :
    (∃ p : K[X], eulerDerivativeOperator U V r p = 0 ∧ p ≠ 0 ∧ p.natDegree = d) ↔
      V.eval (d : K) = 0 ∧ ∀ k < d / r, V.eval ((d % r + r * k : ℕ) : K) = 0 →
        ∃ j ∈ Finset.Ico k (d / r), U.eval ((d % r + r * j : ℕ) : K) = 0 := by
  change (∃ p ∈ LinearMap.ker (eulerDerivativeOperator U V r), p ≠ 0 ∧ p.natDegree = d) ↔ _
  rw [ker_eulerDerivativeOperator, exists_residueSolution_natDegree_iff _ _ hr,
    twoDiagonalDegree_euler_residue_iff, Nat.mod_add_div]

/-- A complete basis of polynomial Euler-derivative solutions. Its indices
are the admissible degrees grouped by residue; its vectors are the monic
single-residue polynomials in `residueSolutionBasis`. -/
noncomputable def eulerSolutionBasis [CharZero K] (U V : K[X]) (hV : V ≠ 0)
    {r : ℕ} (hr : 0 < r) :
    Module.Basis (Σ i : Fin r, twoDiagonalDegrees
      (fun k => (((i + r * k + r).descFactorial r : ℕ) : K) * U.eval ((i + r * k : ℕ) : K))
      (fun k => V.eval ((i + r * k : ℕ) : K)) (eulerResidueRoots V hr i)) K
      (LinearMap.ker (eulerDerivativeOperator U V r)) :=
  (residueSolutionBasis _ _ hr (eulerResidueRoots V hr)
    (fun i k hk => (mem_eulerResidueRoots_iff V hV hr i k).mpr hk)).map
    (LinearEquiv.ofEq _ _ (ker_eulerDerivativeOperator U V r).symm)

end Polynomial
