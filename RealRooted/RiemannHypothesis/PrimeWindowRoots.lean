/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowOrthogonal

import RealRooted.RiemannHypothesis.PrimeWindowPolynomial
import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Analysis.Polynomial.OrderedRootPerturbation
import RealRooted.Bezoutian.RootEvaluation
import RealRooted.Jacobi

/-!
# Prime-window roots approaching shifted Legendre roots under RH

For every fixed degree, RH gives eventually simple real prime-window roots.
Their increasing enumeration approaches the increasing shifted Legendre roots
with error `O(1 / log X)`. The nodes are produced by coefficient perturbation;
their real-rootedness is not an input assumption.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

private theorem exists_uniform_ordered_root_factorization (n : ℕ) :
    ∃ r : Fin n → ℝ, StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n 0 0).IsRoot (r i)) ∧
      shiftedJacobiMonic n 0 0 = ∏ i : Fin n, (Polynomial.X - C (r i)) := by
  have hp : IsMonicOfDegree (shiftedJacobiMonic n 0 0) n :=
    ⟨natDegree_shiftedJacobiMonic n (by norm_num) (by norm_num),
      monic_shiftedJacobiMonic n (by norm_num) (by norm_num)⟩
  obtain ⟨r, hr, hroots⟩ := RealRooted.Polynomial.exists_strictMono_roots
    (RealRooted.shiftedJacobiMonic_splits n (by norm_num) (by norm_num)) hp.natDegree_eq
    (RealRooted.shiftedJacobiMonic_roots_nodup n (by norm_num) (by norm_num))
  refine ⟨r, hr, hroots, ?_⟩
  simpa only [hp.leadingCoeff_eq, map_one, one_mul] using
    RealRooted.Polynomial.splits_eq_C_mul_prod hp.monic.ne_zero hp.natDegree_eq
      r hroots hr.injective

/-- Every fixed-degree prime-window polynomial has eventually simple real roots
whose ordered errors from the shifted Legendre roots are `O(1 / log X)`. -/
theorem exists_primeWindowPolynomial_roots_sub_le (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ r : Fin n → ℝ, StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n 0 0).IsRoot (r i)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
        ∃ s : Fin n → ℝ, StrictMono s ∧
          (∀ i, (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).IsRoot
            (s i)) ∧
          ∀ i, |s i - r i| ≤ C / Real.log X := by
  obtain ⟨r, hr, href, hfactor⟩ := exists_uniform_ordered_root_factorization n
  have hp : IsMonicOfDegree (shiftedJacobiMonic n 0 0) n :=
    ⟨natDegree_shiftedJacobiMonic n (by norm_num) (by norm_num),
      monic_shiftedJacobiMonic n (by norm_num) (by norm_num)⟩
  obtain ⟨A, hA, hroots⟩ := eventually_exists_ordered_roots_abs_sub_le hp
    (RealRooted.shiftedJacobiMonic_splits n (by norm_num) (by norm_num))
    (RealRooted.shiftedJacobiMonic_roots_nodup n (by norm_num) (by norm_num))
    r hr hfactor
    (Filter.Eventually.of_forall fun X : ℝ ↦
      (Chebyshev.isMonicOfDegree_primeWindowPolynomial
        X (Real.sqrt X * Real.log X ^ 3) n).natDegree_eq.le)
    (fun k _ ↦ hRH.tendsto_coeff_primeWindowPolynomial n k)
  obtain ⟨B, hB, hcoeff⟩ := hRH.eventually_coeff_primeWindowPolynomial_sub_le n
  refine ⟨r, hr, href, A * B, mul_pos hA hB, ?_⟩
  filter_upwards [hroots, hcoeff, eventually_gt_atTop (1 : ℝ)] with X hroot hcoef hX
  obtain ⟨_, hsplit, hnodup, s, hsmono, hsroot, hsbound⟩ := hroot
  refine ⟨hsplit, hnodup, s, hsmono, hsroot, ?_⟩
  intro i
  have h := hsbound (B / Real.log X) (div_pos hB (Real.log_pos hX)).le
    (fun k _ ↦ hcoef k) i
  simpa only [mul_div_assoc] using h

/-- The ordered prime roots can be chosen as one family converging coordinatewise
to the actual ordered shifted Legendre roots, retaining the quantitative rate.
All root properties are eventual; the degree-zero enumeration is empty. -/
theorem exists_primeWindowPolynomial_roots_tendsto (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ (r : Fin n → ℝ) (s : ℝ → Fin n → ℝ) (C : ℝ), 0 < C ∧ StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n 0 0).IsRoot (r i)) ∧
      (∀ᶠ X : ℝ in atTop,
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
        StrictMono (s X) ∧
        (∀ i, (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).IsRoot
          (s X i)) ∧
        ∀ i, |s X i - r i| ≤ C / Real.log X) ∧
      ∀ i, Tendsto (fun X : ℝ ↦ s X i) atTop (𝓝 (r i)) := by
  classical
  obtain ⟨r, hr, href, C, hC, hroots⟩ := hRH.exists_primeWindowPolynomial_roots_sub_le n
  let P (X : ℝ) (s : Fin n → ℝ) : Prop := StrictMono s ∧
    (∀ i, (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).IsRoot
      (s i)) ∧ ∀ i, |s i - r i| ≤ C / Real.log X
  let s (X : ℝ) : Fin n → ℝ := if h : ∃ y, P X y then Classical.choose h else r
  have hselected (X : ℝ) (h : ∃ y, P X y) : P X (s X) := by
    dsimp only [s]
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  have hevent : ∀ᶠ X : ℝ in atTop,
      (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
      (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
      P X (s X) := by
    filter_upwards [hroots] with X hX
    exact ⟨hX.1, hX.2.1, hselected X hX.2.2⟩
  refine ⟨r, s, C, hC, hr, href, hevent, ?_⟩
  intro i
  have hlim : Tendsto (fun X : ℝ ↦ C / Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hevent, hlim.eventually (gt_mem_nhds hε)] with X hX hsmall
  rw [Real.dist_eq]
  exact (hX.2.2.2.2 i).trans_lt hsmall

end RiemannHypothesis
