/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public import Mathlib.Algebra.Polynomial.Splits

import RealRooted.Mathlib.Analysis.Polynomial.SimpleRootMatching
import RealRooted.Mathlib.Analysis.Polynomial.SimpleRootSeparation
import TauCeti.Topology.MetricSpace.SeparatedBalls
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear perturbation bounds for ordered real roots


The reference roots are supplied once as an increasing factorization. Coefficient
convergence produces all perturbed roots, without assuming they are real, and
the factor estimate gives a linear bound for each ordered node.
-/

public section

open Filter Topology Finset

noncomputable section

namespace Polynomial

/-- For fixed simple split reference data, bounded-degree coefficient convergence
gives ordered simple real roots with error bounded linearly by coefficient error.
The empty reference list, hence degree zero, is included. -/
theorem eventually_exists_ordered_roots_abs_sub_le
    {ι : Type*} {l : Filter ι} {Q : ι → ℝ[X]} {p : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hps : p.Splits) (hpnd : p.roots.Nodup)
    (r : Fin n → ℝ) (hr : StrictMono r)
    (hfactor : p = ∏ j : Fin n, (X - C (r j)))
    (hdegree : ∀ᶠ t in l, (Q t).natDegree ≤ n)
    (hcoeff : ∀ k ≤ n, Tendsto (fun t => (Q t).coeff k) l (𝓝 (p.coeff k))) :
    ∃ C > 0, ∀ᶠ t in l,
      (Q t).degree = n ∧ (Q t).Splits ∧ (Q t).roots.Nodup ∧
      ∃ s : Fin n → ℝ, StrictMono s ∧ (∀ i, (Q t).IsRoot (s i)) ∧
        ∀ δ : ℝ, 0 ≤ δ → (∀ k ≤ n, |(Q t).coeff k - p.coeff k| ≤ δ) →
          ∀ i, |s i - r i| ≤ C * δ := by
  let T : Finset ℝ := univ.image r
  have hrT (i : Fin n) : r i ∈ T := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨η, hη, _, hsepT⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := T) (U := fun _ => Set.univ) (fun _ _ => Filter.univ_mem)
  have hsep (i j : Fin n) (hij : i ≠ j) : 2 * η ≤ |r i - r j| := by
    have h := hsepT (r i) (hrT i) (r j) (hrT j) (hr.injective.ne hij)
    simpa only [Real.dist_eq] using h.le
  let B : ℝ := 1 + ∑ j : Fin n, |r j|
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hB (i : Fin n) : |r i| ≤ B := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
      abs_nonneg (r j)) (Finset.mem_univ i)
    dsimp only [B]
    linarith
  let K : ℝ := (∑ k ∈ range (n + 1), (B + η) ^ k) / η ^ (n - 1)
  let C : ℝ := K + 1
  have hC : 0 < C := by dsimp [C, K]; positivity
  have hrroots (i : Fin n) : r i ∈ p.roots := by
    apply (mem_roots hp.monic.ne_zero).mpr
    rw [IsRoot.def, hfactor, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (r i))
  have hmatch := eventually_roots_bijection_of_coeff_tendsto hp hps hpnd hdegree hcoeff hη
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdegree, hmatch] with t ht hmatched
  obtain ⟨hdeg, hsplit, hnodup, e, he, heclose⟩ := hmatched
  let s : Fin n → ℝ := fun i => e (r i)
  have hsclose (i : Fin n) : |s i - r i| < η := (heclose (r i) (hrroots i)).1
  have hsroot (i : Fin n) : (Q t).IsRoot (s i) := by
    apply isRoot_of_mem_roots
    apply Multiset.mem_toFinset.mp
    exact he.mapsTo (Multiset.mem_toFinset.mpr (hrroots i))
  have hsmono : StrictMono s := by
    intro i j hij
    have hi := abs_lt.mp (hsclose i)
    have hj := abs_lt.mp (hsclose j)
    have hgap := hsep i j (ne_of_lt hij)
    rw [abs_of_neg (sub_neg.mpr (hr hij))] at hgap
    linarith
  refine ⟨hdeg, hsplit, hnodup, s, hsmono, hsroot, ?_⟩
  intro δ hδ herror i
  have herror' : ∀ k ≤ n, |p.coeff k - (Q t).coeff k| ≤ δ := by
    intro k hk
    simpa only [abs_sub_comm] using herror k hk
  have h := abs_sub_le_of_isRoot_of_close r hfactor ht (hsroot i) hη hB hδ herror'
    i (hsclose i).le (fun j hji => hsep i j hji.symm)
  change |s i - r i| ≤ K * δ at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hδ
  dsimp only [C]
  linarith

end Polynomial
