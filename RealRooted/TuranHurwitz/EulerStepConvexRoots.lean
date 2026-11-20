module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
import RealRooted.TuranHurwitz.WeightedReciprocals
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Convex root regions for derivatives and positive Euler steps

These two preservation statements are the algebraic form of the sector
arguments in part (ii). The Euler weight can be any positive real number.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Every root of a derivative stays in any convex region containing the original roots. -/
theorem derivative_roots_mem_convex {S : Set ℂ} (hS : Convex ℝ S) {p : ℂ[X]}
    (hp : ∀ z ∈ p.roots, z ∈ S) : ∀ z ∈ p.derivative.roots, z ∈ S := by
  intro z hz
  by_cases hdegree : p.natDegree = 0
  · simp only [derivative_of_natDegree_zero hdegree, roots_zero, Multiset.notMem_zero] at hz
  · have hpos : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
    have hzset : z ∈ p.derivative.rootSet ℂ := by
      rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
      exact Polynomial.mem_roots'.mp hz
    have hsub : p.rootSet ℂ ⊆ S := by
      intro w hw
      rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
      exact hp w (Polynomial.mem_roots'.mpr hw)
    exact (convexHull_min hsub hS)
      (Polynomial.rootSet_derivative_subset_convexHull_rootSet hpos hzset)

/-- Positive Euler steps preserve any convex root region containing the origin. -/
theorem eulerStep_roots_mem_convex {S : Set ℂ} (hS : Convex ℝ S) (hzero : 0 ∈ S)
    {p : ℂ[X]} (hpzero : p.eval 0 ≠ 0) (hp : ∀ z ∈ p.roots, z ∈ S)
    {a : ℝ} (ha : 0 < a) :
    ∀ z ∈ (C (a : ℂ) * p + X * p.derivative).roots, z ∈ S := by
  classical
  have hpne : p ≠ 0 := by intro h; simp [h] at hpzero
  intro z hz
  have heq := (Polynomial.mem_roots'.mp hz).2
  rw [IsRoot.def, eval_add, eval_mul, eval_mul, eval_C, eval_X] at heq
  by_cases hpz : p.eval z = 0
  · exact hp z ((mem_roots hpne).mpr hpz)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_mul, add_zero] at heq
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hpzero heq
  have hlog : ∑ w ∈ p.roots.toFinset,
      (p.rootMultiplicity w : ℂ) / (z - w) = p.derivative.eval z / p.eval z := by
    rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
    calc
      _ = ∑ w ∈ p.roots.toFinset, p.rootMultiplicity w • (1 / (z - w)) := by
        simp [nsmul_eq_mul, div_eq_mul_inv]
      _ = (p.roots.map (fun w => 1 / (z - w))).sum := by
        simp only [Finset.sum_multiset_map_count, p.count_roots]
  let poles := insert (none : Option ℂ) (p.roots.toFinset.image some)
  let r : Option ℂ → ℂ := fun o => o.getD 0
  let rho : Option ℂ → ℝ := fun o => o.elim a (fun w => p.rootMultiplicity w)
  have hsum (f : Option ℂ → ℂ) :
      ∑ o ∈ poles, f o = f none + ∑ w ∈ p.roots.toFinset, f (some w) := by
    simp [poles, Finset.sum_image]
  have hnn : ∀ o ∈ poles, 0 ≤ rho o := by
    intro o _
    cases o with
    | none => exact ha.le
    | some w => exact Nat.cast_nonneg _
  have hpos : 0 < ∑ o ∈ poles, rho o := by
    have hsumR : ∑ o ∈ poles, rho o = a + ∑ w ∈ p.roots.toFinset,
        (p.rootMultiplicity w : ℝ) := by simp [poles, rho, Finset.sum_image]
    rw [hsumR]
    exact add_pos_of_pos_of_nonneg ha (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have havoid : ∀ o ∈ poles, z ≠ r o := by
    intro o ho
    cases o with
    | none => exact hz0
    | some w =>
        have hw : w ∈ p.roots := by simpa [poles] using ho
        intro heq
        change z = w at heq
        apply hpz
        rw [heq]
        exact (mem_roots hpne).mp hw
  have hrecip : ∑ o ∈ poles, (rho o : ℂ) / (z - r o) = 0 := by
    rw [hsum]
    dsimp [r, rho]
    rw [sub_zero, hlog]
    field_simp
    simpa only [mul_zero] using heq
  have hmem := mem_convexHull_of_sum_div_eq_zero poles r rho z hnn hpos havoid hrecip
  apply (convexHull_min _ hS) hmem
  rintro _ ⟨o, ho, rfl⟩
  cases o with
  | none => exact hzero
  | some w =>
      apply hp w
      simpa [poles] using ho

end RealRooted.TuranHurwitz
