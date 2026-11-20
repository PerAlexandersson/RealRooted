module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# A weighted reciprocal form of Gauss–Lucas

The proof follows Mathlib's explicit barycentric proof of Gauss–Lucas,
replacing integral root multiplicities by arbitrary nonnegative real weights.
This supplies the convexity lemma in Shi, arXiv:2610.35783v2, Section 2.
These sequence-independent lemmas are candidates for a Mathlib convexity module.
-/

public section

open Polynomial
open scoped ComplexConjugate

namespace RealRooted.TuranHurwitz

/-- A zero weighted reciprocal sum is the center of mass with inverse-square weights. -/
theorem eq_centerMass_of_sum_div_eq_zero {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (rho : ι → ℝ) (z : ℂ) (hpos : 0 < ∑ i ∈ s, rho i / ‖z - r i‖ ^ 2)
    (hz : ∀ i ∈ s, z ≠ r i) (heq : ∑ i ∈ s, (rho i : ℂ) / (z - r i) = 0) :
    z = s.centerMass (fun i => rho i / ‖z - r i‖ ^ 2) r := by
  have hsum : ∑ i ∈ s, (rho i / ‖z - r i‖ ^ 2) • (z - r i) = 0 := by
    calc
      _ = conj (∑ i ∈ s, (rho i : ℂ) / (z - r i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : z - r i ≠ 0 := sub_ne_zero.mpr (hz i hi)
        simp [← Complex.conj_mul', field]
      _ = 0 := by rw [heq, map_zero]
  calc
    z = s.centerMass (fun i => rho i / ‖z - r i‖ ^ 2) (fun _ => z) := by
      rw [Finset.centerMass, ← Finset.sum_smul, inv_smul_smul₀ hpos.ne']
    _ = s.centerMass (fun i => rho i / ‖z - r i‖ ^ 2) (fun i => z - r i) +
        s.centerMass (fun i => rho i / ‖z - r i‖ ^ 2) r := by
      simp only [Finset.centerMass, ← smul_add, ← Finset.sum_add_distrib, sub_add_cancel]
    _ = s.centerMass (fun i => rho i / ‖z - r i‖ ^ 2) r := by
      simp only [Finset.centerMass, hsum, smul_zero, zero_add]

/-- A zero nonnegative reciprocal sum lies in the convex hull of its poles. -/
theorem mem_convexHull_of_sum_div_eq_zero {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (rho : ι → ℝ) (z : ℂ) (hnn : ∀ i ∈ s, 0 ≤ rho i)
    (hpos : 0 < ∑ i ∈ s, rho i) (hz : ∀ i ∈ s, z ≠ r i)
    (heq : ∑ i ∈ s, (rho i : ℂ) / (z - r i) = 0) :
    z ∈ convexHull ℝ (r '' (s : Set ι)) := by
  have hw : ∀ i ∈ s, 0 ≤ rho i / ‖z - r i‖ ^ 2 := fun i hi =>
    div_nonneg (hnn i hi) (sq_nonneg _)
  have hp : 0 < ∑ i ∈ s, rho i / ‖z - r i‖ ^ 2 := by
    obtain ⟨i, hi, hri⟩ := (Finset.sum_pos_iff_of_nonneg hnn).mp hpos
    exact Finset.sum_pos' hw ⟨i, hi, div_pos hri (sq_pos_of_ne_zero
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz i hi))))⟩
  rw [eq_centerMass_of_sum_div_eq_zero s r rho z hp hz heq]
  exact s.centerMass_mem_convexHull hw hp fun i hi => ⟨i, hi, rfl⟩

/-- Only poles with strictly positive weight are needed in the convex hull. -/
theorem mem_convexHull_pos_of_sum_div_eq_zero {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (rho : ι → ℝ) (z : ℂ) (hnn : ∀ i ∈ s, 0 ≤ rho i)
    (hpos : 0 < ∑ i ∈ s, rho i) (hz : ∀ i ∈ s, z ≠ r i)
    (heq : ∑ i ∈ s, (rho i : ℂ) / (z - r i) = 0) :
    z ∈ convexHull ℝ (r '' {i | i ∈ s ∧ 0 < rho i}) := by
  classical
  let t := s.filter (fun i => 0 < rho i)
  have hzero (i : ι) (hi : i ∈ s) (hit : i ∉ t) : rho i = 0 := by
    have hnot : ¬0 < rho i := fun hp => hit (Finset.mem_filter.mpr ⟨hi, hp⟩)
    linarith [hnn i hi]
  have hsum : ∑ i ∈ t, rho i = ∑ i ∈ s, rho i :=
    Finset.sum_subset (Finset.filter_subset _ _) fun i hi hit => hzero i hi hit
  have hdiv : ∑ i ∈ t, (rho i : ℂ) / (z - r i) = 0 := by
    rw [← heq]
    exact Finset.sum_subset (Finset.filter_subset _ _) fun i hi hit => by
      simp [hzero i hi hit]
  simpa only [t, Finset.coe_filter, Set.mem_ofPred_eq] using
    mem_convexHull_of_sum_div_eq_zero t r rho z
    (fun i hi => hnn i (Finset.mem_filter.mp hi).1) (hsum.symm ▸ hpos)
    (fun i hi => hz i (Finset.mem_filter.mp hi).1) hdiv

/-- A positive reciprocal sum with all poles in the closed unit disk is nonzero outside it. -/
theorem sum_div_ne_zero_of_one_lt_norm {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (rho : ι → ℝ) (z : ℂ) (hnn : ∀ i ∈ s, 0 ≤ rho i)
    (hpos : 0 < ∑ i ∈ s, rho i) (hr : ∀ i ∈ s, ‖r i‖ ≤ 1) (hz : 1 < ‖z‖) :
    ∑ i ∈ s, (rho i : ℂ) / (z - r i) ≠ 0 := by
  have hne : ∀ i ∈ s, z ≠ r i := by
    intro i hi heq
    rw [heq] at hz
    linarith [hr i hi]
  intro heq
  have hm := mem_convexHull_of_sum_div_eq_zero s r rho z hnn hpos hne heq
  have hsub : convexHull ℝ (r '' (s : Set ι)) ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i, hi, rfl⟩
    simpa using hr i hi
  have hnorm : ‖z‖ ≤ 1 := by simpa using hsub hm
  linarith

/-- The disk step used in the coefficient lemma cannot create an exterior zero. -/
theorem eval_diskStep_ne_zero {p : ℂ[X]} (hp : p ≠ 0)
    (hr : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha : 0 < a) {eta : ℂ} (heta : ‖eta‖ ≤ 1)
    {z : ℂ} (hz : 1 < ‖z‖) :
    (Polynomial.C (a : ℂ) * p + (Polynomial.X - Polynomial.C eta) * p.derivative).eval z ≠
      0 := by
  classical
  have hpz : p.eval z ≠ 0 := fun heq =>
    (not_le_of_gt hz) (hr z ((Polynomial.mem_roots hp).mpr heq))
  have hze : z - eta ≠ 0 := by
    intro heq
    have hnorm := congrArg norm (sub_eq_zero.mp heq)
    linarith
  have hlog : ∑ w ∈ p.roots.toFinset,
      (p.rootMultiplicity w : ℂ) / (z - w) = p.derivative.eval z / p.eval z := by
    rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
    calc
      _ = ∑ w ∈ p.roots.toFinset, p.rootMultiplicity w • (1 / (z - w)) := by
        simp [nsmul_eq_mul, div_eq_mul_inv]
      _ = (p.roots.map (fun w => 1 / (z - w))).sum := by
        simp only [Finset.sum_multiset_map_count, p.count_roots]
  let s := insert (none : Option ℂ) (p.roots.toFinset.image some)
  let r : Option ℂ → ℂ := fun o => o.getD eta
  let rho : Option ℂ → ℝ := fun o => o.elim a (fun w => p.rootMultiplicity w)
  have hsum (f : Option ℂ → ℂ) :
      ∑ o ∈ s, f o = f none + ∑ w ∈ p.roots.toFinset, f (some w) := by
    simp [s, Finset.sum_image]
  have hnn : ∀ o ∈ s, 0 ≤ rho o := by
    intro o _
    cases o with
    | none => exact ha.le
    | some w => exact Nat.cast_nonneg _
  have hpos : 0 < ∑ o ∈ s, rho o := by
    have hsumR : ∑ o ∈ s, rho o = a + ∑ w ∈ p.roots.toFinset,
        (p.rootMultiplicity w : ℝ) := by simp [s, rho, Finset.sum_image]
    rw [hsumR]
    exact add_pos_of_pos_of_nonneg ha (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hbound : ∀ o ∈ s, ‖r o‖ ≤ 1 := by
    intro o ho
    rcases o with _ | w
    · exact heta
    · have hw : w ∈ p.roots := by simpa [s] using ho
      exact hr w hw
  have hnonzero := sum_div_ne_zero_of_one_lt_norm s r rho z hnn hpos hbound hz
  intro heq
  apply hnonzero
  rw [hsum]
  change (a : ℂ) / (z - eta) +
    (∑ w ∈ p.roots.toFinset, (p.rootMultiplicity w : ℂ) / (z - w)) = 0
  rw [hlog]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X] at heq
  field_simp
  linear_combination heq

end RealRooted.TuranHurwitz
