/-
Copyright (c) 2026 The Tau Ceti contributors, Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Per Alexandersson
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Montel selection on a smaller disc

We extract a locally uniformly convergent subsequence from a uniformly bounded holomorphic
sequence on a disc. The limit is holomorphic on the concentric disc of half the radius.

Adapted from Tau Ceti `Analysis/Complex/Conformal/NormalFamilies.lean` and
`Analysis/Complex/Conformal/Montel/Basic.lean` (Apache-2.0). We specialize the Cauchy estimate
and the selection argument to scalar functions on one compact disc, using Mathlib's
Arzelà–Ascoli theorem for bounded continuous maps. No exhaustion or compact-open adapter is
needed. This is the bounded-disc form of Montel's theorem used in Sokal,
*Chromatic roots are dense in the whole complex plane*, Theorem 1.5(b).
-/

public section

open Filter Topology Metric Set

namespace Complex

/-- Cauchy's estimate gives a common Lipschitz bound on a smaller closed disc. -/
private theorem lipschitzOnWith_closedBall_of_norm_le {F : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball c (2 * r)))
    (hM : ∀ z ∈ ball c (2 * r), ‖F z‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (M / (r / 2))) F (closedBall c r) := by
  have hsub : closedBall c r ⊆ ball c (2 * r) := by
    exact closedBall_subset_ball (by linarith)
  have hd : ∀ z ∈ closedBall c r, ‖deriv F z‖ ≤ M / (r / 2) := by
    intro z hz
    have hzc : closedBall z (r / 2) ⊆ ball c (2 * r) := by
      intro w hw
      have h₁ := mem_closedBall.mp hz
      have h₂ := mem_closedBall.mp hw
      rw [mem_ball]
      linarith [dist_triangle w z c]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hF.diffContOnCl_ball hzc) fun w hw => hM w (hzc (sphere_subset_closedBall hw))
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  rw [dist_eq_norm, dist_eq_norm]
  exact ((convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hF x (hsub hx)).differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
    hd hw hz).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))

/-- A uniformly bounded holomorphic sequence on `ball c (2 * r)` has a subsequence converging
locally uniformly on `ball c r` to a holomorphic function. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_ball {F : ℕ → ℂ → ℂ} {c : ℂ}
    {r M : ℝ} (hr : 0 < r) (hF : ∀ n, DifferentiableOn ℂ (F n) (ball c (2 * r)))
    (hM : ∀ n z, z ∈ ball c (2 * r) → ‖F n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧ DifferentiableOn ℂ g (ball c r) ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop (ball c r) := by
  classical
  let K := closedBall c r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hsub : K ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  let f : ℕ → BoundedContinuousFunction K ℂ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun z => F n z, ((hF n).continuousOn.mono hsub).domRestrict⟩
  have hlip : ∀ n, LipschitzWith (Real.toNNReal (M / (r / 2))) (f n) := by
    intro n
    exact LipschitzWith.of_dist_le_mul fun z w =>
      (lipschitzOnWith_closedBall_of_norm_le hr (hF n) (hM n)).dist_le_mul z z.2 w w.2
  have heq : Equicontinuous (fun n => ⇑(f n)) :=
    Metric.equicontinuous_of_continuity_modulus
      (fun x : ℝ => (Real.toNNReal (M / (r / 2)) : ℝ) * x)
      (by
        have hc : Continuous (fun x : ℝ => (Real.toNNReal (M / (r / 2)) : ℝ) * x) :=
          continuous_const.mul continuous_id
        simpa only [mul_zero] using hc.tendsto (0 : ℝ))
      _ (fun z w n => (hlip n).dist_le_mul z w)
  have hcpt : IsCompact (closure (range f)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall 0 M) (isCompact_closedBall _ _)
      (range f) (by
        rintro _ z ⟨n, rfl⟩
        exact mem_closedBall_zero_iff.mpr (hM n z (hsub z.2)))
      ((equicontinuous_iff_range.mp heq).comp fun a : range f =>
        (⟨⇑(a : BoundedContinuousFunction K ℂ), by
          obtain ⟨n, hn⟩ := a.2
          exact ⟨n, congrArg DFunLike.coe hn⟩⟩ : range fun n => ⇑(f n)))
  obtain ⟨a, -, φ, hφ, ha⟩ := hcpt.tendsto_subseq (x := f) fun n =>
    subset_closure (mem_range_self n)
  let g : ℂ → ℂ := fun z => if hz : z ∈ K then a ⟨z, hz⟩ else 0
  have hconv : TendstoUniformlyOn (fun n => F (φ n)) g atTop K := by
    have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ha
    rw [Metric.tendstoUniformly_iff] at hu
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hu ε hε] with n hn z hz
    specialize hn ⟨z, hz⟩
    change dist (a ⟨z, hz⟩) (F (φ n) z) < ε at hn
    simpa only [g, dite_eq_left hz] using hn
  have hlocal := (hconv.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  exact ⟨φ, g, hφ, hlocal.differentiableOn
    (Eventually.of_forall fun n => (hF (φ n)).mono (ball_subset_ball (by linarith)))
    isOpen_ball, hlocal⟩

end Complex
