/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic

/-!
# Zero exclusion for analytic first-order equations

At a zero of finite order, differentiation lowers the order by one, whereas
multiplication by an analytic function cannot lower it. Thus a nonzero analytic
solution of `f' = g f` has no zeros on its connected domain.
-/

public section

open Filter Set Topology

/-- A nonzero analytic germ satisfying a homogeneous first-order differential
equation with analytic coefficient cannot vanish at its center. -/
theorem AnalyticAt.ne_zero_of_eventually_deriv_eq_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hfinite : analyticOrderAt f z ≠ ⊤)
    (hode : deriv f =ᶠ[𝓝 z] fun w ↦ g w * f w) : f z ≠ 0 := by
  intro hz
  have hderiv : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa only [hz, sub_zero] using hf.analyticOrderAt_deriv_add_one
  have hmul : analyticOrderAt (deriv f) z =
      analyticOrderAt g z + analyticOrderAt f z := by
    rw [analyticOrderAt_congr hode]
    exact analyticOrderAt_fun_mul hg hf
  have hle : analyticOrderAt f z ≤ analyticOrderAt (deriv f) z := by
    calc
      _ = 0 + analyticOrderAt f z := (zero_add _).symm
      _ ≤ analyticOrderAt g z + analyticOrderAt f z :=
        add_le_add (zero_le : 0 ≤ analyticOrderAt g z) le_rfl
      _ = _ := hmul.symm
  have hbad : analyticOrderAt f z + 1 ≤ analyticOrderAt f z :=
    (add_le_add hle le_rfl).trans_eq hderiv
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hn] at hbad
  have hnat : n + 1 ≤ n := ENat.natCast_le_natCast.mp (by
    simpa only [ENat.natCast_add, Nat.cast_one] using hbad)
  exact Nat.not_succ_le_self n hnat

/-- A solution of `f' = g f` on a connected open domain is nowhere zero if it
is nonzero at one point. All analyticity and domain assumptions are explicit. -/
theorem AnalyticOnNhd.ne_zero_of_deriv_eq_mul {f g : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsOpen U) (hconn : IsPreconnected U) (ha : a ∈ U) (hfa : f a ≠ 0)
    (hode : EqOn (deriv f) (fun z ↦ g z * f z) U) :
    ∀ z ∈ U, f z ≠ 0 := by
  intro z hz
  have hfinite : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected hconn ha hz
      (by simp [analyticOrderAt_eq_zero.mpr (Or.inr hfa)])
  exact (hf z hz).ne_zero_of_eventually_deriv_eq_mul (hg z hz) hfinite
    (Filter.Eventually.mono (hU.mem_nhds hz) fun w hw ↦ hode hw)

end
