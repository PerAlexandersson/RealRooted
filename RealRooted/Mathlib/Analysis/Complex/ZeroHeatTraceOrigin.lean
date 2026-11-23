/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import RealRooted.Mathlib.Analysis.Complex.ZeroSpectralIndex
public import TauCeti.Analysis.Complex.GrowthOrder
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.Meromorphic.Divisor
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Native heat traces after inserting origin zeros

The divisor of `z^r g(z)` is the divisor of `g` plus multiplicity `r`
at zero. At positive time, the intrinsic modulus-zero trace therefore
gains the constant `r`. Summability is proved before splitting the
series; no identity is asserted for totalized divergent sums at time zero.
-/

public section

namespace Complex

/-- The native heat trace may also be summed over the whole plane,
because its summand vanishes off the divisor support. -/
theorem zeroHeatTrace_eq_tsum (f : ℂ → ℂ) (t : ℝ) :
    zeroHeatTrace f t = ∑' z : ℂ,
      (MeromorphicOn.divisor f Set.univ z : ℝ) * Real.exp (-‖z‖ * t) := by
  apply tsum_subtype_eq_of_support_subset
    (f := fun z : ℂ ↦ (MeromorphicOn.divisor f Set.univ z : ℝ) *
      Real.exp (-‖z‖ * t)) (s := (MeromorphicOn.divisor f Set.univ).support)
  intro z hz
  by_contra hn
  have hd : MeromorphicOn.divisor f Set.univ z = 0 := Function.notMem_support.mp hn
  exact hz (by simp only [hd, Int.cast_zero, zero_mul])

/-- Finite order makes the native weighted heat summand summable at
every positive time, without any real-zero assumption. -/
theorem summable_zeroHeatTrace_summand {g : ℂ → ℂ} {rho t : ℝ}
    (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0) (horder : TauCeti.OrderLE g rho)
    (ht : 0 < t) :
    Summable (fun z : ℂ ↦
      (MeromorphicOn.divisor g Set.univ z : ℝ) * Real.exp (-‖z‖ * t)) := by
  let p : ℝ := max rho 0 + 1
  have hp : rho < p := by dsimp [p]; linarith [le_max_left rho 0]
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [le_max_right rho 0]
  have hsub := (hasSum_zeroHeatTrace_summand_on_support hg h0 horder hp hp0 ht).summable
  have hsupport : Function.support (fun z : ℂ ↦
      (MeromorphicOn.divisor g Set.univ z : ℝ) * Real.exp (-‖z‖ * t)) ⊆
        (MeromorphicOn.divisor g Set.univ).support := by
    intro z hz
    by_contra hn
    have hd : MeromorphicOn.divisor g Set.univ z = 0 := Function.notMem_support.mp hn
    exact hz (by simp only [hd, Int.cast_zero, zero_mul])
  exact ((hasSum_subtype_iff_of_support_subset hsupport).mp hsub.hasSum).summable

/-- Inserting `z^r` adds exactly its origin multiplicity to the native divisor. -/
theorem divisor_pow_mul_apply {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0)
    (r : ℕ) (z : ℂ) :
    MeromorphicOn.divisor (fun w : ℂ ↦ w ^ r * g w) Set.univ z =
      (if z = 0 then (r : ℤ) else 0) + MeromorphicOn.divisor g Set.univ z := by
  classical
  have hid : AnalyticOnNhd ℂ (id : ℂ → ℂ) Set.univ := fun _ _ ↦ analyticAt_id
  have hga : AnalyticOnNhd ℂ g Set.univ := fun w _ ↦ hg.analyticAt w
  have hp : AnalyticOnNhd ℂ (fun w : ℂ ↦ w ^ r) Set.univ := hid.pow r
  have htopg (w : ℂ) (hw : w ∈ Set.univ) : meromorphicOrderAt g w ≠ ⊤ :=
    hga.meromorphicOrderAt_ne_top_of_exists_ne_zero isConnected_univ
      (show ∃ v ∈ Set.univ, g v ≠ 0 from ⟨0, Set.mem_univ _, h0⟩) hw
  have htopp (w : ℂ) (hw : w ∈ Set.univ) :
      meromorphicOrderAt (fun v : ℂ ↦ v ^ r) w ≠ ⊤ :=
    hp.meromorphicOrderAt_ne_top_of_exists_ne_zero isConnected_univ
      (show ∃ v ∈ Set.univ, v ^ r ≠ (0 : ℂ) from ⟨1, Set.mem_univ _, by simp⟩) hw
  rw [MeromorphicOn.divisor_fun_mul hp.meromorphicOn hga.meromorphicOn
    htopp htopg]
  change MeromorphicOn.divisor (fun w : ℂ ↦ w ^ r) Set.univ z + _ = _
  congr 1
  have hidz : MeromorphicOn.divisor (id : ℂ → ℂ) Set.univ z =
      if z = 0 then 1 else 0 := by
    by_cases hz : z = 0
    · subst z
      rw [hid.meromorphicOn.divisor_eq_analyticOrderNatAt analyticAt_id (Set.mem_univ _)]
      simp only [analyticOrderNatAt, analyticOrderAt_id, ENat.toNat_one, Nat.cast_one, ite_true]
    · simpa only [hz, ite_false] using analyticAt_id.divisor_apply_eq_zero hz
  rw [show (fun w : ℂ ↦ w ^ r) = fun w ↦ id w ^ r from rfl,
    MeromorphicOn.divisor_fun_pow hid.meromorphicOn]
  change r • MeromorphicOn.divisor (id : ℂ → ℂ) Set.univ z = _
  rw [hidz]
  split_ifs <;> simp

/-- The actual native trace gains the origin multiplicity as a constant
at every positive time. -/
theorem zeroHeatTrace_pow_mul {g : ℂ → ℂ} {rho t : ℝ}
    (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0) (horder : TauCeti.OrderLE g rho)
    (r : ℕ) (ht : 0 < t) :
    zeroHeatTrace (fun z : ℂ ↦ z ^ r * g z) t = (r : ℝ) + zeroHeatTrace g t := by
  classical
  have hdelta : Summable (fun z : ℂ ↦ if z = 0 then (r : ℝ) else 0) :=
    (hasSum_ite_eq 0 (r : ℝ)).summable
  have hgheat := summable_zeroHeatTrace_summand hg h0 horder ht
  rw [zeroHeatTrace_eq_tsum, zeroHeatTrace_eq_tsum]
  have heq : (fun z : ℂ ↦
      (MeromorphicOn.divisor (fun w : ℂ ↦ w ^ r * g w) Set.univ z : ℝ) *
        Real.exp (-‖z‖ * t)) =
      (fun z : ℂ ↦ if z = 0 then (r : ℝ) else 0) +
        (fun z : ℂ ↦ (MeromorphicOn.divisor g Set.univ z : ℝ) *
          Real.exp (-‖z‖ * t)) := by
    funext z
    rw [divisor_pow_mul_apply hg h0 r]
    by_cases hz : z = 0 <;> simp [hz]
  rw [heq, Pi.add_def, hdelta.tsum_add hgheat]
  simp

end Complex
