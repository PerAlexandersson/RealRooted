module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Collision intervals and a continuous lower-half-plane phase

An excursion between two levels supplies a collision interval directly from a
continuous normalized real part. No classification of the discriminant roots is
needed for this selection. The phase is the negative arccosine of the normalized
real part, so it remains continuous on the closed lower half-plane away from zero.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

open Set

/-- A continuous crossing contains a closed subinterval with prescribed boundary
levels and strictly intermediate values throughout its interior. -/
theorem exists_interval_of_continuousOn_crossing {f : ℝ → ℝ} {A B L U : ℝ}
    (hAB : A ≤ B) (hf : ContinuousOn f (Icc A B)) (hLU : L < U)
    (hA : f A < L) (hB : U < f B) :
    ∃ x y, x < y ∧ Icc x y ⊆ Icc A B ∧ f x = L ∧ f y = U ∧
      ∀ t ∈ Ioo x y, f t ∈ Ioo L U := by
  let upper := Icc A B ∩ f ⁻¹' {U}
  have hupper_closed : IsClosed upper :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hupper_compact : IsCompact upper :=
    isCompact_Icc.of_isClosed_subset hupper_closed inter_subset_left
  have hupper_nonempty : upper.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hAB hf ⟨hA.le.trans hLU.le, hB.le⟩
    exact ⟨t, ht, he⟩
  obtain ⟨y, hy⟩ := hupper_compact.exists_isLeast hupper_nonempty
  have hyAB : y ∈ Icc A B := hy.1.1
  have hfy : f y = U := hy.1.2
  have hbelow {t : ℝ} (ht : t ∈ Icc A B) (hty : t < y) : f t < U := by
    by_contra he
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc ht.1
      (hf.mono (Icc_subset_Icc le_rfl ht.2)) ⟨hA.le.trans hLU.le, le_of_not_gt he⟩
    have hyz := hy.2 (show z ∈ upper from ⟨⟨hz.1, hz.2.trans ht.2⟩, hfz⟩)
    linarith [hz.2]
  let lower := Icc A y ∩ f ⁻¹' {L}
  have hlower_cont : ContinuousOn f (Icc A y) :=
    hf.mono (Icc_subset_Icc le_rfl hyAB.2)
  have hlower_closed : IsClosed lower :=
    hlower_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hlower_compact : IsCompact lower :=
    isCompact_Icc.of_isClosed_subset hlower_closed inter_subset_left
  have hlower_nonempty : lower.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hyAB.1 hlower_cont
      ⟨hA.le, by rw [hfy]; exact hLU.le⟩
    exact ⟨t, ht, he⟩
  obtain ⟨x, hx⟩ := hlower_compact.exists_isGreatest hlower_nonempty
  have hxAy : x ∈ Icc A y := hx.1.1
  have hfx : f x = L := hx.1.2
  have hxy : x < y := hxAy.2.lt_of_ne (by intro he; rw [he, hfy] at hfx; linarith)
  refine ⟨x, y, hxy, Icc_subset_Icc hxAy.1 hyAB.2, hfx, hfy, ?_⟩
  intro t ht
  refine ⟨?_, hbelow ⟨hxAy.1.trans ht.1.le, ht.2.le.trans hyAB.2⟩ ht.2⟩
  by_contra he
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc ht.2.le
    (hlower_cont.mono (Icc_subset_Icc (hxAy.1.trans ht.1.le) le_rfl))
    ⟨le_of_not_gt he, by rw [hfy]; exact hLU.le⟩
  have hzx := hx.2 (show z ∈ lower from
    ⟨⟨(hxAy.1.trans ht.1.le).trans hz.1, hz.2⟩, hfz⟩)
  linarith [hz.1, ht.1]

/-- The continuous phase taking values in the lower semicircle. -/
noncomputable def lowerPhase (z : ℂ) : ℝ := -Real.arccos (z.re / ‖z‖)

/-- The chosen phase always lies between minus pi and zero. -/
theorem lowerPhase_mem (z : ℂ) : lowerPhase z ∈ Icc (-Real.pi) 0 := by
  constructor
  · exact neg_le_neg (Real.arccos_le_pi _)
  · exact neg_nonpos.mpr (Real.arccos_nonneg _)

/-- Nonvanishing makes the lower-semicircle formula continuous on any domain. -/
theorem continuousOn_lowerPhase {s : Set ℝ} {F : ℝ → ℂ} (hF : ContinuousOn F s)
    (hne : ∀ t ∈ s, F t ≠ 0) : ContinuousOn (fun t ↦ lowerPhase (F t)) s := by
  exact (((Complex.continuous_re.comp_continuousOn hF).div hF.norm
    (fun t ht ↦ norm_ne_zero_iff.mpr (hne t ht))).arccos).neg

/-- On the closed lower half-plane, the continuous phase is an exact polar lift. -/
theorem lowerPhase_polar {z : ℂ} (hz : z ≠ 0) (him : z.im ≤ 0) :
    (‖z‖ : ℂ) * Complex.exp ((lowerPhase z : ℂ) * Complex.I) = z := by
  have hstar : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have him' : 0 ≤ (starRingEnd ℂ z).im := by simpa using neg_nonneg.mpr him
  have harg := Complex.arg_of_im_nonneg_of_ne_zero him' hstar
  have h := congrArg (starRingEnd ℂ)
    (Complex.norm_mul_exp_arg_mul_I (starRingEnd ℂ z))
  rw [harg] at h
  simpa [lowerPhase, map_mul, ← Complex.exp_conj, neg_mul] using h

end RealRooted.EffectiveBKW.PathCube
