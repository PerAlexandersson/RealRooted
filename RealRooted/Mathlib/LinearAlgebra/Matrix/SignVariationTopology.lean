import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation

/-!
# Topological properties of sign variations

This file proves the finite-dimensional lower semicontinuity of sign variations.
The result supplies the limit step in Karlin's Gaussian approximation argument
for variation-diminishing matrices.
-/

open Filter Topology

namespace Fin

/-- Sign variations cannot increase when a convergent net reaches its limit. -/
theorem signVariations_le_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot] {n r : ℕ}
    {f : α → Fin n → ℝ} {x : Fin n → ℝ}
    (hf : Tendsto f l (𝓝 x))
    (hr : ∀ᶠ a in l, signVariations (f a) ≤ r) :
    signVariations x ≤ r := by
  let raw : List SignType := List.ofFn (SignType.sign ∘ x)
  let nz : List SignType := raw.filter (· ≠ 0)
  let d : List SignType := nz.destutter (· ≠ ·)
  have hsub : d.Sublist raw :=
    (List.destutter_sublist (· ≠ ·) nz).trans List.filter_sublist
  obtain ⟨e, he⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  have hrawlen : raw.length = n := by
    simp [raw]
  let eN : Fin d.length ↪o Fin n :=
    e.trans (Fin.castOrderIso hrawlen).toOrderEmbedding
  have he' (k : Fin d.length) :
      d.get k = SignType.sign (x (eN k)) := by
    rw [he k]
    simp only [raw, List.get_ofFn, Function.comp_apply]
    congr 2
  have hd_ne (z : SignType) (hz : z ∈ d) : z ≠ 0 := by
    have hz_nz : z ∈ nz :=
      (List.destutter_sublist (· ≠ ·) nz).mem hz
    exact of_decide_eq_true (List.mem_filter.mp hz_nz).2
  have hd_filter : d.filter (· ≠ 0) = d := by
    rw [List.filter_eq_self]
    intro z hz
    simp [hd_ne z hz]
  have hsign :
      ∀ k : Fin d.length,
        ∀ᶠ a in l, d.get k = SignType.sign (f a (eN k)) := by
    intro k
    have hk := tendsto_pi_nhds.mp hf (eN k)
    have hxne : x (eN k) ≠ 0 := by
      rw [← sign_ne_zero, ← he' k]
      exact hd_ne _ (List.get_mem d k)
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · filter_upwards [hk.eventually_lt_const hxneg] with a ha
      rw [he' k, sign_neg hxneg, sign_neg ha]
    · filter_upwards [hk.eventually_const_lt hxpos] with a ha
      rw [he' k, sign_pos hxpos, sign_pos ha]
  have hmono :
      ∀ᶠ a in l, signVariations x ≤ signVariations (f a) := by
    filter_upwards [Filter.eventually_all.mpr hsign] with a ha
    let rawA : List SignType := List.ofFn (SignType.sign ∘ f a)
    have hrawAlen : rawA.length = n := by
      simp [rawA]
    let eA : Fin d.length ↪o Fin rawA.length :=
      eN.trans (Fin.castOrderIso hrawAlen.symm).toOrderEmbedding
    have hdsub : d.Sublist rawA := by
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨eA, ?_⟩
      intro k
      rw [ha k]
      simp only [rawA, List.get_ofFn, Function.comp_apply]
      congr 2
    have hdsub_nz : d.Sublist (rawA.filter (· ≠ 0)) := by
      have h := hdsub.filter (· ≠ 0)
      rw [hd_filter] at h
      exact h
    have hlen :=
      (List.isChain_destutter (· ≠ ·) nz).length_le_length_destutter_ne hdsub_nz
    simpa only [signVariations, List.signVariations, List.map_ofFn, d, nz, raw,
      rawA] using Nat.sub_le_sub_right hlen 1
  obtain ⟨a, hxa, har⟩ := (hmono.and hr).exists
  exact hxa.trans har

end Fin
