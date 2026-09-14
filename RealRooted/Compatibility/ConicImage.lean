import RealRooted.Compatibility.Basic

open Polynomial

noncomputable section

namespace RealRooted

namespace FamilyCompatible

/-- A finite family of nonnegative conic recombinations of one compatible
family is itself compatible. Empty blocks and zero weights are allowed. -/
theorem map_weightedSum {fs : List ℝ[X]} (hfs : FamilyCompatible fs)
    (blocks : List (List (ℝ × ℝ[X])))
    (hmem : ∀ block ∈ blocks, ∀ ap ∈ block, ap.2 ∈ fs)
    (hnonneg : ∀ block ∈ blocks, ∀ ap ∈ block, 0 ≤ ap.1) :
    FamilyCompatible (blocks.map weightedSum) := by
  intro l hl houter
  have flatten : ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, ap.2 ∈ blocks.map weightedSum) →
      (∀ ap ∈ l, 0 ≤ ap.1) →
      ∃ flat : List (ℝ × ℝ[X]),
        weightedSum flat = weightedSum l ∧
          (∀ ap ∈ flat, ap.2 ∈ fs) ∧
          (∀ ap ∈ flat, 0 ≤ ap.1) := by
    intro outer
    induction outer with
    | nil =>
        intro _ _
        exact ⟨[], rfl, by simp, by simp⟩
    | cons head tail ih =>
        rcases head with ⟨a, p⟩
        intro hblocks hweights
        have hp : p ∈ blocks.map weightedSum := hblocks (a, p) (by simp)
        rcases List.mem_map.mp hp with ⟨block, hblock, hblockSum⟩
        subst p
        have htailBlocks : ∀ ap ∈ tail, ap.2 ∈ blocks.map weightedSum := by
          intro ap hap
          exact hblocks ap (by simp [hap])
        have htailWeights : ∀ ap ∈ tail, 0 ≤ ap.1 := by
          intro ap hap
          exact hweights ap (by simp [hap])
        obtain ⟨flat, hflat, hflatMem, hflatNonneg⟩ :=
          ih htailBlocks htailWeights
        let scaled := block.map fun ap => (a * ap.1, ap.2)
        refine ⟨scaled ++ flat, ?_, ?_, ?_⟩
        · simp [scaled, weightedSum_map_mul_left, hflat]
        · intro ap hap
          rcases List.mem_append.mp hap with hap | hap
          · rcases List.mem_map.mp hap with ⟨bp, hbp, rfl⟩
            exact hmem block hblock bp hbp
          · exact hflatMem ap hap
        · intro ap hap
          rcases List.mem_append.mp hap with hap | hap
          · rcases List.mem_map.mp hap with ⟨bp, hbp, rfl⟩
            exact mul_nonneg (hweights (a, weightedSum block) (by simp))
              (hnonneg block hblock bp hbp)
          · exact hflatNonneg ap hap
  obtain ⟨flat, hflat, hflatMem, hflatNonneg⟩ := flatten l hl houter
  simpa [hflat] using hfs flat hflatMem hflatNonneg

end FamilyCompatible

end RealRooted
