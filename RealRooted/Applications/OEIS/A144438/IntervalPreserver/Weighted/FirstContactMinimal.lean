import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.FirstContactTopology

/-!
# Consequences of minimal bad-contact time

At an earliest bad expanding box, the time is positive, every root residue
sign throughout that box is nonnegative, and the selected bad sign vanishes.
-/

open Polynomial Set

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Positivity at the diagonal rules out bad contact at expansion time zero. -/
theorem weightedDeco_minimal_badContact_time_pos
    {w : ℝ} {n : ℕ} {z : ℝ × ((Fin n → ℝ) × ℝ)}
    (hz : z ∈ weightedDecoBadContactSet w n)
    (hdiag : ∀ r,
      (weightedDecoParameterImage w Finset.univ
        (fun _ : Fin n => (1 / 2 : ℝ))).IsRoot r →
        0 < weightedDecoResidueSign w n
          (fun _ : Fin n => (1 / 2 : ℝ)) r) :
    0 < z.1 := by
  rcases hz with ⟨ht, hbox, hroot, hsign⟩
  rcases ht.1.eq_or_lt with ht0 | ht0
  · have ha : z.2.1 = fun _ : Fin n => (1 / 2 : ℝ) := by
      funext i
      have hi := hbox i
      rw [← ht0] at hi
      norm_num at hi ⊢
      linarith
    rw [ha] at hroot hsign
    exfalso
    exact (not_lt_of_ge hsign) (hdiag z.2.2 hroot)
  · exact ht0

/-- At an earliest bad time, no root over any parameter vector in the current
box can have strictly negative residue sign. -/
theorem weightedDeco_residueSign_nonneg_in_minimal_box
    {w : ℝ} {n : ℕ} (hn : n ≠ 0)
    {z : ℝ × ((Fin n → ℝ) × ℝ)}
    (hz : z ∈ weightedDecoBadContactSet w n)
    (hzmin : ∀ y ∈ weightedDecoBadContactSet w n, z.1 ≤ y.1)
    (htpos : 0 < z.1)
    (hsplits : ∀ b ∈ weightedDecoParameterCube n,
      (weightedDecoParameterImage w Finset.univ b).Splits)
    {b : Fin n → ℝ} (hbox : weightedDecoExpandingBox z.1 b)
    {r : ℝ} (hr : (weightedDecoParameterImage w Finset.univ b).IsRoot r) :
    0 ≤ weightedDecoResidueSign w n b r := by
  rcases hz with ⟨ht, hzbox, hzroot, hzsign⟩
  by_contra hnot
  have hneg : weightedDecoResidueSign w n b r < 0 := lt_of_not_ge hnot
  have hevent := eventually_exists_weightedDeco_root_residueSign_neg hn hr hneg hsplits
  obtain ⟨t', c, ht'0, ht'lt, hcbox, hcCube, s, hsroot, hsneg⟩ :=
    exists_in_smaller_weightedDecoExpandingBox_of_eventually htpos ht.2 hbox hevent
  have ht'1 : t' ≤ 1 := (le_of_lt ht'lt).trans ht.2
  have hy : (t', (c, s)) ∈ weightedDecoBadContactSet w n :=
    ⟨⟨ht'0, ht'1⟩, hcbox, hsroot, hsneg.le⟩
  have hminimal := hzmin (t', (c, s)) hy
  linarith

/-- The selected residue sign at an earliest bad contact is exactly zero. -/
theorem weightedDeco_minimal_badContact_residueSign_eq_zero
    {w : ℝ} {n : ℕ} (hn : n ≠ 0)
    {z : ℝ × ((Fin n → ℝ) × ℝ)}
    (hz : z ∈ weightedDecoBadContactSet w n)
    (hzmin : ∀ y ∈ weightedDecoBadContactSet w n, z.1 ≤ y.1)
    (htpos : 0 < z.1)
    (hsplits : ∀ b ∈ weightedDecoParameterCube n,
      (weightedDecoParameterImage w Finset.univ b).Splits) :
    weightedDecoResidueSign w n z.2.1 z.2.2 = 0 := by
  rcases hz with ⟨ht, hbox, hroot, hsign⟩
  apply le_antisymm hsign
  exact weightedDeco_residueSign_nonneg_in_minimal_box hn
    ⟨ht, hbox, hroot, hsign⟩ hzmin htpos hsplits hbox hroot

end RealRooted.Applications.OEIS
