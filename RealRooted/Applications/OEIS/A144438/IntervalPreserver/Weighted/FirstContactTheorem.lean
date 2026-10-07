import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.FirstContactBoundary

/-!
# Weighted first-contact theorem

Assuming the rank-`n` transformed family already has simple negative roots
and the deletion-to-full residues are positive, every companion residue is
positive throughout the parameter cube.
-/

open Polynomial Set

noncomputable section

namespace RealRooted.Applications.OEIS

private theorem mul_pos_of_div_pos {H d : ℝ} (hd : d ≠ 0) (h : 0 < H / d) :
    0 < H * d := by
  rw [show H * d = (H / d) * d ^ 2 by field_simp [hd]]
  exact mul_pos h (sq_pos_of_ne_zero hd)

theorem weightedDecoResidueSign_const_pos
    {w c : ℝ} {n : ℕ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hn : 1 ≤ n) {r : ℝ}
    (hr : (weightedDecoParameterImage w Finset.univ
      (fun _ : Fin n => c)).IsRoot r) :
    0 < weightedDecoResidueSign w n (fun _ : Fin n => c) r := by
  have hinv := weightedDecoDiagonalInvariant_all hw0 hw1 hc0 hc1 n hn
  have hrdiag : (weightedDecoDiagonal w n c).IsRoot r := by
    simpa only [weightedDecoParameterImage_const_univ] using hr
  have hd : (weightedDecoDiagonal w n c).derivative.eval r ≠ 0 :=
    hinv.simple.eval_derivative_ne_zero hrdiag
  have hres := hinv.companion_residue_pos r hrdiag
  unfold weightedDecoResidueSign
  simp only [weightedDecoParameterCompanion_const_univ,
    weightedDecoParameterImage_const_univ]
  exact mul_pos_of_div_pos hd hres

/-- The unequal-parameter first-contact argument: positive deletion-to-full
residues force positive companion residues on the whole cube. -/
theorem weightedDecoParameterCompanion_residue_pos_of_deletion
    {w : ℝ} {n : ℕ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hn : 1 ≤ n)
    (hsplits : ∀ a ∈ weightedDecoParameterCube n,
      (weightedDecoParameterImage w Finset.univ a).Splits)
    (hsimple : ∀ a ∈ weightedDecoParameterCube n,
      HasSimpleRoots (weightedDecoParameterImage w Finset.univ a))
    (hrootsNeg : ∀ a ∈ weightedDecoParameterCube n, ∀ r,
      (weightedDecoParameterImage w Finset.univ a).IsRoot r → r < 0)
    (halpha : ∀ a ∈ weightedDecoParameterCube n, ∀ r,
      (weightedDecoParameterImage w Finset.univ a).IsRoot r → ∀ j : Fin n,
        0 < (weightedDecoParameterImage w (Finset.univ.erase j) a).eval r /
          (weightedDecoParameterImage w Finset.univ a).derivative.eval r) :
    ∀ a ∈ weightedDecoParameterCube n, ∀ r,
      (weightedDecoParameterImage w Finset.univ a).IsRoot r →
        0 < (weightedDecoParameterCompanion w Finset.univ a).eval r /
          (weightedDecoParameterImage w Finset.univ a).derivative.eval r := by
  have hn0 : n ≠ 0 := by lia
  intro a haCube r hr
  by_contra hnot
  have hquotient :
      (weightedDecoParameterCompanion w Finset.univ a).eval r /
          (weightedDecoParameterImage w Finset.univ a).derivative.eval r ≤ 0 :=
    le_of_not_gt hnot
  have hd : (weightedDecoParameterImage w Finset.univ a).derivative.eval r ≠ 0 :=
    (hsimple a haCube).eval_derivative_ne_zero hr
  have hsign : weightedDecoResidueSign w n a r ≤ 0 := by
    unfold weightedDecoResidueSign
    rw [show
        (weightedDecoParameterCompanion w Finset.univ a).eval r *
            (weightedDecoParameterImage w Finset.univ a).derivative.eval r =
          ((weightedDecoParameterCompanion w Finset.univ a).eval r /
              (weightedDecoParameterImage w Finset.univ a).derivative.eval r) *
            ((weightedDecoParameterImage w Finset.univ a).derivative.eval r) ^ 2 by
      field_simp [hd]]
    exact mul_nonpos_of_nonpos_of_nonneg hquotient (sq_nonneg _)
  have hboxOne : weightedDecoExpandingBox 1 a := by
    intro i
    have hai := haCube i (Set.mem_univ i)
    norm_num at hai ⊢
    exact hai
  have hbadNonempty : (weightedDecoBadContactSet w n).Nonempty :=
    ⟨(1, (a, r)), ⟨by norm_num, hboxOne, hr, hsign⟩⟩
  obtain ⟨z, hz, hzmin⟩ :=
    exists_minimal_weightedDecoBadContact w n hn0 hbadNonempty
  have hdiag : ∀ s,
      (weightedDecoParameterImage w Finset.univ
        (fun _ : Fin n => (1 / 2 : ℝ))).IsRoot s →
        0 < weightedDecoResidueSign w n (fun _ : Fin n => (1 / 2 : ℝ)) s := by
    intro s hs
    exact weightedDecoResidueSign_const_pos hw0 hw1 (by norm_num) (by norm_num) hn hs
  have htpos : 0 < z.1 := weightedDeco_minimal_badContact_time_pos hz hdiag
  rcases hz with ⟨ht, hbox, hzroot, hzsign⟩
  have hzCube : z.2.1 ∈ weightedDecoParameterCube n :=
    weightedDecoParameterCube_of_expandingBox ht hbox
  have hcoords : ∀ i j, z.2.1 i = z.2.1 j :=
    weightedDeco_minimal_badContact_coordinates_eq hn0
      ⟨ht, hbox, hzroot, hzsign⟩ hzmin htpos hsplits hsimple hrootsNeg
      (halpha z.2.1 hzCube z.2.2 hzroot)
  let i0 : Fin n := ⟨0, by lia⟩
  let c := z.2.1 i0
  have haConst : z.2.1 = fun _ : Fin n => c := by
    funext i
    exact hcoords i i0
  have hc : c ∈ Icc (0 : ℝ) 1 :=
    hzCube i0 (Set.mem_univ i0)
  have hsignZero : weightedDecoResidueSign w n z.2.1 z.2.2 = 0 :=
    weightedDeco_minimal_badContact_residueSign_eq_zero hn0
      ⟨ht, hbox, hzroot, hzsign⟩ hzmin htpos hsplits
  have hdiagPos : 0 < weightedDecoResidueSign w n z.2.1 z.2.2 := by
    rw [haConst] at hzroot ⊢
    exact weightedDecoResidueSign_const_pos hw0 hw1 hc.1 hc.2 hn hzroot
  linarith

end RealRooted.Applications.OEIS
