import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.FirstContactTheorem
import RealRooted.Interlacing.OuterDifference

/-!
# Induction over unequal input-root parameters

We combine the generic insertion root step with the first-contact theorem.
Deleting any coordinate is reindexed by `Fin.succAbove`, so the induction
hypothesis applies to every deletion.
-/

open Polynomial Set

noncomputable section

namespace RealRooted.Applications.OEIS

structure WeightedDecoParameterInvariant (w : ℝ) (n : ℕ) : Prop where
  splits : ∀ a ∈ weightedDecoParameterCube n,
    (weightedDecoParameterImage w Finset.univ a).Splits
  simple : ∀ a ∈ weightedDecoParameterCube n,
    HasSimpleRoots (weightedDecoParameterImage w Finset.univ a)
  roots_neg : ∀ a ∈ weightedDecoParameterCube n, ∀ r,
    (weightedDecoParameterImage w Finset.univ a).IsRoot r → r < 0
  companion_residue_pos : ∀ a ∈ weightedDecoParameterCube n, ∀ r,
    (weightedDecoParameterImage w Finset.univ a).IsRoot r →
      0 < (weightedDecoParameterCompanion w Finset.univ a).eval r /
        (weightedDecoParameterImage w Finset.univ a).derivative.eval r

theorem weightedDecoParameterInvariant_one
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    WeightedDecoParameterInvariant w 1 := by
  have hdiag (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :=
    weightedDecoDiagonalInvariant_all hw0 hw1 hc0 hc1 1 (by norm_num)
  have hconst (a : Fin 1 → ℝ) : a = fun _ => a 0 := by
    funext i
    exact congrArg a (Fin.eq_zero i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hc := ha 0 (Set.mem_univ 0)
    rw [hconst a, weightedDecoParameterImage_const_univ]
    exact (hdiag (a 0) hc.1 hc.2).splits
  · intro a ha
    have hc := ha 0 (Set.mem_univ 0)
    rw [hconst a, weightedDecoParameterImage_const_univ]
    exact (hdiag (a 0) hc.1 hc.2).simple
  · intro a ha r hr
    have hc := ha 0 (Set.mem_univ 0)
    rw [hconst a, weightedDecoParameterImage_const_univ] at hr
    exact (hdiag (a 0) hc.1 hc.2).roots_neg r hr
  · intro a ha r hr
    have hc := ha 0 (Set.mem_univ 0)
    rw [hconst a] at hr ⊢
    rw [weightedDecoParameterImage_const_univ] at hr ⊢
    rw [weightedDecoParameterCompanion_const_univ]
    exact (hdiag (a 0) hc.1 hc.2).companion_residue_pos r hr

theorem WeightedDecoParameterInvariant.succ
    {w : ℝ} {n : ℕ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hn : 1 ≤ n)
    (hinv : WeightedDecoParameterInvariant w n) :
    WeightedDecoParameterInvariant w (n + 1) := by
  have hstep (a : Fin (n + 1) → ℝ) (ha : a ∈ weightedDecoParameterCube (n + 1))
      (j : Fin (n + 1)) :
      StrictInterl
          (weightedDecoParameterImage w (Finset.univ.erase j) a)
          (weightedDecoParameterImage w Finset.univ a) ∧
        HasSimpleRoots (weightedDecoParameterImage w Finset.univ a) ∧
        (∀ r, (weightedDecoParameterImage w Finset.univ a).IsRoot r → r < 0) ∧
        (∀ r, (weightedDecoParameterImage w (Finset.univ.erase j) a).IsRoot r →
          ¬(weightedDecoParameterImage w Finset.univ a).IsRoot r) := by
    let b : Fin n → ℝ := fun i => a (j.succAbove i)
    have hb : b ∈ weightedDecoParameterCube n := by
      intro i hi
      exact ha (j.succAbove i) (Set.mem_univ _)
    let g := weightedDecoParameterInput (Finset.univ.erase j) a
    have hgMonic : g.Monic := weightedDecoParameterInput_monic _ _
    have hgDegree : 1 ≤ g.natDegree := by
      dsimp only [g]
      rw [weightedDecoParameterInput_natDegree, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]
      simpa using hn
    have hpSplits : (weightedDecoTransform w g).Splits := by
      dsimp only [g]
      rw [← weightedDecoParameterImage, weightedDecoParameterImage_erase_fin]
      exact hinv.splits b hb
    have hpResidue : ∀ r, (weightedDecoTransform w g).IsRoot r →
        0 < (weightedDecoCompanionTransform w g).eval r /
          (weightedDecoTransform w g).derivative.eval r := by
      intro r hr
      dsimp only [g] at hr ⊢
      rw [← weightedDecoParameterImage,
        weightedDecoParameterImage_erase_fin] at hr ⊢
      rw [← weightedDecoParameterCompanion,
        weightedDecoParameterCompanion_erase_fin]
      exact hinv.companion_residue_pos b hb r hr
    have hpNeg : ∀ r, (weightedDecoTransform w g).IsRoot r → r < 0 := by
      intro r hr
      dsimp only [g] at hr
      rw [← weightedDecoParameterImage,
        weightedDecoParameterImage_erase_fin] at hr
      exact hinv.roots_neg b hb r hr
    have hgOne : 0 < g.eval 1 := by
      dsimp only [g, weightedDecoParameterInput]
      simp only [eval_prod, eval_add, eval_X, eval_C]
      apply Finset.prod_pos
      intro i hi
      have hai := ha i (Set.mem_univ i)
      rcases hai with ⟨hai0, hai1⟩
      linarith
    have haj : 0 ≤ a j := (ha j (Set.mem_univ j)).1
    have hs := weightedDecoTransform_mul_X_add_C_root_step haj hgMonic hgDegree
      hpSplits hpResidue hpNeg hgOne
    have hfull : (X + C (a j)) * g = weightedDecoParameterInput Finset.univ a := by
      dsimp only [g]
      exact (weightedDecoParameterInput_eq_mul_erase (Finset.mem_univ j)).symm
    simpa only [weightedDecoParameterImage, g, hfull] using hs
  have hsimple : ∀ a ∈ weightedDecoParameterCube (n + 1),
      HasSimpleRoots (weightedDecoParameterImage w Finset.univ a) := by
    intro a ha
    exact (hstep a ha 0).2.1
  have hsplits : ∀ a ∈ weightedDecoParameterCube (n + 1),
      (weightedDecoParameterImage w Finset.univ a).Splits := by
    intro a ha
    exact (hstep a ha 0).1.2.1.2
  have hrootsNeg : ∀ a ∈ weightedDecoParameterCube (n + 1), ∀ r,
      (weightedDecoParameterImage w Finset.univ a).IsRoot r → r < 0 := by
    intro a ha r hr
    exact (hstep a ha 0).2.2.1 r hr
  have halpha : ∀ a ∈ weightedDecoParameterCube (n + 1), ∀ r,
      (weightedDecoParameterImage w Finset.univ a).IsRoot r → ∀ j : Fin (n + 1),
        0 < (weightedDecoParameterImage w (Finset.univ.erase j) a).eval r /
          (weightedDecoParameterImage w Finset.univ a).derivative.eval r := by
    intro a ha r hr j
    have hs := hstep a ha j
    have hmul := hs.1.eval_mul_derivative_pos_of_right_root_of_no_common
      (hasPosLeadingCoeff_of_monic
        (weightedDecoParameterImage_monic w (Finset.univ.erase j) a))
      (hasPosLeadingCoeff_of_monic
        (weightedDecoParameterImage_monic w Finset.univ a))
      hs.2.2.2 hr
    have hd := hs.2.1.eval_derivative_ne_zero hr
    rw [show
        (weightedDecoParameterImage w (Finset.univ.erase j) a).eval r /
            (weightedDecoParameterImage w Finset.univ a).derivative.eval r =
          ((weightedDecoParameterImage w (Finset.univ.erase j) a).eval r *
              (weightedDecoParameterImage w Finset.univ a).derivative.eval r) /
            ((weightedDecoParameterImage w Finset.univ a).derivative.eval r) ^ 2 by
      field_simp [hd]]
    exact div_pos hmul (sq_pos_of_ne_zero hd)
  have hresidue := weightedDecoParameterCompanion_residue_pos_of_deletion
    hw0 hw1 (by lia) hsplits hsimple hrootsNeg halpha
  exact ⟨hsplits, hsimple, hrootsNeg, hresidue⟩

theorem weightedDecoParameterInvariant_all
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ∀ n : ℕ, 1 ≤ n → WeightedDecoParameterInvariant w n := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => simpa using weightedDecoParameterInvariant_one hw0 hw1
  | succ m ih =>
      exact WeightedDecoParameterInvariant.succ hw0 hw1 (by lia) (ih (by lia))

end RealRooted.Applications.OEIS
