import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.RootIncidenceCompact

/-!
# Compact parameter boxes for the weighted first-contact argument

We use boxes expanding from the diagonal point `1 / 2` to the full parameter
cube.  A bad contact records a root at which the companion residue is
nonpositive; we use the equivalent denominator-free sign condition.
-/

open Polynomial Set Topology

noncomputable section

namespace RealRooted.Applications.OEIS

def weightedDecoExpandingBox {n : ℕ} (t : ℝ) (a : Fin n → ℝ) : Prop :=
  ∀ i, (1 - t) / 2 ≤ a i ∧ a i ≤ (1 + t) / 2

def weightedDecoBadContactSet (w : ℝ) (n : ℕ) :
    Set (ℝ × ((Fin n → ℝ) × ℝ)) :=
  {z | z.1 ∈ Icc 0 1 ∧
    weightedDecoExpandingBox z.1 z.2.1 ∧
    (weightedDecoParameterImage w Finset.univ z.2.1).IsRoot z.2.2 ∧
    (weightedDecoParameterCompanion w Finset.univ z.2.1).eval z.2.2 *
      (weightedDecoParameterImage w Finset.univ z.2.1).derivative.eval z.2.2 ≤ 0}

theorem isClosed_weightedDecoBadContactSet (w : ℝ) (n : ℕ) :
    IsClosed (weightedDecoBadContactSet w n) := by
  let Z := ℝ × ((Fin n → ℝ) × ℝ)
  have ht : IsClosed {z : Z | z.1 ∈ Icc 0 1} :=
    isClosed_Icc.preimage continuous_fst
  have hlower : IsClosed {z : Z | ∀ i, (1 - z.1) / 2 ≤ z.2.1 i} := by
    rw [show {z : Z | ∀ i, (1 - z.1) / 2 ≤ z.2.1 i} =
        ⋂ i, {z : Z | (1 - z.1) / 2 ≤ z.2.1 i} by ext z; simp]
    apply isClosed_iInter
    intro i
    apply isClosed_le
    · fun_prop
    · exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have hupper : IsClosed {z : Z | ∀ i, z.2.1 i ≤ (1 + z.1) / 2} := by
    rw [show {z : Z | ∀ i, z.2.1 i ≤ (1 + z.1) / 2} =
        ⋂ i, {z : Z | z.2.1 i ≤ (1 + z.1) / 2} by ext z; simp]
    apply isClosed_iInter
    intro i
    apply isClosed_le
    · exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    · fun_prop
  have hpcont : Continuous fun z : Z =>
      (weightedDecoParameterImage w Finset.univ z.2.1).eval z.2.2 :=
    (continuous_weightedDecoParameterImage_eval_prod w Finset.univ).comp
      continuous_snd
  have hpdercont : Continuous fun z : Z =>
      (weightedDecoParameterImage w Finset.univ z.2.1).derivative.eval z.2.2 :=
    (continuous_weightedDecoParameterImage_derivative_eval_prod
      w Finset.univ).comp continuous_snd
  have hhcont : Continuous fun z : Z =>
      (weightedDecoParameterCompanion w Finset.univ z.2.1).eval z.2.2 :=
    (continuous_weightedDecoParameterCompanion_eval_prod w Finset.univ).comp
      continuous_snd
  have hroot : IsClosed {z : Z |
      (weightedDecoParameterImage w Finset.univ z.2.1).IsRoot z.2.2} := by
    rw [show {z : Z |
        (weightedDecoParameterImage w Finset.univ z.2.1).IsRoot z.2.2} =
      {z : Z |
        (weightedDecoParameterImage w Finset.univ z.2.1).eval z.2.2 = 0} by
      ext z
      rfl]
    exact isClosed_eq hpcont continuous_const
  have hsign : IsClosed {z : Z |
      (weightedDecoParameterCompanion w Finset.univ z.2.1).eval z.2.2 *
        (weightedDecoParameterImage w Finset.univ z.2.1).derivative.eval
          z.2.2 ≤ 0} :=
    isClosed_le (hhcont.mul hpdercont) continuous_const
  change IsClosed {z : Z | z.1 ∈ Icc 0 1 ∧
    weightedDecoExpandingBox z.1 z.2.1 ∧
    (weightedDecoParameterImage w Finset.univ z.2.1).IsRoot z.2.2 ∧
    (weightedDecoParameterCompanion w Finset.univ z.2.1).eval z.2.2 *
      (weightedDecoParameterImage w Finset.univ z.2.1).derivative.eval
        z.2.2 ≤ 0}
  have hbox : IsClosed {z : Z | weightedDecoExpandingBox z.1 z.2.1} := by
    rw [show {z : Z | weightedDecoExpandingBox z.1 z.2.1} =
        {z : Z | ∀ i, (1 - z.1) / 2 ≤ z.2.1 i} ∩
          {z : Z | ∀ i, z.2.1 i ≤ (1 + z.1) / 2} by
      ext z
      simp only [weightedDecoExpandingBox, Set.mem_inter_iff, Set.mem_ofPred_eq,
        forall_and]]
    exact hlower.inter hupper
  exact ht.inter (hbox.inter (hroot.inter hsign))

theorem isCompact_weightedDecoBadContactSet
    (w : ℝ) (n : ℕ) (hn : n ≠ 0) :
    IsCompact (weightedDecoBadContactSet w n) := by
  let A : Set (ℝ × ((Fin n → ℝ) × ℝ)) :=
    Icc 0 1 ×ˢ {z : (Fin n → ℝ) × ℝ |
      z.1 ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) ∧
        (weightedDecoParameterImage w Finset.univ z.1).IsRoot z.2}
  have hA : IsCompact A :=
    isCompact_Icc.prod (isCompact_weightedDecoParameterRootIncidence w n hn)
  apply hA.of_isClosed_subset (isClosed_weightedDecoBadContactSet w n)
  rintro z ⟨ht, hbox, hroot, -⟩
  refine ⟨ht, ?_, hroot⟩
  intro i hiuniv
  have hi := hbox i
  constructor <;> linarith [ht.1, ht.2]

/-- If the bad-contact set is nonempty, its expansion-time coordinate attains
a minimum. -/
theorem exists_minimal_weightedDecoBadContact
    (w : ℝ) (n : ℕ) (hn : n ≠ 0)
    (hne : (weightedDecoBadContactSet w n).Nonempty) :
    ∃ z ∈ weightedDecoBadContactSet w n,
      ∀ y ∈ weightedDecoBadContactSet w n, z.1 ≤ y.1 := by
  obtain ⟨z, hz, hzmin⟩ :=
    (isCompact_weightedDecoBadContactSet w n hn).exists_isMinOn hne
      continuous_fst.continuousOn
  exact ⟨z, hz, hzmin⟩

end RealRooted.Applications.OEIS
