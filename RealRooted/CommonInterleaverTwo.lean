/-
# Two-polynomial common interleaver converse

Bridge file for compatibility/common-interleaver statements:
- two-polynomial compatibility and pairwise compatibility on finite lists,
- easy directions from common left interleavers to compatibility,
- the reduction of Chudnovsky--Seymour to the missing two-polynomial converse
  and the still-unpackaged list-level left-handed Helly upgrade.

This file sits between the positive-combination machinery (PosCombo) and
the list-level common-interleaver combinatorics (CommonInterleaverSeq).
-/
import RealRooted.PosCombo
import RealRooted.CommonInterleaverSeq
import RealRooted.AffineFamily
import RealRooted.GammaRealRoots

open Polynomial

noncomputable section

namespace RealRooted

private lemma nonneg_of_add_mul_pos_forall {a b : ℝ}
    (h : ∀ {μ : ℝ}, 0 < μ → 0 ≤ a + μ * b) :
    0 ≤ a := by
  by_contra ha
  have ha_lt : a < 0 := lt_of_not_ge ha
  by_cases hb : b ≤ 0
  · have hbad : a + (1 : ℝ) * b < 0 := by
      nlinarith
    exact not_lt_of_ge (h zero_lt_one) hbad
  · have hb_pos : 0 < b := lt_of_not_ge hb
    let μ : ℝ := -a / (2 * b)
    have hμ_pos : 0 < μ := by
      unfold μ
      simp_all
    have hμ_ge : 0 ≤ a + μ * b := h hμ_pos
    have hμ_bad : a + μ * b < 0 := by
      unfold μ
      have hb_ne : b ≠ 0 := ne_of_gt hb_pos
      field_simp [hb_ne]
      nlinarith
    grind

private lemma coeff_nonneg_of_add_C_mul_nonneg_forall
    {f g : ℝ[X]}
    (h : ∀ {μ : ℝ}, 0 < μ → HasNonnegCoeffs (f + C μ * g)) :
    HasNonnegCoeffs f := by
  intro n
  refine nonneg_of_add_mul_pos_forall
    (a := f.coeff n) (b := g.coeff n) ?_
  intro μ hμ
  have hμnn : HasNonnegCoeffs (f + C μ * g) := h hμ
  simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul] using hμnn n

private lemma no_common_boundary_right_pair_of_no_common_nonneg
    {f g : ℝ[X]} {t : ℝ}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (ht : 0 < t) :
    ∀ r, (C t * f + g).IsRoot r → ¬ (X * f).IsRoot r := by
  intro r hsum hX
  by_cases hr0 : r = 0
  · have hsum_eval : (C t * f + g).eval 0 = 0 := by simp_all
    have hf_eval_nonneg : 0 ≤ f.eval 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hfnn 0
    have hg_eval_nonneg : 0 ≤ g.eval 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hgnn 0
    have htf_eval_nonneg : 0 ≤ t * f.eval 0 := mul_nonneg ht.le hf_eval_nonneg
    have hf_eval0 : f.eval 0 = 0 := by
      rw [eval_add, eval_mul, eval_C] at hsum_eval
      nlinarith
    simp_all
  · simp_all

/-- Chudnovsky--Seymour compatibility for a pair: every nonnegative linear
combination is real-rooted, allowing the zero polynomial in the degenerate
`α = β = 0` case. -/
def Compatible (f g : ℝ[X]) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
    C α * f + C β * g = 0 ∨ ((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits)

/-- Pairwise compatibility on a finite family, in the Chudnovsky--Seymour
sense from `INTERLACING.md`. -/
def PairwiseCompatible (fs : List ℝ[X]) : Prop :=
  ∀ (i j : Fin fs.length), i < j → Compatible (fs.get i) (fs.get j)

/-- Full Chudnovsky--Seymour compatibility for a finite family:
every nonnegative weighted sum of members of `fs` is real-rooted (or zero). -/
def FamilyCompatible (fs : List ℝ[X]) : Prop :=
  ∀ l : List (ℝ × ℝ[X]),
    (∀ ap ∈ l, ap.2 ∈ fs) →
    (∀ ap ∈ l, 0 ≤ ap.1) →
    weightedSum l = 0 ∨ ((weightedSum l) ≠ 0 ∧ (weightedSum l).Splits)

namespace Compatible

lemma comm {f g : ℝ[X]} (h : Compatible f g) : Compatible g f := by
  intro α β hα hβ
  simpa [Compatible, add_comm, mul_comm, mul_left_comm, mul_assoc] using h β α hβ hα

lemma comp_X_add_C {f g : ℝ[X]} (h : Compatible f g) (r : ℝ) :
    Compatible (f.comp (X + C r)) (g.comp (X + C r)) := by
  intro α β hα hβ
  have hcomb :
      C α * f.comp (X + C r) + C β * g.comp (X + C r) =
        (C α * f + C β * g).comp (X + C r) := by
    simp
  rcases h α β hα hβ with hzero | hrr
  · simp_all
  · right
    rw [hcomb]
    exact isRealRooted_comp_X_add_C hrr.1 hrr.2 r

/-- Article 3.1: compatibility is preserved by differentiation. -/
lemma derivative {f g : ℝ[X]} (h : Compatible f g) :
    Compatible f.derivative g.derivative := by
  intro α β hα hβ
  have hcomb :
      C α * f.derivative + C β * g.derivative =
        (C α * f + C β * g).derivative := by
    simp [Polynomial.derivative_add, Polynomial.derivative_mul]
  rcases h α β hα hβ with hzero | hrr
  · simp_all
  · rw [hcomb]
    exact derivative_eq_zero_or_ne_zero_and_splits hrr.2

private lemma isRealRooted_left
    {f g : ℝ[X]} (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) : (f ≠ 0 ∧ f.Splits) := by
  rcases h 1 0 (by simp) (by simp) with hzero | hrr <;> simp_all

private lemma isRealRooted_right
    {f g : ℝ[X]} (h : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g) : (g ≠ 0 ∧ g.Splits) := by
  rcases h 0 1 (by simp) (by simp) with hzero | hrr <;> simp_all

private lemma natDegree_le_one_of_const_left
    {c : ℝ} {g : ℝ[X]}
    (hc : 0 < c)
    (hg_pos : HasPosLeadingCoeff g)
    (hcg : Compatible (C c) g) :
    g.natDegree ≤ 1 := by
  by_cases hdeg : g.natDegree ≤ 1
  · lia
  have hg_deg2 : 2 ≤ g.natDegree := by lia
  have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_right hcg hg_pos
  obtain ⟨t, ht_pos, ht_bad⟩ :=
    exists_pos_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
      hg_rr.2 hg_pos hg_deg2
  have hcombo :
      C (t / c) * C c + g = 0 ∨
        ((C (t / c) * C c + g) ≠ 0 ∧ (C (t / c) * C c + g).Splits) := by
    simpa using hcg (t / c) 1 (by positivity) (by simp)
  have hrewrite :
      C (t / c) * C c + g = C t + g := by
    calc
      C (t / c) * C c + g = C ((t / c) * c) + g := by simp
      _ = C t + g := by
        grind
  rcases hcombo with hzero | hrr
  · have hzero' : C t + g = 0 := by lia
    have hg_const : g = -C t := by grind
    simp_all
  · lia

/-- Article 3.2, one-sided form: in a positive-leading compatible pair, the
right degree is at most one more than the left degree. -/
theorem natDegree_right_le_succ
    {f g : ℝ[X]} (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    g.natDegree ≤ f.natDegree + 1 := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          Compatible f g →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          g.natDegree ≤ f.natDegree + 1)
      f.natDegree ?_ rfl h hf_pos hg_pos
  intro n ih f g hfdeg hfg hf_pos hg_pos
  by_cases hf_deg0 : f.natDegree = 0
  · have hf_ne : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
    let c : ℝ := f.coeff 0
    have hcoeff0 : f.coeff 0 = f.leadingCoeff := by
      simpa [hf_deg0] using (Polynomial.coeff_natDegree (p := f))
    have hc : 0 < c := by
      dsimp [c]
      rw [hcoeff0]
      exact hf_pos
    have hf_const : f = C c := by
      simpa [c] using eq_C_of_natDegree_eq_zero hf_deg0
    have hfg_const : Compatible (C c) g := by lia
    have hbound : g.natDegree ≤ 1 :=
      natDegree_le_one_of_const_left hc hg_pos hfg_const
    lia
  · by_cases hg_deg0 : g.natDegree = 0
    · lia
    · have hf_deg1 : 1 ≤ f.natDegree := by lia
      have hg_deg1 : 1 ≤ g.natDegree := by lia
      have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
      have hg'_pos : HasPosLeadingCoeff g.derivative := hg_pos.derivative (by lia)
      have hfg' : Compatible f.derivative g.derivative := derivative hfg
      have hf'_deg : f.derivative.natDegree = f.natDegree - 1 := f.natDegree_derivative
      have hg'_deg : g.derivative.natDegree = g.natDegree - 1 := g.natDegree_derivative
      grind

/-- Article 3.2: a positive-leading compatible pair has degree gap at most
one. -/
theorem natDegree_close
    {f g : ℝ[X]} (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  constructor
  · simpa using natDegree_right_le_succ h.comm hg_pos hf_pos
  · exact natDegree_right_le_succ h hf_pos hg_pos

lemma toPosComboRealRooted {f g : ℝ[X]} (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro α β hα hβ
  rcases h α β hα.le hβ.le with hzero | hrr
  · have hsum_pos : HasPosLeadingCoeff (C α * f + C β * g) := by
      by_cases hdeg : f.natDegree ≤ g.natDegree
      · exact
          hasPosLeadingCoeff_pos_combo_of_natDegree_le_right
            hdeg hf_pos hg_pos hα hβ
      · exact
          hasPosLeadingCoeff_pos_combo_of_natDegree_le_left
            (le_of_not_ge hdeg) hf_pos hg_pos hα hβ
    have hsum_ne : C α * f + C β * g ≠ 0 := by
      intro hsum
      simp [HasPosLeadingCoeff, hsum] at hsum_pos
    lia
  · lia

/-- In equal degree, strict positive-combination real-rootedness upgrades to
full nonnegative compatibility: the endpoint real-rootedness follows from the
same-degree restricted converse, and the genuinely positive quadrant is exactly
the `PosComboRealRooted` hypothesis. -/
lemma of_posComboRealRooted_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    Compatible f g := by
  have hf : (f ≠ 0 ∧ f.Splits) :=
    PosComboRealRooted.isRealRooted_left_of_sameDegree hfg hf_pos hg_pos hdeg
  have hg : (g ≠ 0 ∧ g.Splits) :=
    PosComboRealRooted.isRealRooted_right_of_sameDegree hfg hf_pos hg_pos hdeg
  intro α β hα hβ
  by_cases hα0 : α = 0
  · subst hα0
    by_cases hβ0 : β = 0 <;> simp_all
  · by_cases hβ0 : β = 0
    · simp_all
    · right
      have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hβ_pos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      exact hfg hα_pos hβ_pos

/-- A common left interleaver gives full nonnegative compatibility for a pair,
not just the strictly positive `PosComboRealRooted` condition. -/
lemma of_commonLeftInterleaver {f g h : ℝ[X]}
    (hhf : Prec h f) (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    Compatible f g := by
  intro α β hα hβ
  by_cases hα0 : α = 0
  · subst hα0
    by_cases hβ0 : β = 0
    · simp_all
    · right
      simpa using isRealRooted_C_mul hhg.2.1.1 hhg.2.1.2 hβ0
  · by_cases hβ0 : β = 0
    · subst hβ0
      right
      simpa using isRealRooted_C_mul hhf.2.1.1 hhf.2.1.2 hα0
    · right
      have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hβ_pos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      exact PosComboRealRooted.of_commonLeftInterleaver hhf hhg hf_pos hg_pos hα_pos hβ_pos

/-- A common right interleaver gives full nonnegative compatibility for a pair.
This is the right-oriented Wagner direction used by the list-level
Chudnovsky--Seymour chain. -/
lemma of_commonInterleaver {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    Compatible f g := by
  intro α β hα hβ
  by_cases hα0 : α = 0
  · subst hα0
    by_cases hβ0 : β = 0
    · simp_all
    · right
      simpa using isRealRooted_C_mul hgh.1.1 hgh.1.2 hβ0
  · by_cases hβ0 : β = 0
    · subst hβ0
      right
      simpa using isRealRooted_C_mul hfh.1.1 hfh.1.2 hα0
    · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      right
      have hprec :
          Prec (weightedSum [(α, f), (β, g)]) h := by
        refine prec_weightedSum_right [(α, f), (β, g)] h ?_ ?_ ?_ ?_ <;> simp_all
      simpa [weightedSum, weightedSum_cons] using hprec.1

end Compatible

namespace PosComboRealRooted

lemma comp_X_add_C {f g : ℝ[X]} (h : PosComboRealRooted f g) (r : ℝ) :
    PosComboRealRooted (f.comp (X + C r)) (g.comp (X + C r)) := by
  intro α β hα hβ
  have hcomb :
      C α * f.comp (X + C r) + C β * g.comp (X + C r) =
        (C α * f + C β * g).comp (X + C r) := by
    simp
  rw [hcomb]
  exact isRealRooted_comp_X_add_C (h hα hβ).1 (h hα hβ).2 r

end PosComboRealRooted

/-- A family with a common left interleaver is pairwise compatible. This is
the easy Chudnovsky--Seymour direction. -/
theorem pairwiseCompatible_of_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rcases hcommon with ⟨h, hprec⟩
  intro i j hij
  exact Compatible.of_commonLeftInterleaver
    (hprec (fs.get i) (List.get_mem _ _))
    (hprec (fs.get j) (List.get_mem _ _))
    (hpos (fs.get i) (List.get_mem _ _))
    (hpos (fs.get j) (List.get_mem _ _))

/-- The same easy direction, but starting from pairwise common left
interleavers rather than a single global witness. -/
theorem pairwiseCompatible_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  intro i j hij
  rcases hpair i j hij with ⟨h, hhi, hhj⟩
  exact Compatible.of_commonLeftInterleaver
    hhi hhj
    (hpos (fs.get i) (List.get_mem _ _))
    (hpos (fs.get j) (List.get_mem _ _))

/-- A family with a common right interleaver is pairwise compatible. -/
theorem pairwiseCompatible_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rcases hcommon with ⟨h, hprec⟩
  intro i j hij
  exact Compatible.of_commonInterleaver
    (hprec (fs.get i) (List.get_mem _ _))
    (hprec (fs.get j) (List.get_mem _ _))
    (hpos (fs.get i) (List.get_mem _ _))
    (hpos (fs.get j) (List.get_mem _ _))

/-- Pairwise common right interleavers imply pairwise compatibility. -/
theorem pairwiseCompatible_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  intro i j hij
  rcases hpair i j hij with ⟨h, hih, hjh⟩
  exact Compatible.of_commonInterleaver
    hih hjh
    (hpos (fs.get i) (List.get_mem _ _))
    (hpos (fs.get j) (List.get_mem _ _))

/-- Once the two-polynomial common-left-interleaver converse is available, the
pairwise Chudnovsky--Seymour hypothesis immediately upgrades to pairwise common
left interleavers. This isolates the exact missing bridge. -/
theorem pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible
    {fs : List ℝ[X]}
    (htwo : ∀ ⦃f g : ℝ[X]⦄, Compatible f g → ∃ h : ℝ[X], Prec h f ∧ Prec h g)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonLeftInterleaver fs := by
  intro i j hij
  simpa using htwo (hpair i j hij)

/-- Reduction for the left-oriented Chudnovsky--Seymour target: the full
`PairwiseCompatible ↔ HasCommonLeftInterleaver` statement follows from the
two-polynomial common-left bridge and the finite-family left Helly upgrade. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : ∀ ⦃f g : ℝ[X]⦄, Compatible f g → ∃ h : ℝ[X], Prec h f ∧ Prec h g)
    (hglobal : PairwiseHasCommonLeftInterleaver fs → HasCommonLeftInterleaver fs) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs := by
  constructor
  · intro hpair
    exact hglobal (pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible htwo hpair)
  · intro hcommon
    exact pairwiseCompatible_of_commonLeftInterleaver hcommon hpos

/-- Once the two-polynomial common-right-interleaver converse is available, the
pairwise Chudnovsky--Seymour hypothesis upgrades to pairwise common right
interleavers. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible
    {fs : List ℝ[X]}
    (htwo : ∀ ⦃f g : ℝ[X]⦄, Compatible f g → ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  intro i j hij
  simpa using htwo (hpair i j hij)

/-- Natural two-polynomial bridge hypothesis in the Chudnovsky--Seymour setup:
compatibility plus positive leading coefficients implies a common right
interleaver. -/
def CompatiblePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Same-degree branch of the positive-leading compatibility bridge. This is
the honest `Compatible`-level version of article 3.6.1 → 3.6.2 in the equal-
degree case. -/
def CompatibleSameDegreePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    g.natDegree = f.natDegree →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Succ-degree branch of the positive-leading compatibility bridge. Since
`Compatible.natDegree_close` already rules out larger degree gaps, this and
the same-degree branch are the only genuinely remaining cases. -/
def CompatibleSuccDegreePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    g.natDegree = f.natDegree + 1 →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Since `Compatible.natDegree_close` limits the degree gap to at most one,
the full positive-leading compatibility bridge reduces to the same-degree and
succ-degree cases, together with symmetry. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hclose := Compatible.natDegree_close hfg hf_pos hg_pos
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · have hcases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by
      lia
    rcases hcases with hsame_deg | hsucc_deg
    · exact hsame hf_pos hg_pos hfg hsame_deg
    · exact hsucc hf_pos hg_pos hfg hsucc_deg
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hcases : f.natDegree = g.natDegree ∨ f.natDegree = g.natDegree + 1 := by lia
    rcases hcases with hsame_deg | hsucc_deg
    · lia
    · rcases hsucc hg_pos hf_pos hfg.comm hsucc_deg with ⟨h, hg_prec, hf_prec⟩
      grind

/-- Core two-polynomial target in positive-combination language: a
positive-leading `PosComboRealRooted` pair admits a common right interleaver. -/
def PosComboPairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    PosComboRealRooted f g →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Degree-closeness bridge for positive-combination pairs. This is the
remaining degree-only ingredient needed to pass from the no-common-roots
orientation core to a full two-polynomial common-right-interleaver theorem. -/
def PosComboNatDegreeCloseStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1

/-- No-common-roots orientation core for the positive-combination converse.
This matches the local step parameter in
`PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common`. -/
def PosComboNoCommonOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    PosComboRealRooted f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g ∨ Prec g f

/-- Bridge statement: in the no-common, close-degree setup, positive-combination
real-rootedness upgrades to full all-combinations real-rootedness. -/
def PosComboNoCommonToAllComboBridgeStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    AllComboRealRooted f g

/-- Stronger no-common bridge hypothesis in the nonnegative regime: instead of
directly asking for `AllComboRealRooted f g`, assume the pair satisfies the
full positive affine family needed by Brändén's converse. This isolates the
remaining missing step as an affine-family packaging problem. -/
def PosComboNoCommonAffineFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
      ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)

private lemma allComboRealRooted_left_rr
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hf0 : f ≠ 0) :
    f ≠ 0 ∧ f.Splits :=
  ⟨hf0, by simpa using hall 1 0⟩

private lemma allComboRealRooted_right_rr
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hg0 : g ≠ 0) :
    g ≠ 0 ∧ g.Splits :=
  ⟨hg0, by simpa using hall 0 1⟩

/-- Stronger boundary-right-pair hypothesis in the nonnegative no-common
regime: for each boundary member `C t * f + g`, orient the right-hand pair
against `X * f`.  This is a useful conditional route to the affine family, not
the current endpoint for the packet proof. -/
def PosComboNoCommonBoundaryRightPairOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ ⦃t : ℝ⦄, 0 < t →
      Prec (C t * f + g) (X * f) ∨ Prec (X * f) (C t * f + g)

/-- Strong shifted-pair formulation for the same-degree no-common branch after
the affine/boundary counterexample.  It remains a named conditional hypothesis;
the downstream bridge now uses the common-right-interleaver target below as the
weaker endpoint. -/
def PosComboNoCommonSameDegreeShiftedPairOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f (g + X * f)

/-- Legacy fixed-orientation same-degree target in the nonnegative no-common
regime.  It is retained for older reductions, but the repaired bridge no
longer treats this as the required same-degree endpoint. -/
def PosComboNoCommonSameDegreeOrientationNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g

/-- Strong same-degree no-common alternative in the nonnegative regime.  This
weakens the fixed orientation, but it is still stronger than the repaired
common-right-interleaver endpoint below. -/
def PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g ∨ Prec g f

/-- Repaired same-degree no-common target in the nonnegative regime. The
orientation alternative is too strong in degree `2`; for the
Chudnovsky--Seymour bridge the needed conclusion is only a common right
interleaver. -/
def PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Fixed-orientation succ-degree target in the nonnegative no-common regime.
This is stronger than what the Chudnovsky--Seymour bridge needs; the repaired
succ-degree endpoint below only asks for a common right interleaver. -/
def PosComboNoCommonSuccDegreeOrientationNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g

/-- Repaired succ-degree no-common target for the Chudnovsky--Seymour bridge
in the nonnegative regime: when the right degree is exactly one larger, the
needed conclusion is the existence of a common interleaver, not a fixed
orientation between `f` and `g`. -/
def PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- If the original pair is already oriented as `f ≺ g`, then every boundary
right pair `(C t * f + g, X * f)` inherits the correct orientation just by
combining `g ≺ X * f` with the trivial self-orientation of `f`. -/
theorem prec_boundary_right_pair_of_prec_nonneg
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    {t : ℝ} (ht : 0 < t) :
    Prec (C t * f + g) (X * f) := by
  have hgfX : Prec g (X * f) := prec_to_prec_mul_X_of_nonneg hprec hfnn hgnn
  have hfX : Prec f (X * f) := prec_self_mul_X_of_nonneg hprec.1.1 hprec.1.2 hfnn
  have htfX : Prec (C t * f) (X * f) := prec_C_mul_left hfX ht.ne'
  have htf_pos : HasPosLeadingCoeff (C t * f) :=
    hasPosLeadingCoeff_C_mul ht (hfnn.pos_leadingCoeff hprec.1.1)
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hprec.2.1.1
  exact prec_add_of_prec_right_of_posLeadingCoeff htfX hgfX htf_pos hg_pos

/-- Once the fixed right-hand pair `(g, X * f)` is oriented, the polynomial
`X * f` itself is already a common right interleaver for `f` and `g`. -/
theorem pairHasCommonInterleaver_of_prec_right_pair_nonneg
    {f g : ℝ[X]}
    (hprec : Prec g (X * f))
    (hfnn : HasNonnegCoeffs f) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hprec.2.1.1 hprec.2.1.2
  exact ⟨X * f, prec_self_mul_X_of_nonneg hf.1 hf.2 hfnn, hprec⟩

private theorem prec_forward_of_orientation_of_succDegree
    {f g : ℝ[X]}
    (hsucc : g.natDegree = f.natDegree + 1)
    (hprec_or : Prec f g ∨ Prec g f) :
    Prec f g := by
  rcases hprec_or with hprec | hprec
  · exact hprec
  · have hbounds := natDegree_bounds_of_prec hprec
    lia

/-- In the succ-degree branch, the boundary right pair is automatic as soon as
the original no-common orientation statement is known: `Prec g f` is ruled out
by degree, so the previous transport theorem applies. -/
theorem prec_boundary_right_pair_of_orientation_succDegree_nonneg
    (horient : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {t : ℝ} (ht : 0 < t) :
    Prec (C t * f + g) (X * f) := by
  have hprec_or : Prec f g ∨ Prec g f :=
    horient hfg hf_pos hg_pos (by lia) (by lia) hno
  have hprec_fg : Prec f g :=
    prec_forward_of_orientation_of_succDegree hsucc hprec_or
  exact prec_boundary_right_pair_of_prec_nonneg hprec_fg hfnn hgnn ht

/-- Orienting each boundary pair `(C t * f + g, X * f)` is already enough to
recover the full affine-family hypothesis. The no-common condition for the
boundary pair is automatic from nonnegative coefficients and the original
no-common hypothesis. -/
theorem posComboNoCommonAffineFamily_of_boundaryRightPairOrientation
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PosComboNoCommonAffineFamilyStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno s t hs ht
  let p : ℝ[X] := C t * f + g
  have hp_rr : (p ≠ 0 ∧ p.Splits) := by
    dsimp [p]
    simpa using PosComboRealRooted.isRealRooted_add_left hfg ht
  have hp_nn : HasNonnegCoeffs p := by
    dsimp [p]
    exact (nonnegCoeffs_C_mul ht.le hfnn).add hgnn
  have hp_pos : HasPosLeadingCoeff p := hp_nn.pos_leadingCoeff hp_rr.1
  have hXf_nn : HasNonnegCoeffs (X * f) := hasNonnegCoeffs_X.mul hfnn
  have hXf0 : X * f ≠ 0 := mul_ne_zero X_ne_zero (HasPosLeadingCoeff.ne_zero hf_pos)
  have hXf_pos : HasPosLeadingCoeff (X * f) := hXf_nn.pos_leadingCoeff hXf0
  have hprec_or : Prec p (X * f) ∨ Prec (X * f) p := by
    dsimp [p]
    exact hboundary hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno ht
  have hno_right : ∀ r, p.IsRoot r → ¬ (X * f).IsRoot r := by
    dsimp [p]
    exact no_common_boundary_right_pair_of_no_common_nonneg hfnn hgnn hno ht
  have hprec : Prec p (X * f) :=
    prec_right_pair_of_prec_or_revPrec_of_no_common_nonneg
      hprec_or hp_rr.1 hp_rr.2 hp_nn hno_right
  have hcombo_rr :
      ((C (1 : ℝ) * p + C s * (X * f)) ≠ 0 ∧ (C (1 : ℝ) * p + C s * (X * f)).Splits) :=
    isRealRooted_nonneg_combo_of_prec
      hprec hp_pos hXf_pos (by simp) hs.le (Or.inl zero_lt_one)
  grind

/-- The corrected shifted-pair same-degree hypothesis already implies the
original same-degree orientation statement in the nonnegative regime, via the
public shifted-pair subtraction theorem from `AffineFamily`. -/
theorem posComboNoCommonSameDegreeOrientation_of_shiftedPairOrientation_and_nonnegCoeffs
    (hshift : PosComboNoCommonSameDegreeShiftedPairOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  exact
    prec_of_prec_shifted_pair_sameDegree_nonneg
      (hshift hf_pos hg_pos hfnn hgnn hfg hdeg hno)
      hf0 hg0 hfnn hgnn hdeg

/-- Consequently, the corrected shifted-pair same-degree hypothesis already
gives the same-degree all-combinations bridge in the nonnegative regime. -/
theorem allComboRealRooted_of_sameDegreeShiftedPairOrientation_and_nonnegCoeffs
    (hshift : PosComboNoCommonSameDegreeShiftedPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_prec
    ((posComboNoCommonSameDegreeOrientation_of_shiftedPairOrientation_and_nonnegCoeffs
        hshift) hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- Forward orientation of the right-family pair `(f + g, f + 2g)` already
forces the sum `f + g` to interlace `g` on the left in the high-degree
same-degree nonnegative branch. This is the first concrete transport step
behind the right-family reroute. -/
theorem prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hpair : Prec (f + g) (f + C (2 : ℝ) * g)) :
    Prec (f + g) g := by
  let F : ℝ[X] := f + g
  let G : ℝ[X] := f + C (2 : ℝ) * g
  rcases
      PosComboRealRooted.family_pair_data_right_one_two
        (f := f) (g := g) hfg (by lia) hf_pos hg_pos hno with
    ⟨_, hF_pos, hG_pos, hF_deg, hG_deg, _⟩
  have hF_deg' : F.natDegree = g.natDegree := by grind
  have hno_FG : ∀ r, F.IsRoot r → ¬ G.IsRoot r := by
    simpa [F, G] using
      PosComboRealRooted.no_common_root_right_family_one_two_of_no_common
        (f := f) (g := g) hno
  have hFG_deg : F.natDegree = G.natDegree := by lia
  have hG_deg_pos : 1 ≤ G.natDegree := by lia
  obtain ⟨uR, q, hGq, huR_root, huR_max, hqF⟩ :=
    exists_rightmost_factor_interlaces_of_prec_sameDegree
      (f := F) (g := G) hpair hFG_deg hG_deg_pos
  have hq_pos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [G, hGq] using hG_pos)
  have hFq_no : ∀ r, F.IsRoot r → ¬ q.IsRoot r := by simp_all
  have hroot_lt : ∀ r, F.IsRoot r → r < uR := by
    intro r hFr
    have hr_le : r ≤ uR :=
      roots_le_of_prec_right hpair huR_max r ((mem_roots hpair.1.1).mpr hFr)
    grind
  have htarget_eq : C (-1 : ℝ) * F + (X - C uR) * q = g := by
    dsimp [F, G] at hGq ⊢
    calc
      C (-1 : ℝ) * (f + g) + (X - C uR) * q
          = C (-1 : ℝ) * (f + g) + (f + C (2 : ℝ) * g) := by
              lia
      _ = g := by
            ext n
            simp [Polynomial.coeff_C_mul]
            ring
  have htarget_eq' : -F + (X - C uR) * q = g := by simp_all
  have hprec :
      Prec F (C (-1 : ℝ) * F + (X - C uR) * q) :=
    prec_of_interlaces_evalCoeff_neg_same
      (f := F) (g := q) (a := C (-1 : ℝ)) (b := X - C uR)
      hqF hq_pos
      (by lia)
      (by lia)
      hFq_no
      (by simp_all)
  lia

/-- Swapping the roles of `f` and `g` gives the symmetric forward transport for
the left-family pair `(f + g, 2f + g)`. -/
theorem prec_sum_left_of_prec_left_family_forward_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hpair : Prec (f + g) (C (2 : ℝ) * f + g)) :
    Prec (f + g) f := by
  have hno_swap : ∀ r, g.IsRoot r → ¬ f.IsRoot r := by grind
  have hf_deg_pos : 1 ≤ f.natDegree := by lia
  simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
      (f := g) (g := f)
      hg_pos hf_pos (PosComboRealRooted.comm hfg) hdeg.symm hf_deg_pos
      hno_swap
      (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using hpair)

/-- If both specialized one-step families point forward, then their common
middle sum `f + g` is already a common left interleaver for `f` and `g`. This
makes the purpose of the `f + g`, `f + 2g`, `2f + g` reroutes explicit. -/
theorem pairHasCommonLeftInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  refine ⟨f + g, ?_, ?_⟩
  · exact
      prec_sum_left_of_prec_left_family_forward_sameDegree_nonneg
        hf_pos hg_pos hfg hdeg hdeg_pos hno hleft
  · exact
      prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
        hf_pos hg_pos hfg hdeg hdeg_pos hno hright

/-- The same forward one-two-family hypotheses already force the original pair
to be compatible: the common left interleaver `f + g` witnesses all
nonnegative combinations. -/
theorem compatible_of_forward_oneTwoFamilies_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    Compatible f g := by
  obtain ⟨h, hhf, hhg⟩ :=
    pairHasCommonLeftInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
      hf_pos hg_pos hfg hdeg hdeg_pos hno hright hleft
  exact Compatible.of_commonLeftInterleaver hhf hhg hf_pos hg_pos

/-- Consequently, any generic two-polynomial compatibility bridge can consume
the forward one-two-family hypotheses directly. -/
theorem pairHasCommonInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
    (htwo : CompatiblePairHasCommonInterleaverStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  htwo hf_pos hg_pos
    (compatible_of_forward_oneTwoFamilies_sameDegree_nonneg
      hf_pos hg_pos hfg hdeg hdeg_pos hno hright hleft)

/-- Any two positive-leading polynomials of degree at most one already satisfy
the Obreschkoff alternative. This is the unconditional low-degree endpoint for
the current bridge search. -/
theorem prec_or_revPrec_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    Prec f g ∨ Prec g f := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  by_cases hf_deg0 : f.natDegree = 0
  · have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_deg_zero hf0 hf_deg0
    by_cases hg_deg0 : g.natDegree = 0
    · have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      exact Or.inl (prec_degree_zero_degree_zero hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_deg0 hg_deg0)
    · have hg_deg1 : g.natDegree = 1 := by lia
      have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg1
      exact Or.inl (prec_degree_zero_right_of_degree_one hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2
        hf_deg0 hg_deg1)
  · have hf_deg1 : f.natDegree = 1 := by lia
    by_cases hg_deg0 : g.natDegree = 0
    · have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_degree_one hf_deg1
      exact Or.inr (prec_degree_zero_right_of_degree_one hg_rr.1 hg_rr.2 hf_rr.1 hf_rr.2
        hg_deg0 hf_deg1)
    · have hg_deg1 : g.natDegree = 1 := by lia
      exact PosComboRealRooted.prec_or_revPrec_of_same_degree_one (by lia) hf_deg1

/-- Therefore every positive-leading pair of degree at most one already
satisfies the all-combinations conclusion. -/
theorem allComboRealRooted_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    AllComboRealRooted f g := by
  rcases
      prec_or_revPrec_of_natDegree_le_one
        hf_pos hg_pos hf_deg_le_one hg_deg_le_one with hprec | hprec
  · exact allComboRealRooted_of_prec hprec
  · exact allComboRealRooted_comm (allComboRealRooted_of_prec hprec)

/-- Two-polynomial common-interleaver endpoint in degree at most one. This is
the direct pair version used by the low-degree Chudnovsky--Seymour package. -/
theorem pairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rcases
      prec_or_revPrec_of_natDegree_le_one
        hf_pos hg_pos hf_deg_le_one hg_deg_le_one with hprec | hprec
  · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
  · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩

/-- A symmetric `Prec` orientation immediately gives a common right
interleaver: use the larger polynomial in the chosen orientation as the
witness. -/
theorem pairHasCommonInterleaver_of_prec_or_revPrec
    {f g : ℝ[X]} :
    Prec f g ∨ Prec g f →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  intro hprec_or
  rcases hprec_or with hprec | hprec
  · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
  · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩

/-- Same-degree specialization of the low-degree pair endpoint. -/
theorem pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one (by lia)

/-- Compatibility-level version of the low-degree common-interleaver endpoint.
In degree at most one the common interleaver exists without using the
compatibility hypothesis, but keeping it in the statement makes this theorem a
drop-in two-polynomial bridge. -/
theorem compatiblePairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Same-degree branch of the honest no-common target is already unconditional
through degree one. -/
theorem posComboNoCommonSameDegreeOrientationAlternative_of_degree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    Prec f g ∨ Prec g f :=
  prec_or_revPrec_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one (by lia)

/-- Degree-one base case for the honest same-degree branch: equal-degree linear
pairs automatically satisfy the Obreschkoff alternative. This is a reusable
base case for future same-degree no-common work. -/
theorem posComboNoCommonSameDegreeOrientationAlternative_of_degree_one
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg1 : f.natDegree = 1) :
    Prec f g ∨ Prec g f :=
  PosComboRealRooted.prec_or_revPrec_of_same_degree_one hdeg hf_deg1

/-- The old same-degree orientation alternative, when available, still feeds
the repaired same-degree common-interleaver target. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_rr : (f ≠ 0 ∧ f.Splits) :=
      PosComboRealRooted.isRealRooted_left_of_sameDegree hfg hf_pos hg_pos hdeg
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
      PosComboRealRooted.isRealRooted_right_of_sameDegree hfg hf_pos hg_pos hdeg
  have hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f)
            ⟨j, by simpa [rootSeqDesc_length hf_rr.2] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [rootSeqDesc_length hg_rr.2] using this⟩).Nonempty := by
    rcases hsame hf_pos hg_pos hfnn hgnn hfg hdeg hno with hprec | hprec
    · intro j hj
      have hjg : j < g.natDegree + 1 := by lia
      exact
        rootSlotInterval_inter_nonempty_of_commonInterleaver hprec
          (prec_refl hprec.2.1.1 hprec.2.1.2) j
          (by lia)
          (by lia)
    · intro j hj
      have hjg : j < g.natDegree + 1 := by lia
      exact
        rootSlotInterval_inter_nonempty_of_commonInterleaver
          (prec_refl hprec.2.1.1 hprec.2.1.2) hprec
          j
          (by lia)
          (by lia)
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hdeg hslot

/-- Low-degree base case for the repaired same-degree no-common target.  Through
degree one, the common-right-interleaver conclusion is unconditional once the
two polynomials have positive leading coefficients and equal degree. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaver_of_degree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
    hf_pos hg_pos hdeg hf_deg_le_one

/-- Succ-degree branch of the honest no-common target is already unconditional
in the constant-vs-linear endpoint case. -/
theorem posComboNoCommonSuccDegreeOrientation_of_degree_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    Prec f g := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_deg_zero hf0 hf_deg0
  have hg_deg1 : g.natDegree = 1 := by lia
  have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg1
  exact prec_degree_zero_right_of_degree_one hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_deg0 hg_deg1

/-- Any proof of the stronger fixed-orientation succ-degree statement can be
used immediately as input for the corrected succ-degree pair bridge. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_orientation_nonneg
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hprec : Prec f g := horient hf_pos hg_pos hfnn hgnn hfg hsucc hno
  exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩

/-- The corrected succ-degree pair bridge is already unconditional in the
constant-vs-linear endpoint case. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_degree_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hprec : Prec f g :=
    posComboNoCommonSuccDegreeOrientation_of_degree_zero
      hf_pos hg_pos hf_deg0 hsucc
  exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩

/-- Degree-one left-hand endpoint of the corrected succ-degree branch under
the affine-family bridge.  The public affine-family degree-one lemma gives the
stronger right-pair orientation `g ≪ X * f`, so `X * f` is the required common
right interleaver. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily_degree_one
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hf_deg1 : f.natDegree = 1)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits) := by
    intro s t hs ht
    exact
      haffBridge hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno hs ht
  have hright : Prec g (X * f) :=
    prec_right_pair_of_affine_family_nonneg_degree_one
      hf0 hg0 hfnn hgnn haff hf_deg1
  exact pairHasCommonInterleaver_of_prec_right_pair_nonneg hright hfnn

/-- The affine-family bridge proves the full corrected succ-degree
common-right-interleaver branch.  The affine-family right-pair theorem gives
`g ≪ X * f`, so `X * f` is a common right interleaver. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits) := by
    intro s t hs ht
    exact
      haffBridge hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno hs ht
  have hright : Prec g (X * f) :=
    prec_right_pair_of_affine_family_nonneg
      hf0 hg0 hfnn hgnn haff
  exact pairHasCommonInterleaver_of_prec_right_pair_nonneg hright hfnn

/-- Any no-common orientation core already contains the honest same-degree
branch in the nonnegative regime: one simply specializes the degree bounds to
equality. -/
theorem posComboNoCommonSameDegreeOrientationAlternative_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement :=
  fun {_ _} hf_pos hg_pos _ _ hfg hdeg hno =>
    hstep hfg hf_pos hg_pos (by lia) (by lia) hno

/-- In the succ-degree branch, any no-common orientation core automatically
forces the forward orientation by degree, so it also packages the honest
succ-degree orientation statement. -/
theorem posComboNoCommonSuccDegreeOrientation_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonSuccDegreeOrientationNonnegStatement := by
  intro f g hf_pos hg_pos _ _ hfg hsucc hno
  have hprec_or : Prec f g ∨ Prec g f :=
    hstep hfg hf_pos hg_pos (by lia) (by lia) hno
  exact prec_forward_of_orientation_of_succDegree hsucc hprec_or

/-- Consequently, any proof of the older no-common orientation core can be fed
directly into the corrected succ-degree common-interleaver bridge. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_orientation_nonneg
    (posComboNoCommonSuccDegreeOrientation_of_noCommonOrientation hstep)

/-- **Honest missing root-slot boundary for milestone B1 (#41).**

This is the same-degree analogue of
`PosComboNoCommonSuccDegreeSlotDataNonnegStatement`.  For a nonnegative
positive-combination pair with no common roots and `g.natDegree = f.natDegree`,
it packages the remaining converse-Obreschkoff content as nonempty
intersections of matching descending root-slot intervals.

The real-rootedness of `f` and `g` is not bundled here because it is already
available from the same-degree `PosComboRealRooted` lemmas. -/
def PosComboNoCommonSameDegreeSlotDataNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty

/-- **Checked reduction of #41 to the same-degree root-slot boundary.**

The repaired same-degree common-right-interleaver endpoint follows from the
matching slot-intersection condition via the constructive slot theorem in
`CommonInterleaverSeq`. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_slotData
    (hstmt : PosComboNoCommonSameDegreeSlotDataNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_rr : f ≠ 0 ∧ f.Splits :=
    PosComboRealRooted.isRealRooted_left_of_sameDegree hfg hf_pos hg_pos hdeg
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    PosComboRealRooted.isRealRooted_right_of_sameDegree hfg hf_pos hg_pos hdeg
  refine
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hdeg ?_
  intro j hj
  exact hstmt hf_pos hg_pos hfnn hgnn hfg hdeg hno j hj _ _

/-- **Honest missing root-slot boundary for milestone B2 (#42).**

This is the succ-degree analogue of the same-degree slot-intersection input
used for #41.  For a nonnegative positive-combination pair with no common
roots and `g.natDegree = f.natDegree + 1`, it packages the two remaining
pieces of the remaining converse-Obreschkoff content:

* real-rootedness of the lower-degree member `f`, and
* the descending root-slot intervals of `f` and `g` meet in each of the
  `f.natDegree + 1` common slots.

The right endpoint `g` is now supplied by
`PosComboRealRooted.isRealRooted_right_of_succDegree`.
The `Fin` bounds are threaded as explicit hypotheses so no in-type proof
obligations remain. -/
def PosComboNoCommonSuccDegreeSlotDataNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty

/-- **Checked reduction of #42 to the root-slot boundary.**

The corrected succ-degree common-right-interleaver endpoint follows from the
precise root-slot condition `PosComboNoCommonSuccDegreeSlotDataNonnegStatement`
via the constructive slot theorem.  This mirrors the same-degree slot boundary
route for #41. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_slotData
    (hstmt : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  obtain ⟨hf_rr, hslot⟩ := hstmt hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hsucc
  refine
    pairHasCommonInterleaver_of_succDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hsucc ?_
  intro j hj
  exact hslot j hj _ _

/-- Honest nonnegative degree-split reduction of the no-common orientation
problem: it is enough to solve the same-degree branch up to orientation
alternative and the succ-degree branch in the forced direction. -/
theorem posComboNoCommonOrientation_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  rcases hdeg with hsame_deg | hsucc_deg
  · exact hsame hf_pos hg_pos hfnn hgnn hfg hsame_deg hno
  · exact Or.inl (hsucc hf_pos hg_pos hfnn hgnn hfg hsucc_deg hno)

/-- The same honest degree-split reduction also packages the no-common
all-combinations bridge in the nonnegative regime. -/
theorem allComboRealRooted_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g := by
  rcases
      posComboNoCommonOrientation_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
      with hprec | hprec
  · exact allComboRealRooted_of_prec hprec
  · exact allComboRealRooted_comm (allComboRealRooted_of_prec hprec)

/-- Affine-family bridge upgraded to the all-combinations conclusion in the
nonnegative-coefficient regime, via `AffineFamily.allComboRealRooted_of_affine_family_nonneg`.
-/
theorem allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits) := by
    intro s t hs ht
    exact haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hs ht
  exact
    allComboRealRooted_of_affine_family_nonneg
      hf0 hg0 hfnn hgnn haff

/-- The same affine-family bridge also yields the no-common orientation step,
since `AllComboRealRooted` can be fed into the completed Obreschkoff converse.
-/
theorem posComboNoCommonOrientation_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hf_rr : (f ≠ 0 ∧ f.Splits) := allComboRealRooted_left_rr hall hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := allComboRealRooted_right_rr hall hg0
  have hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by lia
  exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg

private lemma hasNonnegCoeffs_quotient_add_right_of_common_root
    {f g qf qg : ℝ[X]} {r μ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hqf : f = (X - C r) * qf)
    (hqg : g = (X - C r) * qg)
    (hμ : 0 < μ) :
    HasNonnegCoeffs (qf + C μ * qg) := by
  let p : ℝ[X] := f + C μ * g
  have hp_rr : (p ≠ 0 ∧ p.Splits) := by
    simpa [p] using hfg.isRealRooted_add_right hμ
  have hp_nn : HasNonnegCoeffs p := by
    dsimp [p]
    exact hfnn.add (nonnegCoeffs_C_mul hμ.le hgnn)
  have hp_eq : p = (X - C r) * (qf + C μ * qg) := by grind
  have hq_ne : qf + C μ * qg ≠ 0 := by simp_all
  have hq_rr : ((qf + C μ * qg) ≠ 0 ∧ (qf + C μ * qg).Splits) :=
    isRealRooted_of_dvd hp_rr.1 hp_rr.2 hq_ne
      ⟨X - C r, by grind⟩
  have hp_pos : HasPosLeadingCoeff p := hp_nn.pos_leadingCoeff hp_rr.1
  have hq_pos : HasPosLeadingCoeff (qf + C μ * qg) :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hp_eq] using hp_pos)
  exact
    hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
      hp_rr.1 hp_rr.2 hp_nn hq_rr.1 hq_rr.2 hq_pos
      ⟨X - C r, by grind⟩

private lemma common_root_reduction_data_of_posCombo_nonneg
    {f g : ℝ[X]} {r : ℝ}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hrf : f.IsRoot r)
    (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      PosComboRealRooted qf qg ∧
      HasNonnegCoeffs qf ∧
      HasNonnegCoeffs qg ∧
      qf ≠ 0 ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qf ∧
      HasPosLeadingCoeff qg ∧
      qf.natDegree ≤ qg.natDegree ∧
      qg.natDegree ≤ qf.natDegree + 1 := by
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  have hqfg : PosComboRealRooted qf qg :=
    PosComboRealRooted.of_mul_X_sub_C (r := r) (by lia)
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hqf0 : qf ≠ 0 := by simp_all
  have hqg0 : qg ≠ 0 := by simp_all
  have hqf_nn : HasNonnegCoeffs qf := by
    refine coeff_nonneg_of_add_C_mul_nonneg_forall (f := qf) (g := qg) ?_
    intro μ hμ
    exact
      hasNonnegCoeffs_quotient_add_right_of_common_root
        hfg hfnn hgnn hqf hqg hμ
  have hqg_nn : HasNonnegCoeffs qg := by
    refine coeff_nonneg_of_add_C_mul_nonneg_forall (f := qg) (g := qf) ?_
    intro μ hμ
    simpa [add_comm] using
      hasNonnegCoeffs_quotient_add_right_of_common_root
        (f := g) (g := f) (qf := qg) (qg := qf) (r := r)
        (PosComboRealRooted.comm hfg) hgnn hfnn hqg hqf hμ
  have hqf_pos : HasPosLeadingCoeff qf := hqf_nn.pos_leadingCoeff hqf0
  have hqg_pos : HasPosLeadingCoeff qg := hqg_nn.pos_leadingCoeff hqg0
  have hqdeg_lo : qf.natDegree ≤ qg.natDegree := by
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg0, natDegree_X_sub_C] at hdeg_lo
    lia
  have hqdeg_hi : qg.natDegree ≤ qf.natDegree + 1 := by
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg0, natDegree_X_sub_C] at hdeg_hi
    lia
  simp_all

/-- Honest no-common degree-split reduction of the common-interleaver bridge
in the nonnegative regime: the same-degree branch only needs the Obreschkoff
alternative, while the succ-degree branch only asks for a common interleaver.
-/
theorem posComboNoCommonPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  rcases hdeg with hsame_deg | hsucc_deg
  · rcases hsame hf_pos hg_pos hfnn hgnn hfg hsame_deg hno with hprec | hprec
    · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
    · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩
  · exact hsucc hf_pos hg_pos hfnn hgnn hfg hsucc_deg hno

/-- Repaired no-common degree-split reduction of the common-interleaver bridge
in the nonnegative regime: both same-degree and succ-degree branches are stated
directly with the common-right-interleaver conclusion needed downstream. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  rcases hdeg with hsame_deg | hsucc_deg
  · exact hsame hf_pos hg_pos hfnn hgnn hfg hsame_deg hno
  · exact hsucc hf_pos hg_pos hfnn hgnn hfg hsucc_deg hno

/-- Repaired no-common degree-split reduction with the succ-degree branch
discharged by the affine-family bridge.  After this reduction, the only
remaining local branch is the same-degree common-interleaver statement. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno

private theorem posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs_ordered
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          ∃ h : ℝ[X], Prec f h ∧ Prec g h)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact
      posComboNoCommonPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    rcases
        ih qf.natDegree hqf_deg_lt rfl
          hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi with
      ⟨h, hqf_prec, hqg_prec⟩
    refine ⟨(X - C r) * h, ?_, ?_⟩
    · simpa [hqf] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqf_prec
    · simpa [hqg] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqg_prec

private theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs_ordered
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          ∃ h : ℝ[X], Prec f h ∧ Prec g h)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact
      posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    rcases
        ih qf.natDegree hqf_deg_lt rfl
          hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi with
      ⟨h, hqf_prec, hqg_prec⟩
    refine ⟨(X - C r) * h, ?_, ?_⟩
    · simpa [hqf] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqf_prec
    · simpa [hqg] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqg_prec

private theorem allComboRealRooted_of_degreeSplit_and_nonnegCoeffs_ordered
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact
      allComboRealRooted_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    have hall_q : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl
        hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi
    have hall_mul : AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hall_q
    lia

/-- Recursive upgrade of the honest degree-split no-common package to a full
all-combinations result in the nonnegative-coefficient regime. Shared roots are
factored out until one reaches the terminal no-common quotient, where the
same-degree alternative or succ-degree orientation hypothesis is applied. -/
theorem allComboRealRooted_of_posCombo_and_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · exact
      allComboRealRooted_of_degreeSplit_and_nonnegCoeffs_ordered
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg hclose.2
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hall' : AllComboRealRooted g f :=
      allComboRealRooted_of_degreeSplit_and_nonnegCoeffs_ordered
        hsame hsucc hg_pos hf_pos hgnn hfnn
        (PosComboRealRooted.comm hfg) hdeg' hclose.1
    exact allComboRealRooted_comm hall'

/-- The honest degree-split package therefore yields the full Obreschkoff
orientation alternative for every positive-combination pair with nonnegative
coefficients, not just in the terminal no-common case. -/
theorem posComboOrientation_of_posCombo_and_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    Prec f g ∨ Prec g f := by
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_posCombo_and_degreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn hfg
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hf_rr : (f ≠ 0 ∧ f.Splits) := allComboRealRooted_left_rr hall hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := allComboRealRooted_right_rr hall hg0
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · have hdeg' : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by
      lia
    exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg'
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hdeg'' : g.natDegree + 1 = f.natDegree ∨ g.natDegree = f.natDegree := by lia
    have hprec' : Prec g f ∨ Prec f g :=
      prec_of_allComboRealRooted hg_rr.1 hg_rr.2 hf_rr.1 hf_rr.2
        (allComboRealRooted_comm hall) hdeg''
    lia

private theorem allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs_ordered
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact
      allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs
        haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    have hall_q : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl
        hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi
    have hall_mul : AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hall_q
    lia

/-- Recursive upgrade of the affine-family no-common bridge to a full
all-combinations result in the nonnegative-coefficient regime. Shared roots are
factored out using the positive-combination recursion, and the bridge is only
used at the terminal no-common quotient. -/
theorem allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · exact
      allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs_ordered
        haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg hclose.2
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hall' : AllComboRealRooted g f :=
      allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs_ordered
        haffBridge hg_pos hf_pos hgnn hfnn (PosComboRealRooted.comm hfg)
        hdeg' hclose.1
    exact allComboRealRooted_comm hall'

/-- The affine-family bridge therefore yields the full Obreschkoff orientation
alternative for every positive-combination pair with nonnegative coefficients,
not just the no-common case. -/
theorem posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    Prec f g ∨ Prec g f := by
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hf_rr : (f ≠ 0 ∧ f.Splits) := allComboRealRooted_left_rr hall hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := allComboRealRooted_right_rr hall hg0
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · have hdeg' : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by
      lia
    exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg'
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hdeg'' : g.natDegree + 1 = f.natDegree ∨ g.natDegree = f.natDegree := by lia
    have hprec' : Prec g f ∨ Prec f g :=
      prec_of_allComboRealRooted hg_rr.1 hg_rr.2 hf_rr.1 hf_rr.2
        (allComboRealRooted_comm hall) hdeg''
    lia

/-- The boundary-right-pair orientation statement already yields the full
all-combinations conclusion in the nonnegative-coefficient regime, by first
recovering the affine-family hypothesis and then running the common-root
recursion packaged above. -/
theorem allComboRealRooted_of_posCombo_and_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg

/-- Consequently, the same boundary-right-pair orientation input already gives
the full Obreschkoff orientation alternative for every positive-combination
pair with nonnegative coefficients. -/
theorem posComboOrientation_of_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    Prec f g ∨ Prec g f :=
  posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg

/-- The stronger boundary-right-pair hypothesis already contains the honest
same-degree no-common branch in the nonnegative regime. -/
theorem
    boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement :=
  fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg hno =>
    posComboNoCommonOrientation_of_affineFamilyBridge_and_nonnegCoeffs
      (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
      hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno

/-- The stronger boundary-right-pair hypothesis also contains the corrected
succ-degree common-interleaver branch in the nonnegative regime. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hprec_or :
      Prec f g ∨ Prec g f :=
    posComboNoCommonOrientation_of_affineFamilyBridge_and_nonnegCoeffs
      (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
      hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno
  have hprec_fg : Prec f g :=
    prec_forward_of_orientation_of_succDegree hsucc hprec_or
  exact ⟨g, hprec_fg, prec_refl hprec_fg.2.1.1 hprec_fg.2.1.2⟩

/-- Reduction of no-common orientation to the all-combinations bridge plus
Obreschkoff converse (`prec_of_allComboRealRooted`). -/
theorem posComboNoCommonOrientation_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PosComboNoCommonOrientationStatement := by
  intro f g hfg hf_pos hg_pos hdeg_lo hdeg_hi hno
  have hall : AllComboRealRooted f g :=
    hallBridge hf_pos hg_pos hfg hdeg_lo hdeg_hi hno
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hf_rr : (f ≠ 0 ∧ f.Splits) := allComboRealRooted_left_rr hall hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := allComboRealRooted_right_rr hall hg0
  have hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by lia
  exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg

/-- Converse reduction: the no-common orientation core immediately yields the
all-combinations bridge by passing through `allComboRealRooted_of_prec`. -/
theorem posComboAllComboBridge_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonToAllComboBridgeStatement := by
  intro f g hf_pos hg_pos hfg hdeg_lo hdeg_hi hno
  rcases hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno with hprec | hprec
  · exact allComboRealRooted_of_prec hprec
  · exact allComboRealRooted_comm (allComboRealRooted_of_prec hprec)

/-- The two no-common bridge formulations are equivalent:
orientation (`Prec f g ∨ Prec g f`) and all-combinations real-rootedness. -/
theorem posComboNoCommonBridge_iff_orientation :
    PosComboNoCommonToAllComboBridgeStatement ↔
      PosComboNoCommonOrientationStatement := by
  constructor
  · exact posComboNoCommonOrientation_of_allComboBridge
  · exact posComboAllComboBridge_of_noCommonOrientation

/-- Reduction of the two-polynomial bridge to an orientation theorem for the
positive-combination cone. If one can show `Prec f g ∨ Prec g f` for every
positive-leading `PosComboRealRooted` pair, then compatibility gives a common
right interleaver immediately. -/
theorem compatiblePairHasCommonInterleaver_of_posComboOrientation
    (horient :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        Prec f g ∨ Prec g f) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  rcases horient hf_pos hg_pos
      (Compatible.toPosComboRealRooted hfg hf_pos hg_pos) with hprec | hprec
  · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
  · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩

/-- Compatibility-to-common-interleaver reduction through the positive-combo
bridge. -/
theorem compatiblePairHasCommonInterleaver_of_posComboPair
    (hposCombo : PosComboPairHasCommonInterleaverStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  fun {_ _} hf_pos hg_pos hfg =>
    hposCombo hf_pos hg_pos
      (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- If one has both the no-common-roots orientation core and degree closeness
for `PosComboRealRooted` pairs, then every positive-leading `PosComboRealRooted`
pair has a common right interleaver. -/
theorem posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    PosComboPairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 := hdegClose hfg
  by_cases hfg_deg : f.natDegree ≤ g.natDegree
  · have hprec_or : Prec f g ∨ Prec g f :=
      PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        hfg hf_pos hg_pos hfg_deg hclose.2
    rcases hprec_or with hprec | hprec
    · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
    · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩
  · have hgf_deg : g.natDegree ≤ f.natDegree := le_of_not_ge hfg_deg
    have hprec_or : Prec g f ∨ Prec f g :=
      PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        (PosComboRealRooted.comm hfg) hg_pos hf_pos hgf_deg hclose.1
    rcases hprec_or with hprec | hprec
    · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩
    · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩

/-- Pair-bridge reduction through the all-combinations bridge and a separate
degree-closeness input. -/
theorem posComboPairHasCommonInterleaver_of_allComboBridge_and_degreeClose
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    PosComboPairHasCommonInterleaverStatement :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hdegClose

/-- Degree-closeness specialization with nonnegative coefficients. -/
theorem posComboNatDegreeClose_of_nonnegCoeffs
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 :=
  natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
    hfg (HasPosLeadingCoeff.ne_zero hf_pos)
    (HasPosLeadingCoeff.ne_zero hg_pos) hfnn hgnn

/-- In the nonnegative-coefficient regime, the no-common-roots orientation
core already implies the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (hstep : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    posComboNatDegreeClose_of_nonnegCoeffs hf_pos hg_pos hfnn hgnn hfg
  by_cases hfg_deg : f.natDegree ≤ g.natDegree
  · have hprec_or : Prec f g ∨ Prec g f :=
      PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        hfg hf_pos hg_pos hfg_deg hclose.2
    rcases hprec_or with hprec | hprec
    · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
    · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩
  · have hgf_deg : g.natDegree ≤ f.natDegree := le_of_not_ge hfg_deg
    have hprec_or : Prec g f ∨ Prec f g :=
      PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        (PosComboRealRooted.comm hfg) hg_pos hf_pos hgf_deg hclose.1
    rcases hprec_or with hprec | hprec
    · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩
    · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩

/-- In the nonnegative-coefficient regime, the all-combinations bridge implies
the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- In the nonnegative-coefficient regime, the affine-family bridge already
implies the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rcases
      posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
        haffBridge hf_pos hg_pos hfnn hgnn hfg with hprec | hprec
  · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
  · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩

/-- The boundary-right-pair orientation statement therefore already yields the
full positive-combo pair bridge in the nonnegative-coefficient regime. -/
theorem posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rcases
      posComboOrientation_of_boundaryRightPairOrientation_and_nonnegCoeffs
        hboundary hf_pos hg_pos hfnn hgnn hfg with hprec | hprec
  · exact ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩
  · exact ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩

/-- The honest degree-split package also yields the full positive-combo pair
bridge in the nonnegative-coefficient regime. -/
theorem posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · exact
      posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs_ordered
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg hclose.2
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    rcases
        posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs_ordered
          hsame hsucc hg_pos hf_pos hgnn hfnn
          (PosComboRealRooted.comm hfg) hdeg' hclose.1 with
      ⟨h, hg_prec, hf_prec⟩
    grind

/-- Repaired degree-split package for the full positive-combo pair bridge in
the nonnegative-coefficient regime. This is the version to use after the
same-degree orientation alternative is replaced by a common-interleaver target.
-/
theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf0 : f ≠ 0 := HasPosLeadingCoeff.ne_zero hf_pos
  have hg0 : g ≠ 0 := HasPosLeadingCoeff.ne_zero hg_pos
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · exact
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs_ordered
        hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg hclose.2
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    rcases
        posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs_ordered
          hsame hsucc hg_pos hf_pos hgnn hfnn
          (PosComboRealRooted.comm hfg) hdeg' hclose.1 with
      ⟨h, hg_prec, hf_prec⟩
    grind

/-- Full positive-combo pair bridge in the nonnegative-coefficient regime,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem posComboPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility-to-common-interleaver bridge under no-common orientation and
nonnegative coefficients. -/
theorem compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (hstep : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    hstep hf_pos hg_pos hfnn hgnn
    (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Compatibility bridge under nonnegative coefficients, reduced to the
all-combinations bridge. -/
theorem compatiblePairHasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
affine-family bridge. -/
theorem compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    haffBridge hf_pos hg_pos hfnn hgnn
    (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Compatibility bridge under nonnegative coefficients, reduced to the
boundary-right-pair orientation statement. -/
theorem compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    hboundary hf_pos hg_pos hfnn hgnn
    (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Compatibility bridge under nonnegative coefficients, reduced to the honest
degree-split package. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    hsame hsucc hf_pos hg_pos hfnn hgnn
    (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Compatibility bridge under nonnegative coefficients, reduced to the
repaired degree-split package with common-interleaver conclusions in both
branches. -/
theorem compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    hsame hsucc hf_pos hg_pos hfnn hgnn
    (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Compatibility bridge in the nonnegative-coefficient regime, using the
repaired same-degree branch and the affine-family bridge for the succ-degree
branch. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    hsame haffBridge hf_pos hg_pos hfnn hgnn
    (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

private theorem posComboPairHasCommonInterleaver_via_nonnegShift
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hNonneg :
      ∀ {F G : ℝ[X]},
        HasPosLeadingCoeff F →
        HasPosLeadingCoeff G →
        HasNonnegCoeffs F →
        HasNonnegCoeffs G →
        PosComboRealRooted F G →
        ∃ h : ℝ[X], Prec F h ∧ Prec G h) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by
    simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by
    simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_rr_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_rr_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  rcases hNonneg hf'_pos hg'_pos hfnn hgnn hfg' with
    ⟨h', hf'h', hg'h'⟩
  let h : ℝ[X] := h'.comp (X - C r)
  have hh_comp : h.comp (X + C r) = h' := by
    simp [h, Polynomial.comp_assoc, sub_eq_add_neg, add_assoc, add_comm]
  have hfh : Prec f h := by
    have htranslated : Prec f' (h.comp (X + C r)) := by lia
    exact (prec_comp_X_add_C_iff (f := f) (g := h) r).1 htranslated
  have hgh : Prec g h := by
    have htranslated : Prec g' (h.comp (X + C r)) := by lia
    exact (prec_comp_X_add_C_iff (f := g) (g := h) r).1 htranslated
  grind

/-- Translation reduces the full positive-leading compatibility bridge to the
nonnegative-coefficient degree-split package: shift both polynomials far enough
to the right so all roots become nonpositive, apply the nonnegative theorem,
then translate the common interleaver back. -/
theorem posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  exact posComboPairHasCommonInterleaver_via_nonnegShift
    _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg
    (fun {F G} hF_pos hG_pos hFnn hGnn hFG =>
      posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc (f := F) (g := G) hF_pos hG_pos hFnn hGnn hFG)

/-- Translation reduces the full positive-leading compatibility bridge to the
repaired nonnegative-coefficient degree-split package.  This is the shifted
version whose same-degree input already has the common-right-interleaver
conclusion, rather than the stronger orientation alternative. -/
theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  exact posComboPairHasCommonInterleaver_via_nonnegShift
    _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg
    (fun {F G} hF_pos hG_pos hFnn hGnn hFG =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc (f := F) (g := G) hF_pos hG_pos hFnn hGnn hFG)

/-- Translation reduces the full positive-leading compatibility bridge to the
nonnegative-coefficient degree-split package: shift both polynomials far enough
to the right so all roots become nonpositive, apply the nonnegative theorem,
then translate the common interleaver back. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hf_rr : (f ≠ 0 ∧ f.Splits) := Compatible.isRealRooted_left hfg hf_pos
  have hg_rr : (g ≠ 0 ∧ g.Splits) := Compatible.isRealRooted_right hfg hg_pos
  exact
    posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
      hsame hsucc hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_pos hg_pos
      (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Shifted compatibility bridge using the repaired same-degree
common-interleaver branch directly. -/
theorem compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hf_rr : (f ≠ 0 ∧ f.Splits) := Compatible.isRealRooted_left hfg hf_pos
  have hg_rr : (g ≠ 0 ∧ g.Splits) := Compatible.isRealRooted_right hfg hg_pos
  exact
    posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      hsame hsucc hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_pos hg_pos
      (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Shifted positive-leading compatibility bridge with the succ-degree branch
discharged by the affine-family bridge.  This leaves only the same-degree
orientation alternative as an external hypothesis. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Shifted positive-leading compatibility bridge with the succ-degree branch
discharged by the affine-family bridge and the same-degree branch stated in the
repaired common-right-interleaver form. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- The stronger boundary-right-pair orientation hypothesis already finishes
the positive-leading positive-combination bridge after the nonnegative shift
reduction, provided the summands are individually real-rooted. -/
theorem posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits) (hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hsame_nonneg :
      PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement :=
    boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary
  have hsucc_nonneg :
      PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
    succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
      hboundary
  exact
    posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
      hsame_nonneg hsucc_nonneg
      hf_rr_ne hf_rr_splits hg_rr_ne hg_rr_splits hf_pos hg_pos hfg

/-- The stronger boundary-right-pair orientation hypothesis already finishes
the full positive-leading compatibility bridge after the nonnegative shift
reduction. -/
theorem compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hf_rr : (f ≠ 0 ∧ f.Splits) := Compatible.isRealRooted_left hfg hf_pos
  have hg_rr : (g ≠ 0 ∧ g.Splits) := Compatible.isRealRooted_right hfg hg_pos
  exact
    posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
      hboundary hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_pos hg_pos
      (Compatible.toPosComboRealRooted hfg hf_pos hg_pos)

/-- Compatibility-to-common-interleaver bridge from the reduced positive-combo
ingredients (no-common orientation + degree closeness). -/
theorem compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_posComboPair
    (posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
      hstep hdegClose)

/-- Pairwise upgrade using the natural positive-leading two-polynomial bridge. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonInterleaverStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

/-- Pairwise upgrade using the honest same-degree/succ-degree compatibility
split. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_degreeSplit hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from the nonnegative-coefficient degree-split package,
after shifting each pair into the nonnegative regime. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift hsame hsucc)
    hpos hpair

/-- Pairwise upgrade after the nonnegative shift reduction, with the
succ-degree branch discharged by the affine-family bridge. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
      hsame haffBridge)
    hpos hpair

/-- Pairwise upgrade from the boundary-right-pair hypothesis after shifting
each pair into the nonnegative regime. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_boundaryRightPairOrientation
    {fs : List ℝ[X]}
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
      hboundary)
    hpos hpair

private theorem pairwiseHasCommonInterleaver_of_nonnegPairBridge
    {fs : List ℝ[X]}
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        Compatible f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    hbridge
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hnn (fs.get i) (List.get_mem _ _))
      (hnn (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
no-common-roots orientation core. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hstep : PosComboNoCommonOrientationStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg =>
      compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
        hstep (f := f) (g := g) hf_pos hg_pos hfnn hgnn hfg)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the honest
degree-split package. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg =>
      compatiblePairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc (f := f) (g := g) hf_pos hg_pos hfnn hgnn hfg)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the repaired
degree-split package. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg =>
      compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc (f := f) (g := g) hf_pos hg_pos hfnn hgnn hfg)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime, using the repaired
same-degree branch and the affine-family bridge for the succ-degree branch. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg =>
      compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
        hsame haffBridge (f := f) (g := g) hf_pos hg_pos hfnn hgnn hfg)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
affine-family bridge. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg =>
      compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
        haffBridge (f := f) (g := g) hf_pos hg_pos hfnn hgnn hfg)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
boundary-right-pair orientation statement. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_boundaryRightPairOrientation_nonneg
    {fs : List ℝ[X]}
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg =>
      compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
        hboundary (f := f) (g := g) hf_pos hg_pos hfnn hgnn hfg)
    hpos hnn hpair

/-- A single common right interleaver is in particular a pairwise common right
interleaver witness. -/
theorem pairwiseHasCommonInterleaver_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs) :
    PairwiseHasCommonInterleaver fs := by
  rcases hcommon with ⟨h, hprec⟩
  intro i j hij
  exact ⟨h,
    hprec (fs.get i) (List.get_mem _ _),
    hprec (fs.get j) (List.get_mem _ _)⟩

/-- A single common left interleaver is in particular a pairwise common left
interleaver witness. -/
theorem pairwiseHasCommonLeftInterleaver_of_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs) :
    PairwiseHasCommonLeftInterleaver fs := by
  rcases hcommon with ⟨h, hprec⟩
  intro i j hij
  exact ⟨h,
    hprec (fs.get i) (List.get_mem _ _),
    hprec (fs.get j) (List.get_mem _ _)⟩

/-- A common right interleaver yields full family compatibility for all
nonnegative weighted sums. -/
theorem familyCompatible_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    FamilyCompatible fs := by
  rcases hcommon with ⟨h, hprec⟩
  intro l hmem hnonneg
  by_cases hex : ∃ ap ∈ l, 0 < ap.1
  · right
    have hprec_l : ∀ ap ∈ l, Prec ap.2 h := by grind
    have hpos_l : ∀ ap ∈ l, HasPosLeadingCoeff ap.2 := by grind
    exact (prec_weightedSum_right l h hnonneg hprec_l hpos_l hex).1
  · left
    have hall_zero : ∀ ap ∈ l, ap.1 = 0 := by grind
    exact weightedSum_eq_zero_of_forall_coeff_zero l hall_zero

/-- Full family compatibility implies pairwise compatibility by specializing to
two-term weighted sums. -/
theorem pairwiseCompatible_of_familyCompatible
    {fs : List ℝ[X]}
    (hfull : FamilyCompatible fs) :
    PairwiseCompatible fs := by
  intro i j hij α β hα hβ
  let fi : ℝ[X] := fs.get i
  let fj : ℝ[X] := fs.get j
  have hpair :
      weightedSum [(α, fi), (β, fj)] = 0 ∨
        ((weightedSum [(α, fi), (β, fj)]) ≠ 0 ∧
          (weightedSum [(α, fi), (β, fj)]).Splits) :=
    hfull [(α, fi), (β, fj)] (by grind) (by simp_all)
  simpa [fi, fj, weightedSum, weightedSum_cons] using hpair

private theorem chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (h12 : PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  have h23 : PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs := by
    constructor
    · exact hasCommonInterleaver_of_pairwiseHasCommonInterleaver (fun f hf => (hrr f hf).2) hpos
    · exact pairwiseHasCommonInterleaver_of_commonInterleaver
  have h34 : HasCommonInterleaver fs ↔ FamilyCompatible fs := by
    constructor
    · intro hcommon
      exact familyCompatible_of_commonInterleaver hcommon hpos
    · intro hfull
      exact h23.1 (h12.1 (pairwiseCompatible_of_familyCompatible hfull))
  exact ⟨h12, h23, h34⟩

private theorem chudnovskySeymour_fourWay_of_pairwiseCommonForward
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hforward : PairwiseCompatible fs → PairwiseHasCommonInterleaver fs) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  refine chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon hrr hpos ?_
  exact ⟨hforward, fun hpair => pairwiseCompatible_of_pairwiseHasCommonInterleaver hpair hpos⟩

/-- Chudnovsky--Seymour four-way package in the finite-list language used in
this project, with the two-polynomial converse isolated as hypothesis:

1. pairwise compatibility,
2. pairwise common right interleavers,
3. a global common right interleaver,
4. full nonnegative family compatibility. -/
theorem chudnovskySeymour_fourWay_of_pairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : ∀ ⦃f g : ℝ[X]⦄, Compatible f g → ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible htwo

/-- Chudnovsky--Seymour four-way package with the natural two-polynomial bridge
assumption (requiring positive leading coefficients on the pair). -/
theorem chudnovskySeymour_fourWay_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos htwo hpos

/-- Four-way Chudnovsky--Seymour package from the honest same-degree/succ-degree
compatibility split. -/
theorem chudnovskySeymour_fourWay_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_degreeSplit hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the nonnegative-coefficient
degree-split package, upgraded to arbitrary positive-leading families by a
common translation trick applied pairwise. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift hsame hsucc)

/-- Four-way Chudnovsky--Seymour package after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
    (fs := fs) hrr hpos hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Four-way Chudnovsky--Seymour package from the stronger boundary-right-pair
statement, upgraded to arbitrary positive-leading families by the shift
reduction. -/
theorem chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
      hboundary)

/-- Same four-way Chudnovsky--Seymour package, with assumptions phrased via the
positive-combination two-polynomial bridge. -/
theorem chudnovskySeymour_fourWay_of_posComboBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hposComboBridge : PosComboPairHasCommonInterleaverStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_posComboPair hposComboBridge)

/-- Same four-way package from the reduced positive-combo ingredients:
no-common orientation and degree closeness for `PosComboRealRooted` pairs. -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_and_degreeClose
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_posComboBridge
    (hrr := hrr) (hpos := hpos)
    (posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
      hstep hdegClose)

/-- Four-way Chudnovsky--Seymour package from no-common orientation in the
nonnegative-coefficient regime (where degree closeness is automatic). -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_noCommonOrientation_and_nonnegCoeffs
        hstep hpos hnn

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the honest same-degree/succ-degree split, where the succ-degree branch is
stated directly as a common-interleaver bridge. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc hpos hnn

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the repaired degree split: both same-degree and succ-degree no-common
branches are stated directly as common-interleaver bridges. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc hpos hnn

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the all-combinations bridge. -/
theorem chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) :=
  chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
    (hrr := hrr) (hpos := hpos) (hnn := hnn)
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the affine-family bridge. -/
theorem chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_affineFamilyBridge_and_nonnegCoeffs
        haffBridge hpos hnn

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the boundary-right-pair orientation statement. -/
theorem chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_boundaryRightPairOrientation_nonneg
        hboundary hpos hnn

private theorem pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour :
      (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
        (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
        (HasCommonInterleaver fs ↔ FamilyCompatible fs)) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  hfour.1.trans hfour.2.1

private theorem pairwiseCompatible_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour :
      (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
        (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
        (HasCommonInterleaver fs ↔ FamilyCompatible fs)) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  hfour.1.trans (hfour.2.1.trans hfour.2.2)

/-- Chudnovsky--Seymour `1 ↔ 3` corollary under the natural positive-leading
pair bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairBridgePos
      (fs := fs) hrr hpos htwo

/-- Chudnovsky--Seymour `1 ↔ 4` corollary under the natural positive-leading
pair bridge: pairwise compatibility is equivalent to full family
compatibility. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairBridgePos
      (fs := fs) hrr hpos htwo

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the honest same-degree /
succ-degree compatibility split. -/
theorem pairwiseCompatible_iff_familyCompatible_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_compatibleDegreeSplit
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the nonnegative-coefficient
degree-split package, with the familywise nonnegativity assumption removed by
translation. -/
theorem pairwiseCompatible_iff_familyCompatible_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 4` specialization after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem
    pairwiseCompatible_iff_familyCompatible_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
      (fs := fs) hrr hpos hsame haffBridge

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the stronger
boundary-right-pair statement after the nonnegative shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
      (fs := fs) hrr hpos hboundary

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the no-common orientation core. -/
theorem pairwiseCompatible_iff_familyCompatible_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hstep

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the honest degree-split package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hsame hsucc

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the repaired degree-split package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hsame hsucc

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem pairwiseCompatible_iff_familyCompatible_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
      (fs := fs) hrr hpos hnn hsame haffBridge

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the all-combinations bridge. -/
theorem pairwiseCompatible_iff_familyCompatible_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hallBridge

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the affine-family bridge. -/
theorem pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn haffBridge

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the boundary-right-pair orientation statement. -/
theorem pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hboundary

/-- In the degree-`≤ 1` regime, every pair already has a common right
interleaver. This is the fully packaged two-polynomial input for the
Chudnovsky--Seymour chain in the linear/constant endpoint. -/
theorem pairwiseHasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonInterleaver fs := by
  intro i j hij
  exact
    pairHasCommonInterleaver_of_natDegree_le_one
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hdeg (fs.get i) (List.get_mem _ _))
      (hdeg (fs.get j) (List.get_mem _ _))

/-- Therefore any finite positive-leading family of degree at most one already
has a global common right interleaver. -/
theorem hasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    HasCommonInterleaver fs := by
  have hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits) :=
    fun f hf =>
      isRealRooted_of_natDegree_le_one
        (HasPosLeadingCoeff.ne_zero (hpos f hf)) (hdeg f hf)
  exact
    hasCommonInterleaver_of_pairwiseHasCommonInterleaver
      (fun f hf => (hrr f hf).2) hpos (pairwiseHasCommonInterleaver_of_natDegree_le_one hpos hdeg)

/-- Low-degree Chudnovsky--Seymour package: if every member of the family has
degree at most one and positive leading coefficient, then all four standard
compatibility/common-interleaver formulations collapse without any additional
bridge hypothesis. -/
theorem chudnovskySeymour_fourWay_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
      (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
      (HasCommonInterleaver fs ↔ FamilyCompatible fs) := by
  have hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits) :=
    fun f hf =>
      isRealRooted_of_natDegree_le_one
        (HasPosLeadingCoeff.ne_zero (hpos f hf)) (hdeg f hf)
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
      fun _ => pairwiseHasCommonInterleaver_of_natDegree_le_one hpos hdeg

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `1 ↔ 4`: for
positive-leading linear/constant families, pairwise compatibility is already
equivalent to full family compatibility. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_one
      (fs := fs) hpos hdeg

/-- Roadmap target for the common-interlacing form of the
Chudnovsky--Seymour theorem used in `INTERLACING.md`.

The reverse implication is intentionally only packaged as a statement here:
it still needs
1. the two-polynomial bridge `Compatible f g -> ∃ h, Prec h f ∧ Prec h g`, and
2. the finite-family left-handed Helly upgrade
   `PairwiseHasCommonLeftInterleaver fs -> HasCommonLeftInterleaver fs`. -/
def chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_statement : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs)

end RealRooted
