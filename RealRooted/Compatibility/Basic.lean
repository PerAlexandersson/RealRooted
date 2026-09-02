import RealRooted.AffineFamily
import RealRooted.Compatibility.Pair
import RealRooted.DegreeDropReversal
import RealRooted.WeightedSum

/-!
# Compatibility predicates for real-rooted polynomials

This module contains the Chudnovsky--Seymour pair and family compatibility
predicates, together with basic preservation and endpoint lemmas.
-/

open Polynomial

noncomputable section

namespace RealRooted

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

/-- Reflecting both members at a common degree bound preserves compatibility. -/
lemma reflect_of_natDegree_le {f g : ℝ[X]} (h : Compatible f g) {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) :
    Compatible (reflect N f) (reflect N g) := by
  intro α β hα hβ
  have hcomb :
      C α * reflect N f + C β * reflect N g =
        reflect N (C α * f + C β * g) := by
    simp [Polynomial.reflect_add, Polynomial.reflect_C_mul]
  have hdeg_combo : (C α * f + C β * g).natDegree ≤ N :=
    (Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_C_mul_le α f).trans hfN)
        ((Polynomial.natDegree_C_mul_le β g).trans hgN)
  rcases h α β hα hβ with hzero | hrr
  · left
    simp [hcomb, hzero]
  · right
    rw [hcomb]
    exact ⟨fun hzero => hrr.1 (Polynomial.reflect_eq_zero_iff.mp hzero),
      DegreeDropReversal.splits_reflect_of_splits hrr.2 hdeg_combo⟩

/-- Reflecting both members at a common degree bound preserves and reflects
compatibility. -/
lemma reflect_iff_natDegree_le {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) :
    Compatible (reflect N f) (reflect N g) ↔ Compatible f g := by
  refine ⟨?_, fun h => h.reflect_of_natDegree_le hfN hgN⟩
  intro h
  have hf_ref_N : (reflect N f).natDegree ≤ N :=
    Polynomial.natDegree_reflect_le.trans <| by rw [max_eq_left hfN]
  have hg_ref_N : (reflect N g).natDegree ≤ N :=
    Polynomial.natDegree_reflect_le.trans <| by rw [max_eq_left hgN]
  have hback : Compatible (reflect N (reflect N f)) (reflect N (reflect N g)) :=
    Compatible.reflect_of_natDegree_le
      (f := reflect N f) (g := reflect N g) (N := N) h hf_ref_N hg_ref_N
  intro α β hα hβ
  simpa [Polynomial.reflect_reflect] using hback α β hα hβ

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

/-- Compatibility is preserved by the degree-preserving root regularizer
`iterateTDeriv` at every positive shift. -/
lemma iterateTDeriv {f g : ℝ[X]} (h : Compatible f g)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    Compatible (RealRooted.iterateTDeriv eps n f)
      (RealRooted.iterateTDeriv eps n g) := by
  intro α β hα hβ
  rcases h α β hα hβ with hzero | hrr
  · left
    rw [← RealRooted.iterateTDeriv_linear_combo, hzero]
    simp
  · right
    rw [← RealRooted.iterateTDeriv_linear_combo]
    exact ⟨RealRooted.iterateTDeriv_ne_zero hrr.1,
      RealRooted.splits_iterateTDeriv heps hrr.2⟩

lemma isRealRooted_left
    {f g : ℝ[X]} (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) : (f ≠ 0 ∧ f.Splits) := by
  rcases h 1 0 (by simp) (by simp) with hzero | hrr <;> simp_all

lemma isRealRooted_right
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
  have hg_rr : (g ≠ 0 ∧ g.Splits) := hcg.isRealRooted_right hg_pos
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
      _ = C t + g := by grind
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
  · have hf_ne : f ≠ 0 := hf_pos.ne_zero
    let c : ℝ := f.coeff 0
    have hcoeff0 : f.coeff 0 = f.leadingCoeff := by
      simpa [hf_deg0] using (Polynomial.coeff_natDegree (p := f))
    have hc : 0 < c := by
      dsimp [c]
      rw [hcoeff0]
      exact hf_pos
    have hf_const : f = C c := by simpa [c] using eq_C_of_natDegree_eq_zero hf_deg0
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

/-- Strict positive-combination real-rootedness plus real-rooted endpoints
upgrades to Chudnovsky--Seymour compatibility.

The strictly positive quadrant is exactly the `PosComboRealRooted` hypothesis;
the coordinate axes are supplied by the endpoint real-rootedness assumptions. -/
lemma of_posComboRealRooted {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    Compatible f g := by
  intro α β hα hβ
  by_cases hα0 : α = 0
  · subst hα0
    by_cases hβ0 : β = 0
    · subst hβ0
      simp
    · right
      simpa using isRealRooted_C_mul hg.1 hg.2 hβ0
  · by_cases hβ0 : β = 0
    · subst hβ0
      right
      simpa using isRealRooted_C_mul hf.1 hf.2 hα0
    · right
      have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hβ_pos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      exact hfg hα_pos hβ_pos

/-- In equal degree, strict positive-combination real-rootedness upgrades to
full nonnegative compatibility: the endpoint real-rootedness follows from the
same-degree restricted converse, and the genuinely positive quadrant is exactly
the `PosComboRealRooted` hypothesis. -/
lemma of_posComboRealRooted_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    Compatible f g :=
  of_posComboRealRooted hfg
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg)
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg)

/-- In the succ-degree #42 setting, strict positive-combination
real-rootedness upgrades to full nonnegative compatibility once the left
endpoint is known to split.  The right endpoint real-rootedness is supplied by
the existing succ-degree endpoint theorem. -/
lemma of_posComboRealRooted_succDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_splits : f.Splits) :
    Compatible f g :=
  of_posComboRealRooted hfg ⟨hf_pos.ne_zero, hf_splits⟩
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg)

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

end RealRooted
