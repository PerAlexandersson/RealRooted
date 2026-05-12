/-
# Convex combinations preserve interlacing

This file packages positive and nonnegative linear-combination consequences of
the Wagner addition theorems.

On the common-right side, the positive-leading-coefficient version of Wagner (1)
is strong enough to handle arbitrary finite nonnegative weighted sums.

On the common-left side, Wagner (2) still needs compatibility data for genuine
two-term sums, namely real-rootedness of the resulting combination and
coprimeness of the summands after any shared factor has been removed. For
finite weighted sums, this is packaged below as an inductive compatibility
predicate.
-/
import RealRooted.Basic
import RealRooted.Linear
import RealRooted.WagnerLeftSum

set_option linter.unusedDecidableInType false

open Polynomial

noncomputable section

namespace RealRooted

/-- Weighted sum of a list of polynomials. Terms with zero weight contribute `0`. -/
def weightedSum : List (ℝ × ℝ[X]) → ℝ[X]
  | [] => 0
  | (a, p) :: l => C a * p + weightedSum l

@[simp] lemma weightedSum_nil : weightedSum [] = 0 := rfl

@[simp] lemma weightedSum_cons (a : ℝ) (p : ℝ[X]) (l : List (ℝ × ℝ[X])) :
    weightedSum ((a, p) :: l) = C a * p + weightedSum l := rfl

@[simp] lemma weightedSum_map_one (l : List ℝ[X]) :
    weightedSum (l.map (fun p => ((1 : ℝ), p))) = l.sum := by
  induction l with
  | nil =>
      simp
  | cons p l ih =>
      simp [weightedSum_cons, ih]

lemma weightedSum_eq_zero_of_forall_coeff_zero :
    ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, ap.1 = 0) →
      weightedSum l = 0
  | [], _ => rfl
  | (a, p) :: l, hzero => by
      have ha : a = 0 := hzero (a, p) (by simp)
      have hl : ∀ ap ∈ l, ap.1 = 0 := by
        intro ap hap
        exact hzero ap (by simp [hap])
      simp [weightedSum_cons, ha, weightedSum_eq_zero_of_forall_coeff_zero l hl]

/-- `HasNonnegCoeffs` is closed under finite sums. -/
lemma hasNonnegCoeffs_finset_sum {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ[X]) (hf : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    HasNonnegCoeffs (s.sum f) := by
  intro n
  rw [finset_sum_coeff]
  exact Finset.sum_nonneg fun i hi => hf i hi n

lemma hasPosLeadingCoeff_C_mul {a : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (C a * p) := by
  unfold HasPosLeadingCoeff at hp ⊢
  rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha.ne') p]
  exact mul_pos ha hp

lemma natDegree_C_mul' {a : ℝ} {p : ℝ[X]} (ha : a ≠ 0) :
    (C a * p).natDegree = p.natDegree := by
  rw [natDegree_C_mul ha]

lemma hasPosLeadingCoeff_weightedSum :
    ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, HasPosLeadingCoeff ap.2) →
      (∃ ap ∈ l, 0 < ap.1) →
      HasPosLeadingCoeff (weightedSum l)
  | [], _, _, hex => by rcases hex with ⟨_, hmem, _⟩; simp at hmem
  | (a, p) :: l, hnonneg, hpos, hex => by
      have hnonneg_a : 0 ≤ a := hnonneg (a, p) (by simp)
      rcases lt_or_eq_of_le hnonneg_a with ha | rfl
      · by_cases htail : ∃ ap ∈ l, 0 < ap.1
        · have hCp_pos : HasPosLeadingCoeff (C a * p) :=
            hasPosLeadingCoeff_C_mul ha (hpos (a, p) (by simp))
          have htail_pos : HasPosLeadingCoeff (weightedSum l) :=
            hasPosLeadingCoeff_weightedSum l
              (fun ap hap => hnonneg ap (by simp [hap]))
              (fun ap hap => hpos ap (by simp [hap]))
              htail
          rcases lt_trichotomy (C a * p).natDegree (weightedSum l).natDegree with hlt | heq | hgt
          · simpa [weightedSum_cons] using
              hasPosLeadingCoeff_add_of_natDegree_lt_right hlt htail_pos
          · simpa [weightedSum_cons] using
              hasPosLeadingCoeff_add_of_same_natDegree heq hCp_pos htail_pos
          · simpa [weightedSum_cons] using
              hasPosLeadingCoeff_add_of_natDegree_lt_left hgt hCp_pos
        · have hzero_tail : weightedSum l = 0 := by
            apply weightedSum_eq_zero_of_forall_coeff_zero
            intro ap hap
            have h_ap_nonneg : 0 ≤ ap.1 := hnonneg ap (by simp [hap])
            have h_ap_not_pos : ¬ 0 < ap.1 := by
              intro hapos
              exact htail ⟨ap, hap, hapos⟩
            linarith
          simpa [weightedSum_cons, hzero_tail] using
            hasPosLeadingCoeff_C_mul ha (hpos (a, p) (by simp))
      · have htail : ∃ ap ∈ l, 0 < ap.1 := by
          rcases hex with ⟨ap, hap, hapos⟩
          rcases List.mem_cons.mp hap with hhead | htail
          · cases hhead
            simpa using hapos.ne'
          · exact ⟨ap, htail, hapos⟩
        simpa [weightedSum_cons] using
          hasPosLeadingCoeff_weightedSum l
            (fun ap hap => hnonneg ap (by simp [hap]))
            (fun ap hap => hpos ap (by simp [hap]))
            htail

/-- Recursive compatibility data for building a common-left weighted sum using
Wagner (2). Zero-weight terms may be skipped, while a positive-weight head term
must be compatible with the weighted tail. -/
inductive WeightedCompatibleLeft (h : ℝ[X]) : List (ℝ × ℝ[X]) → Prop
  | singleton {a : ℝ} {p : ℝ[X]}
      (ha : 0 < a) (hprec : Prec h p) (hpos : HasPosLeadingCoeff p) :
      WeightedCompatibleLeft h [(a, p)]
  | cons_zero {a : ℝ} {p : ℝ[X]} {l : List (ℝ × ℝ[X])}
      (ha : a = 0) (hprec : Prec h p) (hpos : HasPosLeadingCoeff p)
      (hl : WeightedCompatibleLeft h l) :
      WeightedCompatibleLeft h ((a, p) :: l)
  | cons_pos {a : ℝ} {p : ℝ[X]} {l : List (ℝ × ℝ[X])}
      (ha : 0 < a) (hprec : Prec h p) (hpos : HasPosLeadingCoeff p)
      (hl : WeightedCompatibleLeft h l)
      (hrr : IsRealRooted (C a * p + weightedSum l))
      (hcop : IsCoprime (C a * p) (weightedSum l)) :
      WeightedCompatibleLeft h ((a, p) :: l)

namespace WeightedCompatibleLeft

lemma nonneg {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l → ∀ ap ∈ l, 0 ≤ ap.1
  | _, @singleton _ a p ha _ _ => by
      intro ap hap
      have hap' : ap = (a, p) := by simpa using hap
      subst hap'
      exact le_of_lt ha
  | _, cons_zero ha _ _ hl => by
      intro ap hap
      rcases List.mem_cons.mp hap with rfl | hap
      · simp [ha]
      · exact nonneg hl ap hap
  | _, cons_pos ha _ _ hl _ _ => by
      intro ap hap
      rcases List.mem_cons.mp hap with rfl | hap
      · exact le_of_lt ha
      · exact nonneg hl ap hap

lemma pos {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l →
      ∀ ap ∈ l, HasPosLeadingCoeff ap.2
  | _, @singleton _ a p _ _ hpos => by
      intro ap hap
      have hap' : ap = (a, p) := by simpa using hap
      subst hap'
      exact hpos
  | _, cons_zero _ _ hpos hl => by
      intro ap hap
      rcases List.mem_cons.mp hap with rfl | hap
      · exact hpos
      · exact pos hl ap hap
  | _, cons_pos _ _ hpos hl _ _ => by
      intro ap hap
      rcases List.mem_cons.mp hap with rfl | hap
      · exact hpos
      · exact pos hl ap hap

lemma exists_pos {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l →
      ∃ ap ∈ l, 0 < ap.1
  | _, @singleton _ a p ha _ _ => by
      exact ⟨(a, p), by simp, ha⟩
  | _, cons_zero _ _ _ hl => by
      rcases exists_pos hl with ⟨ap, hap, hapos⟩
      exact ⟨ap, by simp [hap], hapos⟩
  | _, @cons_pos _ a p l ha _ _ _ _ _ => by
      exact ⟨(a, p), by simp, ha⟩

lemma hasPosLeadingCoeff {h : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hl : WeightedCompatibleLeft h l) :
    HasPosLeadingCoeff (weightedSum l) :=
  hasPosLeadingCoeff_weightedSum l (nonneg hl) (pos hl) (exists_pos hl)

lemma prec {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l → Prec h (weightedSum l)
  | _, singleton ha hprec _ => by
      simpa [weightedSum, weightedSum_cons] using prec_C_mul_right hprec ha.ne'
  | _, cons_zero ha _ _ hl => by
      simpa [weightedSum, weightedSum_cons, ha] using prec hl
  | _, @cons_pos _ a p l ha hprec hpos hl hrr hcop => by
      have hCa_pos : HasPosLeadingCoeff (C a * p) := hasPosLeadingCoeff_C_mul ha hpos
      exact prec_add_of_prec_left
        (prec_C_mul_right hprec ha.ne')
        (prec hl)
        hCa_pos (hasPosLeadingCoeff hl) hrr hcop

lemma toSumCompatibleLeft_map_one {h : ℝ[X]} :
    ∀ {l : List ℝ[X]},
      WeightedCompatibleLeft h (l.map (fun p => ((1 : ℝ), p))) →
      SumCompatibleLeft h l
  | [], hl => by
      cases hl
  | [p], hl => by
      cases hl with
      | singleton _ hprec hpos =>
          simpa using SumCompatibleLeft.singleton hprec hpos
      | cons_zero ha _ _ _ =>
          norm_num at ha
      | cons_pos _ _ _ hl _ _ =>
          cases hl
  | p :: q :: l, hl => by
      cases hl with
      | cons_zero ha _ _ _ =>
          norm_num at ha
      | cons_pos _ hprec hpos htail hrr hcop =>
          have htail' : SumCompatibleLeft h (q :: l) :=
            toSumCompatibleLeft_map_one htail
          have hrr' : IsRealRooted (p + (q :: l).sum) := by
            simpa [weightedSum_map_one] using hrr
          have hcop' : IsCoprime p (q :: l).sum := by
            simpa [weightedSum_map_one] using hcop
          exact SumCompatibleLeft.cons hprec hpos htail' hrr' hcop'

end WeightedCompatibleLeft

/-- Finite weighted Wagner theorem on the left, under recursive Wagner-2
compatibility of the weighted list. -/
theorem prec_weightedSum_left {h : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hl : WeightedCompatibleLeft h l) :
    Prec h (weightedSum l) :=
  hl.prec

/-- Unweighted finite-sum Wagner theorem on the left. The required compatibility
data is the `WeightedCompatibleLeft` condition on unit weights. -/
theorem prec_sum_left {h : ℝ[X]} {l : List ℝ[X]}
    (hl : WeightedCompatibleLeft h (l.map (fun p => ((1 : ℝ), p)))) :
    Prec h l.sum := by
  simpa using prec_sum_of_compatible_left (WeightedCompatibleLeft.toSumCompatibleLeft_map_one hl)

/-- Finite weighted Wagner theorem on the right: if every polynomial in the list
precedes the same right-hand bound `h`, has positive leading coefficient, and all
weights are nonnegative with at least one positive weight, then the weighted sum
also precedes `h`. -/
theorem prec_weightedSum_right :
    ∀ (l : List (ℝ × ℝ[X])) (h : ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, Prec ap.2 h) →
      (∀ ap ∈ l, HasPosLeadingCoeff ap.2) →
      (∃ ap ∈ l, 0 < ap.1) →
      Prec (weightedSum l) h
  | [], _, _, _, _, hex => by rcases hex with ⟨_, hmem, _⟩; simp at hmem
  | (a, p) :: l, h, hnonneg, hprec, hpos, hex => by
      have hnonneg_a : 0 ≤ a := hnonneg (a, p) (by simp)
      rcases lt_or_eq_of_le hnonneg_a with ha | rfl
      · by_cases htail : ∃ ap ∈ l, 0 < ap.1
        · have hCp_prec : Prec (C a * p) h :=
            prec_C_mul_left (hprec (a, p) (by simp)) ha.ne'
          have hCp_pos : HasPosLeadingCoeff (C a * p) :=
            hasPosLeadingCoeff_C_mul ha (hpos (a, p) (by simp))
          have htail_prec : Prec (weightedSum l) h :=
            prec_weightedSum_right l h
              (fun ap hap => hnonneg ap (by simp [hap]))
              (fun ap hap => hprec ap (by simp [hap]))
              (fun ap hap => hpos ap (by simp [hap]))
              htail
          have htail_pos : HasPosLeadingCoeff (weightedSum l) :=
            hasPosLeadingCoeff_weightedSum l
              (fun ap hap => hnonneg ap (by simp [hap]))
              (fun ap hap => hpos ap (by simp [hap]))
              htail
          simpa [weightedSum_cons] using
            prec_add_of_prec_right_of_posLeadingCoeff hCp_prec htail_prec hCp_pos htail_pos
        · have hzero_tail : weightedSum l = 0 := by
            apply weightedSum_eq_zero_of_forall_coeff_zero
            intro ap hap
            have h_ap_nonneg : 0 ≤ ap.1 := hnonneg ap (by simp [hap])
            have h_ap_not_pos : ¬ 0 < ap.1 := by
              intro hapos
              exact htail ⟨ap, hap, hapos⟩
            linarith
          simpa [weightedSum_cons, hzero_tail] using
            prec_C_mul_left (hprec (a, p) (by simp)) ha.ne'
      · have htail : ∃ ap ∈ l, 0 < ap.1 := by
          rcases hex with ⟨ap, hap, hapos⟩
          rcases List.mem_cons.mp hap with hhead | htail
          · cases hhead
            simpa using hapos.ne'
          · exact ⟨ap, htail, hapos⟩
        simpa [weightedSum_cons] using
          prec_weightedSum_right l h
            (fun ap hap => hnonneg ap (by simp [hap]))
            (fun ap hap => hprec ap (by simp [hap]))
            (fun ap hap => hpos ap (by simp [hap]))
            htail

/-- Unweighted finite-sum Wagner theorem on the right. -/
theorem prec_sum_right
    (l : List ℝ[X]) (h : ℝ[X])
    (hprec : ∀ p ∈ l, Prec p h)
    (hpos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    Prec l.sum h := by
  rw [← weightedSum_map_one l]
  apply prec_weightedSum_right (l.map (fun p => ((1 : ℝ), p))) h
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    norm_num
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    exact hprec p hp
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    exact hpos p hp
  · cases l with
    | nil =>
        contradiction
    | cons p l =>
        refine ⟨((1 : ℝ), p), ?_, by norm_num⟩
        simp


end RealRooted
