import RealRooted.Basic
import RealRooted.Linear
import RealRooted.WagnerLeftSum

/-!
# Weighted sums and interlacing

This file packages positive and nonnegative linear-combination consequences of
the Wagner addition theorems.

On the common-right side, the positive-leading-coefficient version of Wagner (1)
is strong enough to handle arbitrary finite nonnegative weighted sums.

On the common-left side, Wagner (2) still needs compatibility data for genuine
two-term sums, namely real-rootedness of the resulting combination and
coprimeness of the summands after any shared factor has been removed.  For
finite weighted sums, this is packaged below as an inductive compatibility
predicate.
-/

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
  induction l <;> simp [weightedSum_cons, *]

lemma weightedSum_eq_zero_of_forall_coeff_zero :
    ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, ap.1 = 0) →
      weightedSum l = 0
  | [], _ => rfl
  | (a, p) :: l, hzero => by
      have ha : a = 0 := hzero (a, p) (by simp)
      have hl : ∀ ap ∈ l, ap.1 = 0 :=
        List.forall_mem_of_forall_mem_cons hzero
      simp [weightedSum_cons, ha, weightedSum_eq_zero_of_forall_coeff_zero l hl]

private lemma forall_weight_eq_zero_of_nonneg_of_not_exists_pos
    {l : List (ℝ × ℝ[X])}
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hnot_pos : ¬ ∃ ap ∈ l, 0 < ap.1) :
    ∀ ap ∈ l, ap.1 = 0 := fun ap hap => by
  exact le_antisymm (not_lt.mp fun hap_pos => hnot_pos ⟨ap, hap, hap_pos⟩)
    (hnonneg ap hap)

lemma hasPosLeadingCoeff_weightedSum :
    ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, HasPosLeadingCoeff ap.2) →
      (∃ ap ∈ l, 0 < ap.1) →
      HasPosLeadingCoeff (weightedSum l)
  | [], _, _, hex => by simp_all
  | (a, p) :: l, hnonneg, hpos, hex => by
      have hnonneg_a : 0 ≤ a := hnonneg (a, p) (by simp)
      have hnonneg_tail : ∀ ap ∈ l, 0 ≤ ap.1 :=
        List.forall_mem_of_forall_mem_cons hnonneg
      have hpos_tail : ∀ ap ∈ l, HasPosLeadingCoeff ap.2 :=
        List.forall_mem_of_forall_mem_cons hpos
      rcases lt_or_eq_of_le hnonneg_a with ha | rfl
      · by_cases htail : ∃ ap ∈ l, 0 < ap.1
        · have hCp_pos : HasPosLeadingCoeff (C a * p) :=
            hasPosLeadingCoeff_C_mul ha (hpos (a, p) (by simp))
          have htail_pos : HasPosLeadingCoeff (weightedSum l) :=
            hasPosLeadingCoeff_weightedSum l hnonneg_tail hpos_tail htail
          rcases lt_trichotomy (C a * p).natDegree (weightedSum l).natDegree with hlt | heq | hgt
          · simpa [weightedSum_cons] using
              hasPosLeadingCoeff_add_of_natDegree_lt_right hlt htail_pos
          · simpa [weightedSum_cons] using
              hasPosLeadingCoeff_add_of_same_natDegree heq hCp_pos htail_pos
          · simpa [weightedSum_cons] using
              hasPosLeadingCoeff_add_of_natDegree_lt_left hgt hCp_pos
        · have hzero_tail : weightedSum l = 0 :=
            weightedSum_eq_zero_of_forall_coeff_zero l
              (forall_weight_eq_zero_of_nonneg_of_not_exists_pos
                hnonneg_tail htail)
          simpa [weightedSum_cons, hzero_tail] using
            hasPosLeadingCoeff_C_mul ha (hpos (a, p) (by simp))
      · have htail : ∃ ap ∈ l, 0 < ap.1 := by simp_all
        simpa [weightedSum_cons] using
          hasPosLeadingCoeff_weightedSum l hnonneg_tail hpos_tail htail

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
      (hrr_ne : (C a * p + weightedSum l) ≠ 0)
      (hrr_splits : (C a * p + weightedSum l).Splits)
      (hcop : IsCoprime (C a * p) (weightedSum l)) :
      WeightedCompatibleLeft h ((a, p) :: l)

namespace WeightedCompatibleLeft

lemma nonneg {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l → ∀ ap ∈ l, 0 ≤ ap.1
  | _, @singleton _ a p ha _ _ => by
      grind
  | _, cons_zero ha _ _ hl => fun ap hap => by
      rcases List.mem_cons.mp hap with rfl | hap
      · exact ha.symm.le
      · exact nonneg hl ap hap
  | _, cons_pos ha _ _ hl _ _ _ => fun ap hap => by
      rcases List.mem_cons.mp hap with rfl | hap
      · exact ha.le
      · exact nonneg hl ap hap

lemma pos {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l →
      ∀ ap ∈ l, HasPosLeadingCoeff ap.2
  | _, @singleton _ a p _ _ hpos => by
      simp_all
  | _, cons_zero _ _ hpos hl => fun ap hap => by
      rcases List.mem_cons.mp hap with rfl | hap
      · exact hpos
      · exact pos hl ap hap
  | _, cons_pos _ _ hpos hl _ _ _ => fun ap hap => by
      rcases List.mem_cons.mp hap with rfl | hap
      · exact hpos
      · exact pos hl ap hap

lemma exists_pos {h : ℝ[X]} :
    ∀ {l : List (ℝ × ℝ[X])}, WeightedCompatibleLeft h l →
      ∃ ap ∈ l, 0 < ap.1
  | _, @singleton _ a p ha _ _ => by
      simp_all
  | _, cons_zero _ _ _ hl => by
      rcases exists_pos hl with ⟨ap, hap, hapos⟩
      grind
  | _, @cons_pos _ a p l ha _ _ _ _ _ _ => by
      simp_all

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
  | _, @cons_pos _ a p l ha hprec hpos hl hrr_ne hrr_splits hcop => by
      have hCa_pos : HasPosLeadingCoeff (C a * p) := hasPosLeadingCoeff_C_mul ha hpos
      exact prec_add_of_prec_left
        (prec_C_mul_right hprec ha.ne')
        (prec hl)
        hCa_pos (hasPosLeadingCoeff hl) hrr_ne hrr_splits hcop

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
          simp_all
      | cons_pos _ _ _ hl _ _ _ =>
          cases hl
  | p :: q :: l, hl => by
      cases hl with
      | cons_zero ha _ _ _ =>
          simp_all
      | cons_pos _ hprec hpos htail hrr_ne hrr_splits hcop =>
          exact SumCompatibleLeft.cons hprec hpos
            (toSumCompatibleLeft_map_one htail)
            (by simp_all) (by simp_all) (by simp_all)

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
  | [], _, _, _, _, hex => by simp_all
  | (a, p) :: l, h, hnonneg, hprec, hpos, hex => by
      have hnonneg_a : 0 ≤ a := hnonneg (a, p) (by simp)
      have hnonneg_tail : ∀ ap ∈ l, 0 ≤ ap.1 :=
        List.forall_mem_of_forall_mem_cons hnonneg
      have hprec_tail : ∀ ap ∈ l, Prec ap.2 h :=
        List.forall_mem_of_forall_mem_cons hprec
      have hpos_tail : ∀ ap ∈ l, HasPosLeadingCoeff ap.2 :=
        List.forall_mem_of_forall_mem_cons hpos
      rcases lt_or_eq_of_le hnonneg_a with ha | rfl
      · by_cases htail : ∃ ap ∈ l, 0 < ap.1
        · have hCp_prec : Prec (C a * p) h :=
            prec_C_mul_left (hprec (a, p) (by simp)) ha.ne'
          have hCp_pos : HasPosLeadingCoeff (C a * p) :=
            hasPosLeadingCoeff_C_mul ha (hpos (a, p) (by simp))
          have htail_prec : Prec (weightedSum l) h :=
            prec_weightedSum_right l h hnonneg_tail hprec_tail hpos_tail htail
          have htail_pos : HasPosLeadingCoeff (weightedSum l) :=
            hasPosLeadingCoeff_weightedSum l hnonneg_tail hpos_tail htail
          simpa [weightedSum_cons] using
            prec_add_of_prec_right_of_posLeadingCoeff hCp_prec htail_prec hCp_pos htail_pos
        · have hzero_tail : weightedSum l = 0 :=
            weightedSum_eq_zero_of_forall_coeff_zero l
              (forall_weight_eq_zero_of_nonneg_of_not_exists_pos
                hnonneg_tail htail)
          simpa [weightedSum_cons, hzero_tail] using
            prec_C_mul_left (hprec (a, p) (by simp)) ha.ne'
      · have htail : ∃ ap ∈ l, 0 < ap.1 := by simp_all
        simpa [weightedSum_cons] using
          prec_weightedSum_right l h hnonneg_tail hprec_tail hpos_tail htail

/-- Unweighted finite-sum Wagner theorem on the right. -/
theorem prec_sum_right
    (l : List ℝ[X]) (h : ℝ[X])
    (hprec : ∀ p ∈ l, Prec p h)
    (hpos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    Prec l.sum h := by
  rw [← weightedSum_map_one l]
  apply prec_weightedSum_right (l.map (fun p => ((1 : ℝ), p))) h
  · simp
  · simp_all
  · simp_all
  · cases l <;> simp_all

end RealRooted
