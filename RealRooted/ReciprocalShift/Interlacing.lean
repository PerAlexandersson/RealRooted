import RealRooted.ReciprocalShift.Roots

/-!
# Ordered root lists for reciprocal shifts

This module contains the inverse-root ordering and root-list model behind the
proper-position transport for degree-padded reciprocal shifts. Padding
interlacing and the polynomial-level `Prec` swap live in later modules.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Inversion reverses the order of two nonpositive real numbers when the
right-hand number is strictly negative. -/
theorem one_div_antitone_of_nonpos {a b : ℝ}
    (hb : b < 0) (hab : a ≤ b) :
    1 / b ≤ 1 / a := by
  have ha : a < 0 := lt_of_le_of_lt hab hb
  have ha_ne : a ≠ 0 := ne_of_lt ha
  have hb_ne : b ≠ 0 := ne_of_lt hb
  have hleft : (1 : ℝ) / b = a * (1 / (a * b)) := by
    grind
  have hright : (1 : ℝ) / a = b * (1 / (a * b)) := by
    grind
  rw [hleft, hright]
  have hproduct : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have hpositive : 0 < 1 / (a * b) := by
    positivity
  exact mul_le_mul_of_nonneg_right hab hpositive.le

/-- The ordered model list for a degree-padded reciprocal shift is sorted. -/
theorem reciprocalShift_model_sorted (l : List ℝ) (k : ℕ)
    (hsorted : l.Pairwise (· ≤ ·)) (hnonpos : ∀ x ∈ l, x ≤ 0) :
    ((l.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r)
      ++ List.replicate k 0).Pairwise (· ≤ ·) := by
  set L := l.filter fun r ↦ decide (r ≠ 0) with hL
  have hnegative : ∀ x ∈ L, x < 0 := by
    grind
  have hsortedL : L.Pairwise (· ≤ ·) := hsorted.filter _
  have hinverse : (L.reverse.map fun r ↦ 1 / r).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map, List.pairwise_reverse]
    refine hsortedL.imp_of_mem ?_
    intro a b ha hb hab
    exact one_div_antitone_of_nonpos (hnegative b hb) hab
  rw [List.pairwise_append]
  refine ⟨hinverse, by simp, ?_⟩
  intro a ha b hb
  rw [List.mem_map] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  rw [List.mem_reverse] at hx
  rw [← hxa]
  have hneg : 1 / x < 0 := one_div_neg.mpr (hnegative x hx)
  have hb_zero : b = 0 := (List.mem_replicate.mp hb).2
  rw [hb_zero]
  exact hneg.le

/-- A sorted-list representative of a split polynomial's roots transports to
the reciprocal-shift root multiset through inverse roots and degree padding. -/
theorem reciprocalShift_model_roots
    {D : ℕ} {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hdegree : p.natDegree ≤ D) (l : List ℝ) (hl : (l : Multiset ℝ) = p.roots) :
    (((l.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r)
      ++ List.replicate (D - p.natDegree) 0 : List ℝ) : Multiset ℝ) =
        (reciprocalShift D p).roots := by
  rw [roots_reciprocalShift_eq hp_ne hp_splits hdegree]
  rw [← Multiset.coe_add, add_comm]
  congr 1
  rw [← Multiset.map_coe, Multiset.coe_reverse, ← Multiset.filter_coe, hl]
  simp only [one_div]

end RealRooted
