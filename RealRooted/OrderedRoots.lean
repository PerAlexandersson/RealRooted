import RealRooted.Basic

/-!
# Canonically ordered polynomial roots

This file packages the increasing root list of a real polynomial and relates
coordinate bounds on equal-length root lists to same-degree proper position.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The `i`th root of a polynomial, in increasing order. The default value is
irrelevant when the polynomial has the expected degree and splits. -/
noncomputable def orderedRoot (p : ℝ[X]) (n : ℕ) (i : Fin n) : ℝ :=
  (p.roots.sort (· ≤ ·)).getD i 0

/-- For two nonzero, split polynomials of degree `n`, proper position is
equivalent to the coordinate bounds on their canonically ordered roots. -/
theorem prec_iff_orderedRoot_bounds
    {p q : ℝ[X]} {n : ℕ}
    (hpNe : p ≠ 0) (hpSplits : p.Splits)
    (hqNe : q ≠ 0) (hqSplits : q.Splits)
    (hpDegree : p.natDegree = n) (hqDegree : q.natDegree = n) :
    Prec p q ↔
      (∀ i : Fin n, orderedRoot p n i ≤ orderedRoot q n i) ∧
      (∀ (i : Fin n) (hi : i.val + 1 < n),
        orderedRoot q n i ≤ orderedRoot p n ⟨i.val + 1, hi⟩) := by
  constructor
  · intro h
    obtain ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := h
    have hssLength : ss.length = n := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hpSplits, hpDegree]
    have hrsLength : rs.length = n := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hqSplits, hqDegree]
    obtain ⟨_, halt⟩ := hshape.resolve_left (by intro hbad; lia)
    have hssCanonical : p.roots.sort (· ≤ ·) = ss := by
      rw [← hss_eq, Multiset.coe_sort]
      exact List.mergeSort_eq_self (· ≤ ·) hss
    have hrsCanonical : q.roots.sort (· ≤ ·) = rs := by
      rw [← hrs_eq, Multiset.coe_sort]
      exact List.mergeSort_eq_self (· ≤ ·) hrs
    obtain ⟨hleft, hright⟩ :=
      listAlternates_getD_bounds ss rs halt (by lia)
    constructor
    · intro i
      change (p.roots.sort (· ≤ ·)).getD i.val 0 ≤
        (q.roots.sort (· ≤ ·)).getD i.val 0
      rw [hssCanonical, hrsCanonical]
      exact hleft i.val (by lia)
    · intro i hi
      change (q.roots.sort (· ≤ ·)).getD i.val 0 ≤
        (p.roots.sort (· ≤ ·)).getD (i.val + 1) 0
      rw [hssCanonical, hrsCanonical]
      exact hright i.val (by lia)
  · rintro ⟨hleft, hright⟩
    let ss := p.roots.sort (· ≤ ·)
    let rs := q.roots.sort (· ≤ ·)
    have hssLength : ss.length = n := by
      rw [show ss = p.roots.sort (· ≤ ·) by rfl, Multiset.length_sort,
        card_roots_of_splits hpSplits, hpDegree]
    have hrsLength : rs.length = n := by
      rw [show rs = q.roots.sort (· ≤ ·) by rfl, Multiset.length_sort,
        card_roots_of_splits hqSplits, hqDegree]
    refine ⟨⟨hpNe, hpSplits⟩, ⟨hqNe, hqSplits⟩, ss, rs,
      Multiset.pairwise_sort .., Multiset.pairwise_sort .., ?_, ?_,
      Or.inr ⟨by lia, ?_⟩⟩
    · simp [ss]
    · simp [rs]
    · apply listAlternates_of_getD_bounds ss rs (by lia)
      · intro i hi
        let k : Fin n := ⟨i, by lia⟩
        simpa only [orderedRoot, ss, rs, k] using hleft k
      · intro i hi
        let k : Fin n := ⟨i, by lia⟩
        simpa only [orderedRoot, ss, rs, k] using hright k (by lia)

/-- Same-degree proper position bounds corresponding increasing roots. -/
theorem Prec.orderedRoot_le {p q : ℝ[X]} {n : ℕ}
    (h : Prec p q) (hpDegree : p.natDegree = n) (hqDegree : q.natDegree = n)
    (i : Fin n) :
    orderedRoot p n i ≤ orderedRoot q n i :=
  (prec_iff_orderedRoot_bounds h.1.1 h.1.2 h.2.1.1 h.2.1.2
    hpDegree hqDegree).mp h |>.1 i

end RealRooted
