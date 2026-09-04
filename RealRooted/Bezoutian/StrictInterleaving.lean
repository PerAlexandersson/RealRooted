import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Mathlib.Data.List.Interleave

/-!
# Strict same-degree interlacing

Root-list reversal lemmas and the strict same-degree proper-position predicate,
including its transport across nonzero scalar multiples.

-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

protected lemma interleaves_reverse_of_interlaced_left :
    ∀ {ss rs : List ℝ} (h : ss.length + 1 = rs.length)
      (h_lt₁ : ∀ (i : Fin ss.length) (j : Fin rs.length),
        i.val + 1 = j.val → ss[i.val] < rs[j.val])
      (h_lt₂ : ∀ (i : Fin rs.length) (j : Fin ss.length),
        i.val < j.val + 1 → rs[i.val] < ss[j.val]),
      List.Interleaves (· > ·) ss.reverse rs.reverse := by
  intro ss
  induction ss with
  | nil =>
    intro rs h _ _
    rcases rs with _ | ⟨r, _ | ⟨r₂, rs⟩⟩
    · simp
    · simp
    · simp at h
  | cons s ss ih =>
    intro rs h h_lt₁ h_lt₂
    rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs⟩⟩
    · simp at h
    · simp at h
    have h_len : ss.length + 1 = (r₂ :: rs).length := by
      simp only [List.length_cons] at h ⊢
      lia
    have h_eq_len₁ : ss.reverse.length + 1 = (rs.reverse ++ [r₂]).length := by simp_all
    have h_eq_len₂ : ss.reverse.length = rs.reverse.length := by simpa using h_len
    rw [List.reverse_cons, List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_add_one_eq_length h_eq_len₁,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len₂,
      ← List.reverse_cons]
    refine ⟨h_lt₂ ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩ Nat.zero_lt_one,
      h_lt₁ ⟨0, Nat.zero_lt_succ _⟩ ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ rfl,
      ih h_len ?_ ?_⟩
    · intro i j hij
      exact
        h_lt₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by lia)
    · intro i j hij
      exact
        h_lt₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by lia)

protected lemma interleaves_reverse_of_interlaced :
    ∀ {ss rs : List ℝ} (h : ss.length = rs.length)
      (h_lt₁ : ∀ (k : Fin ss.length), ss[k.val] < rs[k.val])
      (h_lt₂ : ∀ (i j : Fin ss.length), i.val < j.val → rs[i.val] < ss[j.val]),
      List.Interleaves (· > ·) ss.reverse rs.reverse := by
  intro ss
  induction ss with
  | nil =>
    intro rs h _ _
    rcases rs with _ | ⟨r, rs⟩
    · simp
    · simp at h
  | cons s ss ih =>
    intro rs h h_lt₁ h_lt₂
    rcases rs with _ | ⟨r, rs⟩
    · simp at h
    have h_len : ss.length = rs.length := by
      simp only [List.length_cons] at h ⊢
      lia
    have h_eq_len : ss.reverse.length = rs.reverse.length := by simp_all
    rw [List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len,
      ← List.reverse_cons]
    have h_len_left : ss.length + 1 = (r :: rs).length := by simp [h_len]
    refine ⟨h_lt₁ ⟨0, Nat.zero_lt_succ _⟩,
            RealRooted.interleaves_reverse_of_interlaced_left h_len_left ?_ ?_⟩
    · intro i j hij
      rcases i with ⟨i_val, hi⟩
      rcases j with ⟨_ | j_val, hj⟩
      · lia
      · have h_eq : i_val = j_val := by lia
        subst h_eq
        exact h_lt₁ ⟨i_val + 1, Nat.succ_lt_succ hi⟩
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · exact h_lt₂ ⟨0, Nat.zero_lt_succ _⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
          (Nat.zero_lt_succ _)
      · exact h_lt₂ ⟨i_val + 1, h.symm ▸ hi⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ hij

protected lemma List.Interleaves.ofFn {n : ℕ}
    (s r : Fin n → ℝ)
    (h_lt₁ : ∀ k : Fin n, s k < r k)
    (h_lt₂ : ∀ (i j : Fin n), i < j → r i < s j) :
    List.Interleaves (· > ·) (List.ofFn s).reverse (List.ofFn r).reverse := by
  have h_len : (List.ofFn s).length = (List.ofFn r).length := by simp
  refine RealRooted.interleaves_reverse_of_interlaced h_len ?_ ?_ <;> simp_all

protected lemma List.Interleaves.ofFn_succ {n : ℕ}
    (s : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (h_lt₁ : ∀ (i : Fin n) (j : Fin (n + 1)), i.val + 1 = j.val → s i < t j)
    (h_lt₂ : ∀ (i : Fin (n + 1)) (j : Fin n), i.val < j.val + 1 → t i < s j) :
    List.Interleaves (· > ·) (List.ofFn s).reverse (List.ofFn t).reverse := by
  have h_len_st : (List.ofFn s).length + 1 = (List.ofFn t).length := by simp
  apply RealRooted.interleaves_reverse_of_interlaced_left h_len_st
  · intro i j hij
    have hi : i.val < n := by simpa using i.isLt
    have hj : j.val < n + 1 := by simpa using j.isLt
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact h_lt₁ ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
  · intro i j hij
    have hi : i.val < n + 1 := by simpa using i.isLt
    have hj : j.val < n := by simpa using j.isLt
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact h_lt₂ ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij


protected lemma interlaced_of_interleaves_reverse_left :
    ∀ {ss rs : List ℝ} (h : ss.length + 1 = rs.length)
      (_ : List.Interleaves (· > ·) ss.reverse rs.reverse),
      (∀ (i : Fin ss.length) (j : Fin rs.length), i.val + 1 = j.val →
        ss[i.val] < rs[j.val]) ∧
      (∀ (i : Fin rs.length) (j : Fin ss.length), i.val < j.val + 1 →
        rs[i.val] < ss[j.val]) := by
  intro ss
  induction ss with
  | nil =>
    simp
  | cons s ss ih =>
    intro rs h h_inter
    rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs⟩⟩
    · simp
    · simp at h
    have h_len : ss.length + 1 = (r₂ :: rs).length := by simp_all
    have h_eq_len₁ : ss.reverse.length + 1 = (rs.reverse ++ [r₂]).length := by simp_all
    have h_eq_len₂ : ss.reverse.length = rs.reverse.length := by simp_all
    rw [List.reverse_cons, List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_add_one_eq_length h_eq_len₁,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len₂,
      ← List.reverse_cons] at h_inter
    obtain ⟨hr₁s, hsr₂, h_inter_tail⟩ := h_inter
    have h_tail :
        (∀ (i : Fin ss.length) (j : Fin (r₂ :: rs).length),
          i.val + 1 = j.val → ss[i.val] < (r₂ :: rs)[j.val]) ∧
        (∀ (i : Fin (r₂ :: rs).length) (j : Fin ss.length),
          i.val < j.val + 1 → (r₂ :: rs)[i.val] < ss[j.val]) :=
      ih h_len h_inter_tail
    constructor
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · rcases j with ⟨_ | _ | j_val, hj⟩
        · contradiction
        · exact hsr₂
        · lia
      · rcases j with ⟨_ | j_val, hj⟩
        · contradiction
        · exact h_tail.1 ⟨i_val, Nat.lt_of_succ_lt_succ hi⟩
            ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ (Nat.succ.inj hij)
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · rcases j with ⟨_ | j_val, hj⟩
        · exact hr₁s
        · exact hr₁s.trans (hsr₂.trans (h_tail.2 ⟨0, Nat.zero_lt_succ _⟩
            ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ (Nat.zero_lt_succ _)))
      · rcases j with ⟨_ | j_val, hj⟩
        · contradiction
        · exact h_tail.2 ⟨i_val, Nat.lt_of_succ_lt_succ hi⟩
            ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ (Nat.succ_lt_succ_iff.mp hij)

protected lemma interlaced_of_interleaves_reverse :
    ∀ {ss rs : List ℝ} (h : ss.length = rs.length)
      (_ : List.Interleaves (· > ·) ss.reverse rs.reverse),
      (∀ (k : Fin ss.length), ss[k.val] < rs[k.val]) ∧
      (∀ (i j : Fin ss.length), i.val < j.val → rs[i.val] < ss[j.val]) := by
  intro ss
  induction ss with
  | nil =>
    simp
  | cons s ss ih =>
    intro rs h h_inter
    rcases rs with _ | ⟨r, rs⟩
    · simp at h
    have h_len : ss.length = rs.length := by simp_all
    have h_eq_len : ss.reverse.length = rs.reverse.length := by simp_all
    rw [List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len,
      ← List.reverse_cons] at h_inter
    obtain ⟨hsr, h_inter_tail⟩ := h_inter
    have h_len_left : ss.length + 1 = (r :: rs).length := by simp [h_len]
    have h_tail :
        (∀ (i : Fin ss.length) (j : Fin (r :: rs).length),
          i.val + 1 = j.val → ss[i.val] < (r :: rs)[j.val]) ∧
        (∀ (i : Fin (r :: rs).length) (j : Fin ss.length),
          i.val < j.val + 1 → (r :: rs)[i.val] < ss[j.val]) :=
      RealRooted.interlaced_of_interleaves_reverse_left h_len_left h_inter_tail
    constructor
    · intro k
      rcases k with ⟨_ | k_val, hk⟩
      · exact hsr
      · have h_lt : k_val + 1 < (r :: rs).length := by lia
        exact h_tail.1 ⟨k_val, Nat.lt_of_succ_lt_succ hk⟩ ⟨k_val + 1, h_lt⟩ rfl
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · rcases j with ⟨_ | j_val, hj⟩
        · lia
        · exact h_tail.2 ⟨0, Nat.zero_lt_succ _⟩ ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ hij
      · rcases j with ⟨_ | j_val, hj⟩
        · contradiction
        · have h_lt : i_val + 1 < (r :: rs).length := by lia
          exact h_tail.2 ⟨i_val + 1, h_lt⟩ ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ hij


private lemma interleaves_lt_of_le_of_forall_ne :
    ∀ {l₁ l₂ : List ℝ}, List.Interleaves (· ≤ ·) l₁ l₂ →
      (∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b) → List.Interleaves (· < ·) l₁ l₂
  | _, _, .nil_nil, _ => .nil_nil
  | _, _, .nil_singleton a, _ => .nil_singleton a
  | _, _, .cons_symm h hab, hne => by
      apply List.Interleaves.cons_symm
      · apply interleaves_lt_of_le_of_forall_ne h
        intro a ha b hb
        exact (hne b hb a (by simp [ha])).symm
      · exact lt_of_le_of_ne hab (hne _ (by simp) _ (by simp)).symm

/-- Strict same-degree proper position, stated on canonical sorted root lists. -/
def StrictPrecSameDegree (p q : ℝ[X]) : Prop :=
  (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) ∧ p.natDegree = q.natDegree ∧
    List.Interleaves (· > ·) (p.roots.sort (· ≤ ·)).reverse (q.roots.sort (· ≤ ·)).reverse

/-- Equal-degree proper position is strict when the two polynomials have no
common root. -/
theorem StrictPrecSameDegree.of_prec_of_no_common {p q : ℝ[X]} (h : Prec p q)
    (hdeg : p.natDegree = q.natDegree)
    (hno : ∀ r, p.IsRoot r → ¬q.IsRoot r) :
    StrictPrecSameDegree p q := by
  obtain ⟨hp, hq, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := h
  have hss_len : ss.length = p.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hp.2]
  have hrs_len : rs.length = q.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
  obtain ⟨_, halt⟩ := hshape.resolve_left (by intro hbad; lia)
  have hlen : ss.length = rs.length := by lia
  have hinter : List.Interleaves (· ≤ ·) rs ss :=
    interleaves_of_listAlternates_of_length hlen halt
  have hne : ∀ r ∈ rs, ∀ s ∈ ss, r ≠ s := by
    intro r hr s hs heq
    subst r
    have hsRoot : p.IsRoot s := by
      apply (mem_roots hp.1).mp
      rw [← hss_eq]
      exact Multiset.mem_coe.mpr hs
    have hqRoot : q.IsRoot s := by
      apply (mem_roots hq.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr
    exact hno s hsRoot hqRoot
  have hstrict : List.Interleaves (· < ·) rs ss :=
    interleaves_lt_of_le_of_forall_ne hinter hne
  have hreverse : List.Interleaves (· > ·) ss.reverse rs.reverse := by
    apply (List.interleaves_reverse_reverse_of_length_eq_length hlen).2
    simpa [Function.swap] using hstrict
  have hssCanonical : ss = p.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hss_sorted (Multiset.pairwise_sort _ _)
    exact Multiset.coe_eq_coe.mp (hss_eq.trans (Multiset.sort_eq ..).symm)
  have hrsCanonical : rs = q.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs_sorted (Multiset.pairwise_sort _ _)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq ..).symm)
  rw [hssCanonical, hrsCanonical] at hreverse
  exact ⟨hp, hq, hdeg, hreverse⟩

lemma StrictPrecSameDegree.C_mul_C_mul {p q : ℝ[X]} (h : StrictPrecSameDegree p q)
    {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    StrictPrecSameDegree (C u * p) (C v * q) := by
  obtain ⟨hp, hq, hdeg, halt⟩ := h
  refine ⟨isRealRooted_C_mul hp.1 hp.2 hu, isRealRooted_C_mul hq.1 hq.2 hv, ?_, ?_⟩
  · exact (natDegree_C_mul hu).trans (hdeg.trans (natDegree_C_mul hv).symm)
  · simp_all

lemma StrictPrecSameDegree.C_mul_C_mul_iff {p q : ℝ[X]} {u v : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    StrictPrecSameDegree (C u * p) (C v * q) ↔ StrictPrecSameDegree p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.C_mul_C_mul hu hv⟩
  have h_mul := h.C_mul_C_mul (inv_ne_zero hu) (inv_ne_zero hv)
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, one_mul,
    ← mul_assoc, ← C_mul, inv_mul_cancel₀ hv, C_1, one_mul] at h_mul

/-- Strict same-degree proper position implies the legacy non-strict proper
position predicate. -/
theorem StrictPrecSameDegree.to_prec {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) : Prec p q := by
  obtain ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, hdeg, h_inter⟩ := h
  have h_len : (p.roots.sort (· ≤ ·)).length = (q.roots.sort (· ≤ ·)).length := by
    simp [card_roots_of_splits, *]
  rw [List.interleaves_reverse_reverse_of_length_eq_length h_len] at h_inter
  have h_le : List.Interleaves (· ≤ ·) (q.roots.sort (· ≤ ·))
      (p.roots.sort (· ≤ ·)) := h_inter.mono fun _ _ hab ↦ le_of_lt hab
  exact
    ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, p.roots.sort (· ≤ ·),
      q.roots.sort (· ≤ ·), Multiset.pairwise_sort .., Multiset.pairwise_sort ..,
      Multiset.sort_eq _ _, Multiset.sort_eq _ _,
      Or.inr ⟨h_len, (listAlternates_iff_interleaves_of_length h_len).2 h_le⟩⟩

end RealRooted
