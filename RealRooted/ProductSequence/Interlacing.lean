import RealRooted.Basic.ProperPosition
import RealRooted.Basic.RootLists
import RealRooted.WagnerX.ListInterlacing

/-!
# Interlacing in product sequences

Multiplying a real-rooted polynomial by a linear factor inserts one root into its
ordered root list, so the two polynomials interlace.  Iterating gives the complete
theory of *product sequences* `P (n + 1) = L n * P n` with every `L n` linear:

* `interlaces_self_mul_of_natDegree_eq_one`: `Interlaces f (L * f)`;
* `productSequence_natDegree`: `(P n).natDegree = (P 0).natDegree + n`;
* `productSequence_interlaces`: `Interlaces (P n) (P (n + 1))`.

No sign or leading-coefficient condition is needed: the roots of `L n` may lie
anywhere on the real line.  These are the facts behind the product-recurrence
OEIS triangles (`P (n + 1) = (a + b X) P n`, possibly with `n`-dependent `a, b`).
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A sorted list interlaces with itself after inserting one element. -/
theorem listInterlaces_self_orderedInsert (a : ℝ) :
    ∀ {ss : List ℝ}, ss.Pairwise (· ≤ ·) → ListInterlaces ss (ss.orderedInsert (· ≤ ·) a)
  | [], _ => by simp [ListInterlaces]
  | s :: t, hs => by
      have hst : ∀ b ∈ t, s ≤ b := (List.pairwise_cons.mp hs).1
      have ht : t.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      by_cases has : a ≤ s
      · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) t has]
        have hrec := listInterlaces_self_orderedInsert s ht
        rw [orderedInsert_eq_cons_of_forall_le hst] at hrec
        exact ⟨has, le_rfl, hrec⟩
      · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) t has]
        have hrec := listInterlaces_self_orderedInsert a ht
        cases htail : t.orderedInsert (· ≤ ·) a with
        | nil =>
            have := congrArg List.length htail
            simp [List.orderedInsert_length] at this
        | cons r rs =>
            rw [htail] at hrec
            refine ⟨le_rfl, ?_, hrec⟩
            have hr : r ∈ t.orderedInsert (· ≤ ·) a := by rw [htail]; exact List.mem_cons_self
            rcases List.mem_cons.mp ((List.perm_orderedInsert _ a t).mem_iff.mp hr) with h | h
            · rw [h]; exact le_of_lt (lt_of_not_ge has)
            · exact hst r h

/-- **Multiplying by a linear factor interlaces.**  If `f` is nonzero and splits
and `L` has degree one, then `f` interlaces `L * f`. -/
theorem interlaces_self_mul_of_natDegree_eq_one {f L : ℝ[X]} (hf : f ≠ 0) (hs : f.Splits)
    (hL : L.natDegree = 1) : Interlaces f (L * f) := by
  have hL0 : L ≠ 0 := by
    rintro rfl
    simp at hL
  have hLf : L * f ≠ 0 := mul_ne_zero hL0 hf
  have hLs : L.Splits := Splits.of_natDegree_le_one (by rw [hL])
  obtain ⟨r, hr⟩ : ∃ r, L.roots = {r} := by
    have hcard : L.roots.card = 1 := by
      rw [← hL]; exact (splits_iff_card_roots.mp hLs)
    exact Multiset.card_eq_one.mp hcard
  set ss := f.roots.sort (· ≤ ·) with hss
  have hsorted : ss.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  refine ⟨⟨hLf, hLs.mul hs⟩, ⟨hf, hs⟩, ?_, ss.orderedInsert (· ≤ ·) r, ss, ?_, hsorted, ?_,
    Multiset.sort_eq _ _, listInterlaces_self_orderedInsert r hsorted⟩
  · rw [natDegree_mul hL0 hf, hL]; ring
  · exact hsorted.orderedInsert r ss
  · rw [roots_mul hLf, hr, Multiset.singleton_add]
    rw [show (r ::ₘ f.roots) = ((r :: ss : List ℝ) : Multiset ℝ) by
      rw [← Multiset.cons_coe, hss, Multiset.sort_eq]]
    exact Multiset.coe_eq_coe.mpr (List.perm_orderedInsert _ r ss)

section Sequence

variable {P L : ℕ → ℝ[X]}

/-- Every member of a product sequence is nonzero and splits. -/
theorem productSequence_ne_zero_and_splits (hL : ∀ n, (L n).natDegree = 1)
    (h0 : P 0 ≠ 0) (hs0 : (P 0).Splits) (hstep : ∀ n, P (n + 1) = L n * P n) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits
  | 0 => ⟨h0, hs0⟩
  | n + 1 => by
      obtain ⟨hne, hs⟩ := productSequence_ne_zero_and_splits hL h0 hs0 hstep n
      exact (hstep n ▸ (interlaces_self_mul_of_natDegree_eq_one hne hs (hL n)).1)

/-- **Degrees in a product sequence.** -/
theorem productSequence_natDegree (hL : ∀ n, (L n).natDegree = 1)
    (h0 : P 0 ≠ 0) (hs0 : (P 0).Splits) (hstep : ∀ n, P (n + 1) = L n * P n) :
    ∀ n, (P n).natDegree = (P 0).natDegree + n
  | 0 => by simp
  | n + 1 => by
      have hne := (productSequence_ne_zero_and_splits hL h0 hs0 hstep n).1
      have hL0 : L n ≠ 0 := by
        intro h
        have := hL n
        rw [h] at this
        simp at this
      rw [hstep n, natDegree_mul hL0 hne, hL n,
        productSequence_natDegree hL h0 hs0 hstep n]
      ring

/-- **Consecutive members of a product sequence interlace.** -/
theorem productSequence_interlaces (hL : ∀ n, (L n).natDegree = 1)
    (h0 : P 0 ≠ 0) (hs0 : (P 0).Splits) (hstep : ∀ n, P (n + 1) = L n * P n) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  obtain ⟨hne, hs⟩ := productSequence_ne_zero_and_splits hL h0 hs0 hstep n
  rw [hstep n]
  exact interlaces_self_mul_of_natDegree_eq_one hne hs (hL n)

end Sequence

end RealRooted
