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

/-- Rows `P m = c m · F · q ^ (m + e)` with a linear `q` and a real-rooted `F`: consecutive
nonzero rows differ by the factor `(c (m + 1) / c m) · q`, so they interlace. -/
theorem interlaces_of_forall_eq_C_mul_pow {P : ℕ → ℝ[X]} {F q : ℝ[X]} {e : ℕ}
    (hform : ∀ m, ∃ c : ℝ, P m = C c * (F * q ^ (m + e))) (hne : ∀ m, P m ≠ 0)
    (hF : F.Splits) (hq : q.natDegree = 1) (m : ℕ) : Interlaces (P m) (P (m + 1)) := by
  obtain ⟨c, hc⟩ := hform m
  obtain ⟨c', hc'⟩ := hform (m + 1)
  have hc0 : c ≠ 0 := by rintro rfl; exact hne m (by simp [hc])
  have hc'0 : c' ≠ 0 := by rintro rfl; exact hne (m + 1) (by simp [hc'])
  have hstep : P (m + 1) = (C (c' / c) * q) * P m := by
    rw [hc', hc, show m + 1 + e = m + e + 1 by lia, pow_succ]
    have : C (c' / c) * C c = C c' := by rw [← C_mul, div_mul_cancel₀ _ hc0]
    linear_combination (F * q ^ (m + e) * q) * this.symm
  have hqs : q.Splits := Splits.of_natDegree_le_one (by rw [hq])
  have hs : (P m).Splits := by
    rw [hc]; exact (Splits.C c).mul (hF.mul (hqs.pow _))
  have hL : (C (c' / c) * q).natDegree = 1 := by
    rw [natDegree_C_mul (div_ne_zero hc'0 hc0), hq]
  rw [hstep]
  exact interlaces_self_mul_of_natDegree_eq_one (hne m) hs hL

/-- A three-term recurrence whose multipliers are `α n · q` and `β n · q ^ 2` keeps the form
`P m = c m · F · q ^ (m + e)` of its first two rows. -/
theorem forall_eq_C_mul_pow_of_rec2 {P : ℕ → ℝ[X]} {F q : ℝ[X]} {e : ℕ} {α β : ℕ → ℝ}
    (hrec : ∀ n, P (n + 2) = C (α n) * q * P (n + 1) + C (β n) * q ^ 2 * P n)
    (h0 : ∃ c : ℝ, P 0 = C c * (F * q ^ (0 + e)))
    (h1 : ∃ c : ℝ, P 1 = C c * (F * q ^ (1 + e))) :
    ∀ m, ∃ c : ℝ, P m = C c * (F * q ^ (m + e)) := by
  have key : ∀ m, (∃ c : ℝ, P m = C c * (F * q ^ (m + e))) ∧
      ∃ c : ℝ, P (m + 1) = C c * (F * q ^ (m + 1 + e)) := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ m ih =>
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
        refine ⟨⟨b, hb⟩, ⟨α m * b + β m * a, ?_⟩⟩
        rw [hrec, ha, hb, show m + 1 + 1 + e = m + e + 2 by lia,
          show m + 1 + e = m + e + 1 by lia]
        simp only [map_add, map_mul]
        ring
  exact fun m => (key m).1

/-- An order-three recurrence whose multipliers are `α n · q`, `β n · q ^ 2` and
`γ n · q ^ 3` keeps the form `P m = c m · F · q ^ (m + e)` of its first three rows. -/
theorem forall_eq_C_mul_pow_of_rec3 {P : ℕ → ℝ[X]} {F q : ℝ[X]} {e : ℕ} {α β γ : ℕ → ℝ}
    (hrec : ∀ n, P (n + 3) =
      C (α n) * q * P (n + 2) + C (β n) * q ^ 2 * P (n + 1) + C (γ n) * q ^ 3 * P n)
    (h0 : ∃ c : ℝ, P 0 = C c * (F * q ^ (0 + e)))
    (h1 : ∃ c : ℝ, P 1 = C c * (F * q ^ (1 + e)))
    (h2 : ∃ c : ℝ, P 2 = C c * (F * q ^ (2 + e))) :
    ∀ m, ∃ c : ℝ, P m = C c * (F * q ^ (m + e)) := by
  have key : ∀ m, (∃ c : ℝ, P m = C c * (F * q ^ (m + e))) ∧
      (∃ c : ℝ, P (m + 1) = C c * (F * q ^ (m + 1 + e))) ∧
      ∃ c : ℝ, P (m + 2) = C c * (F * q ^ (m + 2 + e)) := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1, h2⟩
    | succ m ih =>
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩⟩ := ih
        refine ⟨⟨b, hb⟩, ⟨d, by rw [show m + 1 + 1 = m + 2 by lia, hd]⟩,
          ⟨α m * d + β m * b + γ m * a, ?_⟩⟩
        rw [show m + 1 + 2 = m + 3 by lia, hrec, ha, hb, hd,
          show m + 3 + e = m + e + 3 by lia, show m + 2 + e = m + e + 2 by lia,
          show m + 1 + e = m + e + 1 by lia]
        simp only [map_add, map_mul]
        ring
  exact fun m => (key m).1

end RealRooted
