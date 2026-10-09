import RealRooted.Mathlib.Combinatorics.Enumerative.Pattern
import RealRooted.Mathlib.Combinatorics.Enumerative.Excedance

/-!
# Pattern occurrences as a statistic

Pattern occurrences are counted by their position sets.  Thus equal-valued
subwords at different positions contribute with their multiplicity.
-/

namespace List

universe u v

variable {α : Type u} {β : Type v}

/-- The number of occurrences of a pattern in a word, counted by position sets. -/
def patternCount [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (p : List β) : ℕ :=
  ((l.sublistsLen p.length).filter (fun s => decide (s.SameOrderType p))).length

/-- A word has no occurrences of a pattern exactly when it avoids that pattern. -/
theorem patternCount_eq_zero_iff [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (p : List β) :
    l.patternCount p = 0 ↔ l.Avoids p := by
  unfold patternCount List.Avoids List.ContainsPattern
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h hcontains
    obtain ⟨s, hs, hst⟩ := List.any_eq_true.mp hcontains
    have hlen : s.length = p.length :=
      sameOrderType_length (of_decide_eq_true hst)
    have hslen : s ∈ l.sublistsLen p.length := by
      rw [List.mem_sublistsLen]
      exact ⟨(List.mem_sublists.mp hs), hlen⟩
    exact h s hslen hst
  · intro h s hs hst
    have hsubl : s ∈ l.sublists := by
      rw [List.mem_sublists]
      exact (List.mem_sublistsLen.mp hs).1
    exact h (List.any_eq_true.mpr ⟨s, hsubl, hst⟩)

/-- Fixed-length sublists commute with mapping. -/
private theorem sublistsLen_map (f : α → β) (n : ℕ) (l : List α) :
    (l.map f).sublistsLen n = (l.sublistsLen n).map (List.map f) := by
  induction l generalizing n with
  | nil =>
    cases n <;> simp
  | cons a l ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      simp only [List.map_cons]
      rw [List.sublistsLen_succ_cons, List.sublistsLen_succ_cons, ih (n + 1),
        ih n]
      simp only [List.map_append, List.map_map]
      congr 1

/-- Strictly decreasing relabellings preserve pattern counts after relabelling
both the word and the pattern. -/
theorem patternCount_map_of_strictAnti [LinearOrder α] [LinearOrder β]
    {f : α → α} {g : β → β} (hf : StrictAnti f) (hg : StrictAnti g)
    (l : List α) (p : List β) :
    (l.map f).patternCount (p.map g) = l.patternCount p := by
  unfold patternCount
  simp only [List.length_map]
  rw [sublistsLen_map]
  rw [List.filter_map]
  have hfilter :
      List.filter
          ((fun s => decide (s.SameOrderType (p.map g))) ∘
            List.map f) (l.sublistsLen p.length) =
        List.filter (fun s => decide (s.SameOrderType p))
          (l.sublistsLen p.length) := by
    apply List.filter_congr
    intro s hs
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, decide_eq_true_eq]
    exact (sameOrderType_map_of_strictAnti_iff hf hg).symm
  rw [hfilter]
  simp only [List.length_map]

private theorem patternCount_block_perm {γ : Type} (a b c d : List γ) :
    (a ++ b ++ c ++ d).Perm (b ++ d ++ a ++ c) := by
  have h₁ : (a ++ b ++ c ++ d).Perm (b ++ a ++ c ++ d) := by
    simpa only [List.append_assoc] using
      (List.Perm.append_right (c ++ d) (List.perm_append_comm : (a ++ b).Perm (b ++ a)))
  have h₂ : (b ++ a ++ c ++ d).Perm (b ++ a ++ d ++ c) := by
    simpa only [List.append_assoc] using
      (List.Perm.append_left (b ++ a)
        (List.perm_append_comm : (c ++ d).Perm (d ++ c)))
  have h₃ : (b ++ a ++ d ++ c).Perm (b ++ d ++ a ++ c) := by
    simpa only [List.append_assoc] using
      (List.Perm.append_left b
        (List.Perm.append_right c
          (List.perm_append_comm : (a ++ d).Perm (d ++ a))))
  exact h₁.trans (h₂.trans h₃)

private theorem sublistsLen_append_one_perm (n : ℕ) (l : List α) (a : α) :
    (List.sublistsLen n (l ++ [a])).Perm
      (match n with
      | 0 => [[]]
      | n + 1 =>
        (List.sublistsLen n l).map (fun s => s ++ [a]) ++
          List.sublistsLen (n + 1) l) := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => simp
    | succ n =>
      cases n <;> simp
  | cons b l ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      cases n with
      | zero =>
        simp [List.sublistsLen_one, List.reverse_append]
      | succ n =>
        simp only [List.cons_append, List.sublistsLen_succ_cons]
        simp only [List.map_append, List.map_map, List.append_assoc]
        have hleft₀ := (ih (n + 2)).append
          ((ih (n + 1)).map (List.cons b))
        have hleft :
            (List.sublistsLen (n + 2) (l ++ [a]) ++
              List.map (List.cons b) (List.sublistsLen (n + 1) (l ++ [a]))).Perm
            ((List.sublistsLen (n + 1) l).map (fun s => s ++ [a]) ++
              List.sublistsLen (n + 2) l ++
              List.map (List.cons b)
                ((List.sublistsLen n l).map (fun s => s ++ [a]) ++
                  List.sublistsLen (n + 1) l)) := by
          simpa using hleft₀
        have hright :
            ((List.sublistsLen (n + 1) l).map (fun s => s ++ [a]) ++
              List.sublistsLen (n + 2) l ++
              List.map (List.cons b)
                ((List.sublistsLen n l).map (fun s => s ++ [a]) ++
                  List.sublistsLen (n + 1) l)).Perm
            ((List.sublistsLen (n + 1) (b :: l)).map (fun s => s ++ [a]) ++
              List.sublistsLen (n + 2) (b :: l)) := by
          rw [List.sublistsLen_succ_cons, List.sublistsLen_succ_cons]
          have hright₀ := List.Perm.append_left
            ((List.sublistsLen (n + 1) l).map (fun s => s ++ [a]))
            (List.Perm.append_right
              (List.map (List.cons b) (List.sublistsLen (n + 1) l))
              (List.perm_append_comm :
                (List.sublistsLen (n + 2) l ++
                  List.map (List.cons b)
                    ((List.sublistsLen n l).map (fun s => s ++ [a]))).Perm
                (List.map (List.cons b)
                    ((List.sublistsLen n l).map (fun s => s ++ [a])) ++
                  List.sublistsLen (n + 2) l)))
          have hmap :
              List.map (List.cons b)
                  (List.map (fun s => s ++ [a]) (List.sublistsLen n l)) =
                List.map (fun s => s ++ [a])
                  (List.map (List.cons b) (List.sublistsLen n l)) := by
            rw [List.map_map, List.map_map]
            congr 1
          nth_rewrite 2 [hmap] at hright₀
          simpa only [Nat.add_assoc, List.map_append, List.append_assoc] using hright₀
        simpa [List.map_map, Function.comp_apply, List.append_assoc] using
          hleft.trans hright

private theorem reverse_sublistsLen_perm (n : ℕ) (l : List α) :
    (List.sublistsLen n l.reverse).Perm
      ((List.sublistsLen n l).reverse.map List.reverse) := by
  induction l generalizing n with
  | nil =>
    cases n <;> simp
  | cons a l ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      rw [List.reverse_cons]
      have h₁₀ := sublistsLen_append_one_perm (n + 1) l.reverse a
      have h₁ :
          (List.sublistsLen (n + 1) (l.reverse ++ [a])).Perm
            (List.map (fun s => s ++ [a]) (List.sublistsLen n l.reverse) ++
              List.sublistsLen (n + 1) l.reverse) := by
        simpa using h₁₀
      have h₁' := h₁.trans (((ih n).map (fun s => s ++ [a])).append (ih (n + 1)))
      have hmap :
          List.map (fun s => s ++ [a])
              ((List.sublistsLen n l).reverse.map List.reverse) =
            (List.map (List.cons a) (List.sublistsLen n l)).reverse.map
              List.reverse := by
        simp
      rw [hmap] at h₁'
      simpa [List.sublistsLen_succ_cons, List.map_append, List.map_map,
        List.append_assoc] using h₁'

/-- Reversing both words and patterns preserves the number of occurrences. -/
theorem patternCount_reverse [LinearOrder α] [LinearOrder β]
    (l : List α) (p : List β) :
    l.reverse.patternCount p.reverse = l.patternCount p := by
  unfold patternCount
  simp only [List.length_reverse]
  have hperm := reverse_sublistsLen_perm p.length l
  have hfiltered := hperm.filter (fun s => decide (s.SameOrderType p.reverse))
  have hlen := hfiltered.length_eq
  rw [List.filter_map] at hlen
  have hfilter :
      List.filter
          ((fun s => decide (s.SameOrderType p.reverse)) ∘ List.reverse)
          (l.sublistsLen p.length).reverse =
        List.filter (fun s => decide (s.SameOrderType p))
          (l.sublistsLen p.length).reverse := by
    apply List.filter_congr
    intro s hs
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, decide_eq_true_eq]
    exact (sameOrderType_reverse_iff (l := s) (m := p)).symm
  rw [hfilter] at hlen
  have hrev := (List.reverse_perm (l.sublistsLen p.length)).filter
    (fun s => decide (s.SameOrderType p))
  have hrevlen := hrev.length_eq
  have hlen' : (List.filter (fun s => decide (s.SameOrderType p.reverse))
      (l.reverse.sublistsLen p.length)).length =
      (List.filter (fun s => decide (s.SameOrderType p))
        (l.sublistsLen p.length).reverse).length := by
    simpa only [List.length_map] using hlen
  exact hlen'.trans hrevlen

end List

/-- Pattern count for a permutation is the count for its one-line word. -/
def Equiv.Perm.patternCount {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin k)) : ℕ :=
  (List.ofFn σ).patternCount (List.ofFn τ)

@[simp] theorem Equiv.Perm.patternCount_eq_zero_iff {n k : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    σ.patternCount τ = 0 ↔ σ.Avoids τ := by
  exact List.patternCount_eq_zero_iff _ _

private theorem Equiv.Perm.ofFn_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    List.ofFn (Equiv.Perm.complement σ) = (List.ofFn σ).map Fin.rev := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp [Equiv.Perm.complement, Fin.revPerm_apply]

/-- The one-line word of a reversed permutation is the reversed word. -/
private theorem Equiv.Perm.ofFn_reverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    List.ofFn (Equiv.Perm.reverse σ) = (List.ofFn σ).reverse := by
  change List.ofFn (fun i : Fin n => σ i.rev) = (List.ofFn σ).reverse
  apply List.ext_get
  · simp
  · intro i hi hj
    have hlen : (List.ofFn σ).length = n := List.length_ofFn
    have hi_n : i < n := by
      simpa only [List.length_ofFn] using hi
    have hbound : (List.ofFn σ).length - 1 - i < (List.ofFn σ).length := by
      simpa only [hlen] using (show n - 1 - i < n by lia)
    rw [List.get_ofFn, List.get_reverse' _ _ hbound, List.get_ofFn]
    apply congrArg σ
    apply Fin.ext
    rw [Fin.val_rev, Fin.val_cast, Fin.val_cast]
    simp only [hlen]
    lia

/-- Complementing both permutations preserves their pattern count. -/
theorem Equiv.Perm.patternCount_complement {n k : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    σ.patternCount τ = (σ.complement).patternCount (τ.complement) := by
  unfold Equiv.Perm.patternCount
  rw [Equiv.Perm.ofFn_complement, Equiv.Perm.ofFn_complement]
  exact (List.patternCount_map_of_strictAnti Fin.rev_strictAnti
    Fin.rev_strictAnti _ _).symm

/-- Reversing both permutations preserves their pattern count. -/
theorem Equiv.Perm.patternCount_reverse {n k : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    (σ.reverse).patternCount (τ.reverse) = σ.patternCount τ := by
  unfold Equiv.Perm.patternCount
  rw [Equiv.Perm.ofFn_reverse, Equiv.Perm.ofFn_reverse]
  exact List.patternCount_reverse _ _

private def pattern21 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def pattern12 : Equiv.Perm (Fin 2) := Equiv.refl (Fin 2)

/-- The 21-occurrence check agrees with inversion count on permutations of
length four. -/
example : ∀ σ : Equiv.Perm (Fin 4), σ.patternCount pattern21 = σ.inversionCount := by
  decide

/-- Increasing and decreasing two-pattern occurrences partition the six pairs
of positions in permutations of length four. -/
example : ∀ σ : Equiv.Perm (Fin 4),
    σ.patternCount pattern12 + σ.patternCount pattern21 = 6 := by
  decide

/-- The reverse symmetry check on permutations of length four. -/
example : ∀ σ : Equiv.Perm (Fin 4), σ.patternCount pattern21 =
    (σ.reverse).patternCount (pattern21.reverse) := by
  decide
