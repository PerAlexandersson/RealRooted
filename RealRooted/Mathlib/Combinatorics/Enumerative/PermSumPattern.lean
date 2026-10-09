import Mathlib.Data.Fintype.Perm
import RealRooted.Mathlib.Combinatorics.Enumerative.Pattern
import RealRooted.Mathlib.Combinatorics.Enumerative.PermSum

/-!
# Pattern containment in direct and skew sums

A pattern that is neither a direct sum nor a skew sum of two nonempty blocks is contained in a
direct (or skew) sum only through one of the two blocks.  In particular `2413` and `3142`
are avoided by `σ ⊕ τ` and `σ ⊖ τ` exactly when both `σ` and `τ` avoid them, so the class of
separable permutations is closed under direct and skew sums.
-/

namespace List

variable {α β : Type*} [LT α] [LT β]
  [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]

/-- A word is a direct sum word when it splits at a proper position into a nonempty prefix
whose entries are all below the entries of the nonempty suffix. -/
def IsDirectSumWord (p : List β) : Prop :=
  ∃ k < p.length, 0 < k ∧ ∀ x ∈ p.take k, ∀ y ∈ p.drop k, x < y

/-- A word is a skew sum word when it splits at a proper position into a nonempty prefix
whose entries are all above the entries of the nonempty suffix. -/
def IsSkewSumWord (p : List β) : Prop :=
  ∃ k < p.length, 0 < k ∧ ∀ x ∈ p.take k, ∀ y ∈ p.drop k, y < x

instance (p : List β) : Decidable p.IsDirectSumWord := by
  unfold IsDirectSumWord
  infer_instance

instance (p : List β) : Decidable p.IsSkewSumWord := by
  unfold IsSkewSumWord
  infer_instance

/-- Entries of same-order-type lists compare in the same way at every position. -/
theorem sameOrderType_getElem_lt_iff {l : List α} {m : List β} (h : l.SameOrderType m)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
    l[i] < l[j] ↔ m[i]'(sameOrderType_length h ▸ hi) < m[j]'(sameOrderType_length h ▸ hj) := by
  have hlen := sameOrderType_length h
  unfold SameOrderType sameOrderTypeBool at h
  simp only [dite_eq_left hlen] at h
  have := of_decide_eq_true h ⟨i, hi⟩ ⟨j, hj⟩
  simpa using this

/-- An occurrence of `p` in `a ++ b` either lies in one block or splits into two
nonempty pieces of the two blocks. -/
private theorem containsPattern_append_cases {a b : List α} {p : List β}
    (h : (a ++ b).ContainsPattern p) :
    a.ContainsPattern p ∨ b.ContainsPattern p ∨
      ∃ s₁ s₂, s₁ <+ a ∧ s₂ <+ b ∧ s₁ ≠ [] ∧ s₂ ≠ [] ∧ (s₁ ++ s₂).SameOrderType p := by
  rw [containsPattern_iff] at h
  obtain ⟨s, hs, hsp⟩ := h
  obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hs
  by_cases e₁ : s₁ = []
  · right
    left
    rw [containsPattern_iff]
    exact ⟨s₂, h₂, by simpa only [e₁, List.nil_append] using hsp⟩
  by_cases e₂ : s₂ = []
  · left
    rw [containsPattern_iff]
    exact ⟨s₁, h₁, by simpa only [e₂, List.append_nil] using hsp⟩
  exact Or.inr (Or.inr ⟨s₁, s₂, h₁, h₂, e₁, e₂, hsp⟩)

/-- An occurrence of `p` split into two nonempty pieces, the first below the second,
makes `p` a direct sum word. -/
private theorem isDirectSumWord_of_sameOrderType_append {s₁ s₂ : List α} {p : List β}
    (e₁ : s₁ ≠ []) (e₂ : s₂ ≠ []) (hlt : ∀ x ∈ s₁, ∀ y ∈ s₂, x < y)
    (h : (s₁ ++ s₂).SameOrderType p) : p.IsDirectSumWord := by
  have hlen := sameOrderType_length h
  have h₁ : 0 < s₁.length := List.length_pos_iff.mpr e₁
  have h₂ : 0 < s₂.length := List.length_pos_iff.mpr e₂
  rw [List.length_append] at hlen
  refine ⟨s₁.length, by lia, h₁, ?_⟩
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [List.length_take, List.length_drop] at hi hj
  simp only [List.getElem_take, List.getElem_drop]
  have hi' : i < (s₁ ++ s₂).length := by
    rw [List.length_append]
    lia
  have hj' : s₁.length + j < (s₁ ++ s₂).length := by
    rw [List.length_append]
    lia
  have key := (sameOrderType_getElem_lt_iff h hi' hj').mp
  apply key
  rw [List.getElem_append_left (by lia), List.getElem_append_right (by lia)]
  simp only [Nat.add_sub_cancel_left]
  exact hlt _ (List.getElem_mem _) _ (List.getElem_mem _)

/-- An occurrence of `p` split into two nonempty pieces, the first above the second,
makes `p` a skew sum word. -/
private theorem isSkewSumWord_of_sameOrderType_append {s₁ s₂ : List α} {p : List β}
    (e₁ : s₁ ≠ []) (e₂ : s₂ ≠ []) (hlt : ∀ x ∈ s₁, ∀ y ∈ s₂, y < x)
    (h : (s₁ ++ s₂).SameOrderType p) : p.IsSkewSumWord := by
  have hlen := sameOrderType_length h
  have h₁ : 0 < s₁.length := List.length_pos_iff.mpr e₁
  have h₂ : 0 < s₂.length := List.length_pos_iff.mpr e₂
  rw [List.length_append] at hlen
  refine ⟨s₁.length, by lia, h₁, ?_⟩
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [List.length_take, List.length_drop] at hi hj
  simp only [List.getElem_take, List.getElem_drop]
  have hi' : i < (s₁ ++ s₂).length := by
    rw [List.length_append]
    lia
  have hj' : s₁.length + j < (s₁ ++ s₂).length := by
    rw [List.length_append]
    lia
  have key := (sameOrderType_getElem_lt_iff h hj' hi').mp
  apply key
  rw [List.getElem_append_right (by lia), List.getElem_append_left (by lia)]
  simp only [Nat.add_sub_cancel_left]
  exact hlt _ (List.getElem_mem _) _ (List.getElem_mem _)

/-- If `p` is not a direct sum word and every entry of `a` is below every entry of `b`,
then `p` occurs in `a ++ b` exactly when it occurs in `a` or in `b`. -/
theorem containsPattern_append_iff_of_forall_lt {a b : List α} {p : List β}
    (hab : ∀ x ∈ a, ∀ y ∈ b, x < y) (hp : ¬ p.IsDirectSumWord) :
    (a ++ b).ContainsPattern p ↔ a.ContainsPattern p ∨ b.ContainsPattern p := by
  constructor
  · intro h
    rcases containsPattern_append_cases h with h | h | ⟨s₁, s₂, h₁, h₂, e₁, e₂, hs⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (isDirectSumWord_of_sameOrderType_append e₁ e₂
        (fun x hx y hy => hab x (h₁.subset hx) y (h₂.subset hy)) hs) hp
  · rintro (h | h)
    · exact containsPattern_of_sublist (List.sublist_append_left a b) h
    · exact containsPattern_of_sublist (List.sublist_append_right a b) h

/-- If `p` is not a skew sum word and every entry of `a` is above every entry of `b`,
then `p` occurs in `a ++ b` exactly when it occurs in `a` or in `b`. -/
theorem containsPattern_append_iff_of_forall_gt {a b : List α} {p : List β}
    (hab : ∀ x ∈ a, ∀ y ∈ b, y < x) (hp : ¬ p.IsSkewSumWord) :
    (a ++ b).ContainsPattern p ↔ a.ContainsPattern p ∨ b.ContainsPattern p := by
  constructor
  · intro h
    rcases containsPattern_append_cases h with h | h | ⟨s₁, s₂, h₁, h₂, e₁, e₂, hs⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (isSkewSumWord_of_sameOrderType_append e₁ e₂
        (fun x hx y hy => hab x (h₁.subset hx) y (h₂.subset hy)) hs) hp
  · rintro (h | h)
    · exact containsPattern_of_sublist (List.sublist_append_left a b) h
    · exact containsPattern_of_sublist (List.sublist_append_right a b) h

/-- Order-preserving relabelling of a word does not change which patterns it contains. -/
theorem containsPattern_map_iff_of_strictMono {γ : Type*} [LT γ]
    [DecidableRel (· < · : γ → γ → Prop)] {f : γ → α} {l : List γ} {p : List β}
    (hf : ∀ ⦃a b : γ⦄, a < b ↔ f a < f b) :
    (l.map f).ContainsPattern p ↔ l.ContainsPattern p := by
  rw [containsPattern_iff, containsPattern_iff]
  constructor
  · rintro ⟨s, hs, hsp⟩
    obtain ⟨s', hs', rfl⟩ := List.sublist_map_iff.mp hs
    exact ⟨s', hs',
      sameOrderType_trans (sameOrderType_symm (sameOrderType_map_of_strictMono hf)) hsp⟩
  · rintro ⟨s, hs, hsp⟩
    exact ⟨s.map f, hs.map f, sameOrderType_trans (sameOrderType_map_of_strictMono hf) hsp⟩

end List

namespace Equiv.Perm

/-- If `p` is not a direct sum word, then `p` occurs in a direct sum exactly when it occurs
in one of the two summands. -/
theorem directSum_containsPattern_iff {m n k : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (p : Perm (Fin k)) (hp : ¬ (List.ofFn p).IsDirectSumWord) :
    (σ.directSum τ).ContainsPattern p ↔ σ.ContainsPattern p ∨ τ.ContainsPattern p := by
  unfold ContainsPattern
  rw [directSum_toList, List.containsPattern_append_iff_of_forall_lt _ hp,
    List.containsPattern_map_iff_of_strictMono, List.containsPattern_map_iff_of_strictMono]
  · intro a b
    simp only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  · intro a b
    simp only [Fin.lt_def, Fin.val_castAdd]
  · intro x hx y hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    have := a.isLt
    lia

/-- If `p` is not a skew sum word, then `p` occurs in a skew sum exactly when it occurs
in one of the two summands. -/
theorem skewSum_containsPattern_iff {m n k : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (p : Perm (Fin k)) (hp : ¬ (List.ofFn p).IsSkewSumWord) :
    (σ.skewSum τ).ContainsPattern p ↔ σ.ContainsPattern p ∨ τ.ContainsPattern p := by
  unfold ContainsPattern
  rw [skewSum_toList, List.containsPattern_append_iff_of_forall_gt _ hp,
    List.containsPattern_map_iff_of_strictMono, List.containsPattern_map_iff_of_strictMono]
  · intro a b
    simp only [Function.comp_apply, Fin.lt_def, Fin.val_cast, Fin.val_castAdd]
  · intro a b
    simp only [Fin.lt_def, Fin.val_cast, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  · intro x hx y hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
    simp only [Function.comp_apply, Fin.lt_def, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    have := b.isLt
    lia

/-- A direct sum avoids `p` exactly when both summands do, if `p` is not a direct sum word. -/
theorem directSum_avoids_iff {m n k : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (p : Perm (Fin k)) (hp : ¬ (List.ofFn p).IsDirectSumWord) :
    (σ.directSum τ).Avoids p ↔ σ.Avoids p ∧ τ.Avoids p := by
  unfold Avoids
  rw [directSum_containsPattern_iff σ τ p hp, not_or]

/-- A skew sum avoids `p` exactly when both summands do, if `p` is not a skew sum word. -/
theorem skewSum_avoids_iff {m n k : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (p : Perm (Fin k)) (hp : ¬ (List.ofFn p).IsSkewSumWord) :
    (σ.skewSum τ).Avoids p ↔ σ.Avoids p ∧ τ.Avoids p := by
  unfold Avoids
  rw [skewSum_containsPattern_iff σ τ p hp, not_or]

end Equiv.Perm

namespace Equiv.Perm

/-- The word `2413` is not a direct sum word. -/
theorem not_isDirectSumWord_pattern2413 : ¬ (List.ofFn pattern2413).IsDirectSumWord := by
  decide

/-- The word `2413` is not a skew sum word. -/
theorem not_isSkewSumWord_pattern2413 : ¬ (List.ofFn pattern2413).IsSkewSumWord := by
  decide

/-- The word `3142` is not a direct sum word. -/
theorem not_isDirectSumWord_pattern3142 : ¬ (List.ofFn pattern3142).IsDirectSumWord := by
  decide

/-- The word `3142` is not a skew sum word. -/
theorem not_isSkewSumWord_pattern3142 : ¬ (List.ofFn pattern3142).IsSkewSumWord := by
  decide

/-- A direct sum avoids `2413` exactly when both summands do. -/
theorem directSum_avoids_pattern2413_iff {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) :
    (σ.directSum τ).Avoids pattern2413 ↔ σ.Avoids pattern2413 ∧ τ.Avoids pattern2413 :=
  Equiv.Perm.directSum_avoids_iff σ τ _ not_isDirectSumWord_pattern2413

/-- A direct sum avoids `3142` exactly when both summands do. -/
theorem directSum_avoids_pattern3142_iff {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) :
    (σ.directSum τ).Avoids pattern3142 ↔ σ.Avoids pattern3142 ∧ τ.Avoids pattern3142 :=
  Equiv.Perm.directSum_avoids_iff σ τ _ not_isDirectSumWord_pattern3142

/-- A skew sum avoids `2413` exactly when both summands do. -/
theorem skewSum_avoids_pattern2413_iff {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) :
    (σ.skewSum τ).Avoids pattern2413 ↔ σ.Avoids pattern2413 ∧ τ.Avoids pattern2413 :=
  Equiv.Perm.skewSum_avoids_iff σ τ _ not_isSkewSumWord_pattern2413

/-- A skew sum avoids `3142` exactly when both summands do. -/
theorem skewSum_avoids_pattern3142_iff {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) :
    (σ.skewSum τ).Avoids pattern3142 ↔ σ.Avoids pattern3142 ∧ τ.Avoids pattern3142 :=
  Equiv.Perm.skewSum_avoids_iff σ τ _ not_isSkewSumWord_pattern3142

/-! ### Small kernel checks -/

example :
    (Equiv.Perm.directSum (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 3) 2)).Avoids
      pattern2413 := by
  decide

example :
    (Equiv.Perm.skewSum (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 3) 2)).Avoids
      pattern3142 := by
  decide

example : ¬ (Equiv.Perm.directSum pattern2413 (Equiv.refl (Fin 1))).Avoids pattern2413 := by
  decide

example : ¬ (Equiv.Perm.skewSum (Equiv.refl (Fin 1)) pattern3142).Avoids pattern3142 := by
  decide

example : ¬ (Equiv.Perm.directSum (Equiv.refl (Fin 2)) pattern3142).Avoids pattern3142 := by
  decide

end Equiv.Perm
