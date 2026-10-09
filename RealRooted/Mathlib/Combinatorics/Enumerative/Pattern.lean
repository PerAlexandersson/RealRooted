import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Pattern containment and avoidance

This is a Mathlib-shaped staging module.  Positions in words and permutations are
zero-based.  A word contains a pattern when one of its (not necessarily
contiguous) sublists has the same strict order relations as the pattern.
-/

namespace List

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Two lists have the same order type when they have the same length and their
entries at every pair of positions have the same strict order relation. -/
def sameOrderTypeBool [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (m : List β) : Bool :=
  if h : l.length = m.length then
    decide (∀ i j : Fin l.length,
      l.get i < l.get j ↔ m.get (Fin.cast h i) < m.get (Fin.cast h j))
  else false

/-- `l.SameOrderType m`: `l` and `m` are order-isomorphic (same length, same strict comparisons
at every pair of positions). -/
def SameOrderType [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (m : List β) : Prop := sameOrderTypeBool l m = true

instance [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (m : List β) : Decidable (l.SameOrderType m) := by
  unfold SameOrderType
  infer_instance

/-- Same-order-type lists have equal lengths. -/
theorem sameOrderType_length [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {m : List β}
    (h : l.SameOrderType m) : l.length = m.length := by
  unfold SameOrderType sameOrderTypeBool at h
  split at h
  · assumption
  · simp at h

/-- A list has the same order type as itself. -/
theorem sameOrderType_refl [LT α] [DecidableRel (· < · : α → α → Prop)]
    (l : List α) : l.SameOrderType l := by
  unfold SameOrderType sameOrderTypeBool
  simp only [↓reduceDIte]
  apply decide_eq_true
  intro i j
  rfl

/-- Same order type is symmetric. -/
theorem sameOrderType_symm [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {m : List β}
    (h : l.SameOrderType m) : m.SameOrderType l := by
  have hlen := sameOrderType_length h
  unfold SameOrderType sameOrderTypeBool at h ⊢
  simp only [dite_eq_left hlen, dite_eq_left hlen.symm] at h ⊢
  apply decide_eq_true
  intro i j
  have hh := of_decide_eq_true h (Fin.cast hlen.symm i) (Fin.cast hlen.symm j)
  simpa only [Fin.cast_cast, Fin.cast_eq_self] using hh.symm

/-- Same order type is transitive. -/
theorem sameOrderType_trans [LT α] [LT β] [LT γ]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    [DecidableRel (· < · : γ → γ → Prop)] {l : List α} {m : List β}
    {n : List γ} (h₁ : l.SameOrderType m) (h₂ : m.SameOrderType n) :
    l.SameOrderType n := by
  have hlen₁ := sameOrderType_length h₁
  have hlen₂ := sameOrderType_length h₂
  unfold SameOrderType sameOrderTypeBool at h₁ h₂ ⊢
  simp only [dite_eq_left (hlen₁.trans hlen₂), dite_eq_left hlen₁, dite_eq_left hlen₂]
    at h₁ h₂ ⊢
  apply decide_eq_true
  intro i j
  have hh₁ := of_decide_eq_true h₁ i j
  have hh₂ := of_decide_eq_true h₂ (Fin.cast hlen₁ i) (Fin.cast hlen₁ j)
  rw [hh₁]
  simpa only [Fin.cast_cast, Fin.cast_eq_self] using hh₂

/-- Strictly increasing relabelling preserves order type. -/
theorem sameOrderType_map_of_strictMono [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {f : α → β} (hf : ∀ ⦃a b : α⦄, a < b ↔ f a < f b) {l : List α} :
    (l.map f).SameOrderType l := by
  unfold SameOrderType sameOrderTypeBool
  simp only [List.length_map, ↓reduceDIte]
  apply decide_eq_true
  intro i j
  have hi : (i : ℕ) < l.length := by simpa using i.isLt
  have hj : (j : ℕ) < l.length := by simpa using j.isLt
  let i' : Fin l.length := ⟨i, hi⟩
  let j' : Fin l.length := ⟨j, hj⟩
  have hgi : (l.map f).get i = f (l.get i') := by simp [i']
  have hgj : (l.map f).get j = f (l.get j') := by simp [j']
  rw [hgi, hgj]
  simpa [i', j'] using (hf (a := l.get i') (b := l.get j')).symm

/-- Strictly antitone relabellings preserve the order type after reversing both
order relations. -/
theorem sameOrderType_map_of_strictAnti_iff [LinearOrder α] [LinearOrder β]
    [LinearOrder γ] [LinearOrder δ] {f : α → β} {g : γ → δ}
    (hf : StrictAnti f) (hg : StrictAnti g)
    {l : List α} {m : List γ} :
    l.SameOrderType m ↔ (l.map f).SameOrderType (m.map g) := by
  constructor
  · intro h
    have hlen := sameOrderType_length h
    have hmap : (l.map f).length = (m.map g).length := by
      simpa only [List.length_map] using hlen
    unfold SameOrderType sameOrderTypeBool at h ⊢
    simp only [dite_eq_left hlen, dite_eq_left hmap] at h ⊢
    apply decide_eq_true
    intro i j
    have hi : (i : ℕ) < l.length := by simpa using i.isLt
    have hj : (j : ℕ) < l.length := by simpa using j.isLt
    let i' : Fin l.length := ⟨i, hi⟩
    let j' : Fin l.length := ⟨j, hj⟩
    let mi' : Fin m.length := Fin.cast hlen i'
    let mj' : Fin m.length := Fin.cast hlen j'
    have hgi : (l.map f).get i = f (l.get i') := by simp [i']
    have hgj : (l.map f).get j = f (l.get j') := by simp [j']
    have hmi : (m.map g).get (Fin.cast hmap i) = g (m.get mi') := by
      simp [mi', i']
    have hmj : (m.map g).get (Fin.cast hmap j) = g (m.get mj') := by
      simp [mj', j']
    rw [hgi, hgj, hmi, hmj]
    rw [hf.lt_iff_gt, hg.lt_iff_gt]
    have hh' := of_decide_eq_true h j' i'
    simpa [mi', mj'] using hh'
  · intro h
    have hmap : (l.map f).length = (m.map g).length := by
      exact sameOrderType_length h
    have hlen : l.length = m.length := by simpa only [List.length_map] using hmap
    unfold SameOrderType sameOrderTypeBool at h ⊢
    simp only [dite_eq_left hmap, dite_eq_left hlen] at h ⊢
    apply decide_eq_true
    intro i j
    have hi : (i : ℕ) < l.length := i.isLt
    have hj : (j : ℕ) < l.length := j.isLt
    let i' : Fin l.length := ⟨i, hi⟩
    let j' : Fin l.length := ⟨j, hj⟩
    let iF : Fin (l.map f).length := ⟨i, by simpa only [List.length_map] using hi⟩
    let jF : Fin (l.map f).length := ⟨j, by simpa only [List.length_map] using hj⟩
    let mi' : Fin m.length := Fin.cast hlen i'
    let mj' : Fin m.length := Fin.cast hlen j'
    have hgi : (l.map f).get iF = f (l.get i') := by simp [iF, i']
    have hgj : (l.map f).get jF = f (l.get j') := by simp [jF, j']
    have hmi : (m.map g).get (Fin.cast hmap iF) = g (m.get mi') := by
      simp [mi', iF, i']
    have hmj : (m.map g).get (Fin.cast hmap jF) = g (m.get mj') := by
      simp [mj', jF, j']
    have hh := of_decide_eq_true h jF iF
    rw [hgj, hgi, hmj, hmi] at hh
    rw [hf.lt_iff_gt, hg.lt_iff_gt] at hh
    simpa only [List.get_eq_getElem, i', j', mi', mj'] using hh

/-- Reversing both lists preserves their order type. -/
theorem sameOrderType_reverse [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {m : List β} (h : l.SameOrderType m) :
    l.reverse.SameOrderType m.reverse := by
  have hlen := sameOrderType_length h
  unfold SameOrderType sameOrderTypeBool at h ⊢
  simp only [List.length_reverse, dite_eq_left hlen] at h ⊢
  apply decide_eq_true
  intro i j
  have hrevlen : l.reverse.length = m.reverse.length := by
    simpa only [List.length_reverse] using hlen
  have hi : (i : ℕ) < l.length := by simpa only [List.length_reverse] using i.isLt
  have hj : (j : ℕ) < l.length := by simpa only [List.length_reverse] using j.isLt
  have hri : l.length - 1 - (i : ℕ) < l.length := by lia
  have hrj : l.length - 1 - (j : ℕ) < l.length := by lia
  let ri : Fin l.length := ⟨l.length - 1 - (i : ℕ), hri⟩
  let rj : Fin l.length := ⟨l.length - 1 - (j : ℕ), hrj⟩
  let mi : Fin m.reverse.length := Fin.cast hrevlen i
  let mj : Fin m.reverse.length := Fin.cast hrevlen j
  let rmi : Fin m.length := Fin.cast hlen ri
  let rmj : Fin m.length := Fin.cast hlen rj
  have hli : l.reverse.get i = l.get ri := by
    rw [List.get_reverse']
  have hlj : l.reverse.get j = l.get rj := by
    rw [List.get_reverse']
  have hmi_bound : m.length - 1 - (mi : ℕ) < m.length := by
    have hmi_lt : (mi : ℕ) < m.length := by
      simpa only [List.length_reverse] using mi.isLt
    lia
  have hmj_bound : m.length - 1 - (mj : ℕ) < m.length := by
    have hmj_lt : (mj : ℕ) < m.length := by
      simpa only [List.length_reverse] using mj.isLt
    lia
  have hmi : m.reverse.get mi = m.get rmi := by
    rw [List.get_reverse' m mi hmi_bound]
    apply congrArg m.get
    apply Fin.ext
    simp [mi, rmi, ri, hlen]
  have hmj : m.reverse.get mj = m.get rmj := by
    rw [List.get_reverse' m mj hmj_bound]
    apply congrArg m.get
    apply Fin.ext
    simp [mj, rmj, rj, hlen]
  rw [hli, hlj, hmi, hmj]
  simpa [rmi, rmj] using (of_decide_eq_true h ri rj)

/-- Reversal preserves and reflects same order type. -/
theorem sameOrderType_reverse_iff [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {m : List β} :
    l.SameOrderType m ↔ l.reverse.SameOrderType m.reverse := by
  constructor
  · exact sameOrderType_reverse
  · intro h
    have hh := sameOrderType_reverse h
    simpa only [List.reverse_reverse] using hh

/-- The computable predicate that a list contains a given pattern. -/
def ContainsPattern [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (p : List β) : Prop :=
  l.sublists.any (fun s => decide (s.SameOrderType p)) = true

instance [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (p : List β) : Decidable (l.ContainsPattern p) := by
  unfold ContainsPattern
  infer_instance

/-- A list avoids a given pattern when it does not contain it. -/
def Avoids [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (p : List β) : Prop :=
  ¬l.ContainsPattern p

instance [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (l : List α) (p : List β) : Decidable (l.Avoids p) := by
  unfold Avoids
  infer_instance

/-- The Boolean enumeration of sublists gives the usual existential definition
of pattern containment. -/
theorem containsPattern_iff [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {p : List β} : l.ContainsPattern p ↔
    ∃ s, s <+ l ∧ s.SameOrderType p := by
  unfold ContainsPattern
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, hs, hdec⟩
    exact ⟨s, (List.mem_sublists.mp hs), of_decide_eq_true hdec⟩
  · rintro ⟨s, hs, hst⟩
    exact ⟨s, List.mem_sublists.mpr hs, of_decide_eq_true (by simpa using hst)⟩

/-- Containment is reflexive. -/
theorem containsPattern_refl [LT α] [DecidableRel (· < · : α → α → Prop)]
    (l : List α) : l.ContainsPattern l := by
  rw [containsPattern_iff]
  exact ⟨l, List.Sublist.refl _, sameOrderType_refl _⟩

/-- Strictly antitone relabellings preserve pattern containment. -/
theorem containsPattern_map_of_strictAnti_iff [LinearOrder α] [LinearOrder β]
    [LinearOrder γ] [LinearOrder δ] {f : α → β} {g : γ → δ}
    (hf : StrictAnti f) (hg : StrictAnti g) {l : List α} {p : List γ} :
    (l.map f).ContainsPattern (p.map g) ↔ l.ContainsPattern p := by
  rw [containsPattern_iff, containsPattern_iff]
  constructor
  · rintro ⟨t, ht, htp⟩
    obtain ⟨s, hs, rfl⟩ := List.sublist_map_iff.mp ht
    exact ⟨s, hs, (sameOrderType_map_of_strictAnti_iff hf hg).mpr htp⟩
  · rintro ⟨s, hs, hsp⟩
    exact ⟨s.map f, hs.map f,
      (sameOrderType_map_of_strictAnti_iff hf hg).mp hsp⟩

/-- Reversing both words preserves pattern containment. -/
theorem containsPattern_reverse_iff [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {p : List β} :
    l.ContainsPattern p ↔ l.reverse.ContainsPattern p.reverse := by
  rw [containsPattern_iff, containsPattern_iff]
  constructor
  · rintro ⟨s, hs, hsp⟩
    exact ⟨s.reverse, List.reverse_sublist.mpr hs, sameOrderType_reverse hsp⟩
  · rintro ⟨s, hs, hsp⟩
    refine ⟨s.reverse, ?_, ?_⟩
    · simpa only [List.reverse_reverse] using List.reverse_sublist.mpr hs
    · simpa only [List.reverse_reverse] using sameOrderType_reverse hsp

/- Transport a sublist through an order-type equivalence. -/
private theorem sameOrderType_sublist_transport [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l : List α} {m : List β} {s : List β} (h : l.SameOrderType m) (hs : s <+ m) :
    ∃ t : List α, t <+ l ∧ t.SameOrderType s := by
  have hlen := sameOrderType_length h
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
  let e' : Fin s.length ↪o Fin l.length :=
    e.trans (Fin.castOrderIso hlen.symm).toOrderEmbedding
  let t : List α := List.ofFn (fun i => l.get (e' i))
  have htlen : t.length = s.length := by simp [t]
  let e'' : Fin t.length ↪o Fin l.length :=
    (Fin.castOrderIso htlen).toOrderEmbedding.trans e'
  have hrel : ∀ i j : Fin l.length,
      l.get i < l.get j ↔ m.get (Fin.cast hlen i) < m.get (Fin.cast hlen j) := by
    unfold SameOrderType sameOrderTypeBool at h
    simp only [dite_eq_left hlen] at h
    exact of_decide_eq_true h
  refine ⟨t, ?_, ?_⟩
  · apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨e'', ?_⟩
    intro i
    simp only [t, List.get_ofFn]
    rfl
  · unfold SameOrderType sameOrderTypeBool
    simp only [dite_eq_left htlen]
    apply decide_eq_true
    intro i j
    let hi : Fin s.length := Fin.cast htlen i
    let hj : Fin s.length := Fin.cast htlen j
    have hh := hrel (e' hi) (e' hj)
    have hti : t.get i = l.get (e' hi) := by
      change (List.ofFn (fun k => l.get (e' k))).get i = l.get (e' hi)
      rw [List.get_ofFn]
    have htj : t.get j = l.get (e' hj) := by
      change (List.ofFn (fun k => l.get (e' k))).get j = l.get (e' hj)
      rw [List.get_ofFn]
    rw [hti, htj]
    rw [hh]
    have hei : Fin.cast hlen (e' hi) = e hi := by
      simp [e', Fin.cast_cast]
    have hej : Fin.cast hlen (e' hj) = e hj := by
      simp [e', Fin.cast_cast]
    rw [hei, hej]
    rw [← he hi, ← he hj]

/-- Containment is transitive. -/
theorem containsPattern_trans [LT α] [LT β] [LT γ]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    [DecidableRel (· < · : γ → γ → Prop)] {l : List α} {m : List β} {p : List γ}
    (h₁ : l.ContainsPattern m) (h₂ : m.ContainsPattern p) : l.ContainsPattern p := by
  rw [containsPattern_iff] at h₁ h₂ ⊢
  rcases h₁ with ⟨s, hs, hsm⟩
  rcases h₂ with ⟨t, ht, htp⟩
  obtain ⟨u, hu, hut⟩ := sameOrderType_sublist_transport hsm ht
  exact ⟨u, hu.trans hs, sameOrderType_trans hut htp⟩


/-- Containment is monotone in the ambient word under sublists. -/
theorem containsPattern_of_sublist [LT α] [LT β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    {l₁ l₂ : List α} {p : List β} (hl : l₁ <+ l₂) (h : l₁.ContainsPattern p) :
    l₂.ContainsPattern p := by
  rw [containsPattern_iff] at h ⊢
  rcases h with ⟨s, hs, hp⟩
  exact ⟨s, hs.trans hl, hp⟩

end List

namespace Equiv.Perm

/-- Pattern containment for permutations is containment of their one-line words. -/
def ContainsPattern {n k : ℕ} (σ : Perm (Fin n)) (τ : Perm (Fin k)) : Prop :=
  (List.ofFn σ).ContainsPattern (List.ofFn τ)

instance {n k : ℕ} (σ : Perm (Fin n)) (τ : Perm (Fin k)) :
    Decidable (σ.ContainsPattern τ) := by
  unfold ContainsPattern
  infer_instance

/-- Pattern avoidance for permutations. -/
def Avoids {n k : ℕ} (σ : Perm (Fin n)) (τ : Perm (Fin k)) : Prop :=
  ¬σ.ContainsPattern τ

instance {n k : ℕ} (σ : Perm (Fin n)) (τ : Perm (Fin k)) : Decidable (σ.Avoids τ) := by
  unfold Avoids
  infer_instance

/-- Reverse the one-line word of a permutation. -/
def reverse {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin n) := Fin.revPerm.trans σ

/-- Complement the values in the one-line word of a permutation. -/
def complement {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin n) := σ.trans Fin.revPerm

private theorem ofFn_reverse {n : ℕ} (σ : Perm (Fin n)) :
    List.ofFn (reverse σ) = (List.ofFn σ).reverse := by
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

private theorem ofFn_complement {n : ℕ} (σ : Perm (Fin n)) :
    List.ofFn (complement σ) = (List.ofFn σ).map Fin.rev := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp [complement, Fin.revPerm_apply]

/-- Reversing both permutations preserves pattern containment. -/
theorem containsPattern_reverse_iff {n k : ℕ} (σ : Perm (Fin n))
    (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ (reverse σ).ContainsPattern (reverse τ) := by
  unfold ContainsPattern
  rw [ofFn_reverse, ofFn_reverse]
  exact List.containsPattern_reverse_iff

/-- Complementing both permutations preserves pattern containment. -/
theorem containsPattern_complement_iff {n k : ℕ} (σ : Perm (Fin n))
    (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ (complement σ).ContainsPattern (complement τ) := by
  unfold ContainsPattern
  rw [ofFn_complement, ofFn_complement]
  exact (List.containsPattern_map_of_strictAnti_iff
    Fin.rev_strictAnti Fin.rev_strictAnti).symm

/-- The finite set of permutations avoiding every pattern in a finite list. -/
def avoiders (n : ℕ) (ps : List (Σ k, Perm (Fin k))) : Finset (Perm (Fin n)) :=
  Finset.univ.filter fun σ => ps.all (fun p => decide (σ.Avoids p.2)) = true

/-- The list characterization of permutation pattern containment. -/
theorem containsPattern_iff {n k : ℕ} (σ : Perm (Fin n)) (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ ∃ s, List.Sublist s (List.ofFn σ) ∧
      s.SameOrderType (List.ofFn τ) := by
  exact List.containsPattern_iff

/-- Every permutation contains itself as a pattern. -/
theorem containsPattern_refl {n : ℕ} (σ : Perm (Fin n)) : σ.ContainsPattern σ := by
  exact List.containsPattern_refl (List.ofFn σ)

/-- Permutation pattern containment is transitive. -/
theorem containsPattern_trans {n k r : ℕ} (σ : Perm (Fin n))
    (τ : Perm (Fin k)) (υ : Perm (Fin r)) :
    σ.ContainsPattern τ → τ.ContainsPattern υ → σ.ContainsPattern υ := by
  exact List.containsPattern_trans

/-- Reversing a permutation twice gives the original permutation. -/
theorem reverse_reverse {n : ℕ} (σ : Perm (Fin n)) : reverse (reverse σ) = σ := by
  ext i
  simp [reverse, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]

/-- Complementing a permutation twice gives the original permutation. -/
theorem complement_complement {n : ℕ} (σ : Perm (Fin n)) :
    complement (complement σ) = σ := by
  ext i
  simp [complement, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]

end Equiv.Perm

namespace PatternRegression

private def p132 : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2

private def p2413 : Equiv.Perm (Fin 4) :=
  { toFun := ![1, 3, 0, 2]
    invFun := ![2, 0, 3, 1]
    left_inv := by decide
    right_inv := by decide }

private def p3142 : Equiv.Perm (Fin 4) :=
  { toFun := ![2, 0, 3, 1]
    invFun := ![1, 3, 0, 2]
    left_inv := by decide
    right_inv := by decide }

private def count132 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ => σ.Avoids p132).card

private def countSeparable (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ =>
    σ.Avoids p2413 ∧ σ.Avoids p3142).card

example : count132 1 = 1 ∧ count132 2 = 2 ∧ count132 3 = 5 := by
  decide

example : countSeparable 1 = 1 ∧ countSeparable 2 = 2 ∧ countSeparable 3 = 6 := by
  decide

example :
    ((List.range 4).permutations'.filter
      (fun w : List ℕ => w.Avoids [0, 2, 1])).length = 14 := by
  decide

example :
    ((List.range 4).permutations'.filter
      (fun w : List ℕ => w.Avoids [1, 3, 0, 2] ∧ w.Avoids [2, 0, 3, 1])).length = 22 := by
  decide

end PatternRegression
