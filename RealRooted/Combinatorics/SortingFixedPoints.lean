module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic

/-!
Aristotle project `c46dc43c-0f1b-436e-852d-810faecd9567`, adapted locally.

# Words, stable sorting ranks and fixed positions

For a word `u : Fin n → Fin N`, the stable sort orders the positions by the key
`(u w, w)` (lexicographically).  The rank of a position is its index in that order;
a position is *fixed* when its rank equals itself (i.e. it is a fixed point of the
sorting permutation).  We show that, for every set `J` of letters, the number of words of
length `n` in which every letter of `J` is carried by some fixed position is
`N ^ (n - |J|)` (or `0` when `|J| > n`), by removing/inserting one fixed position at a time.
-/

@[expose] public section

open Finset

namespace RealRooted.FiniteWords

variable {n N : ℕ}

/-- Sorting key of position `w` in a word `u`. -/
def key (u : Fin n → Fin N) (w : Fin n) : Lex (Fin N × Fin n) := toLex (u w, w)

/-- Rank of position `x` in the stable sort of `u`. -/
def rank (u : Fin n → Fin N) (x : Fin n) : ℕ := (univ.filter (fun w => key u w < key u x)).card

/-- Position `x` is a fixed point of the sorting permutation of `u`. -/
def IsFixed (u : Fin n → Fin N) (x : Fin n) : Prop := rank u x = x.val

instance (u : Fin n → Fin N) (x : Fin n) : Decidable (IsFixed u x) := by
  unfold IsFixed; infer_instance

/-- Letters carried by fixed positions. -/
def bad (u : Fin n → Fin N) : Finset (Fin N) := (univ.filter (fun x => IsFixed u x)).image u

theorem key_lt_iff (u : Fin n → Fin N) (a b : Fin n) :
    key u a < key u b ↔ u a < u b ∨ (u a = u b ∧ a < b) := by
  simp [key, Prod.Lex.toLex_lt_toLex]

theorem key_injective (u : Fin n → Fin N) : Function.Injective (key u) := by
  intro a b h
  simp only [key, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
  exact h.2

theorem rank_lt_of_key_lt (u : Fin n → Fin N) {a b : Fin n} (h : key u a < key u b) :
    rank u a < rank u b := by
  unfold rank
  apply card_lt_card
  refine ⟨fun w hw => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact lt_trans hw h
  · have : a ∈ univ.filter (fun w => key u w < key u a) := hsub (by simpa using h)
    simp at this

theorem rank_lt_rank_iff (u : Fin n → Fin N) (a b : Fin n) :
    rank u a < rank u b ↔ key u a < key u b := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h' | h'
    · exact absurd (rank_lt_of_key_lt u h') (not_lt.2 h.le)
    · rw [key_injective u h'] at h; exact lt_irrefl _ h
  · exact rank_lt_of_key_lt u

theorem rank_injective (u : Fin n → Fin N) : Function.Injective (rank u) := by
  intro a b h
  by_contra hne
  rcases lt_or_gt_of_ne ((key_injective u).ne hne) with h' | h'
  · exact absurd h (rank_lt_of_key_lt u h').ne
  · exact absurd h (rank_lt_of_key_lt u h').ne'

/-- Effect of deleting one position on the ranks of the other positions. -/
theorem rank_removeNth (u : Fin (n + 1) → Fin N) (p : Fin (n + 1)) (i : Fin n) :
    rank (Fin.removeNth p u) i + (if key u p < key u (p.succAbove i) then 1 else 0)
      = rank u (p.succAbove i) := by
  unfold rank
  rw [card_filter, card_filter, Fin.sum_univ_succAbove _ p, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : key (Fin.removeNth p u) j < key (Fin.removeNth p u) i
      ↔ key u (p.succAbove j) < key u (p.succAbove i) := by
    rw [key_lt_iff, key_lt_iff]
    simp only [Fin.removeNth, (Fin.strictMono_succAbove p).lt_iff_lt]
  simp only [this]

/-- Deleting a fixed position preserves exactly the other fixed positions. -/
theorem isFixed_removeNth (u : Fin (n + 1) → Fin N) (p : Fin (n + 1)) (hp : IsFixed u p)
    (i : Fin n) : IsFixed (Fin.removeNth p u) i ↔ IsFixed u (p.succAbove i) := by
  have h := rank_removeNth u p i
  have hiff : key u p < key u (p.succAbove i) ↔ p.val < rank u (p.succAbove i) := by
    rw [← rank_lt_rank_iff, hp]
  have hne : rank u (p.succAbove i) ≠ p.val := by
    intro hc
    rw [← hp] at hc
    exact Fin.succAbove_ne p i (rank_injective u hc)
  have hval : (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
    split_ifs with hip
    · rw [Fin.succAbove_of_castSucc_lt p i (by simpa [Fin.lt_def] using hip)]; simp
    · rw [Fin.succAbove_of_le_castSucc p i (by simp [Fin.le_def]; lia)]; simp
  unfold IsFixed
  rw [hval]
  by_cases hk : key u p < key u (p.succAbove i)
  · rw [ite_eq_left hk] at h
    have := hiff.1 hk
    split_ifs with hip <;> lia
  · rw [ite_eq_right hk] at h
    have := mt hiff.2 hk
    split_ifs with hip <;> lia

/-- Number of letters of `u'` smaller than `a`. -/
def cntLt (u' : Fin n → Fin N) (a : Fin N) : ℕ := (univ.filter (fun j => u' j < a)).card

/-- Number of occurrences of `a` in `u'` before position `y`. -/
def cntEq (u' : Fin n → Fin N) (a : Fin N) (y : ℕ) : ℕ :=
  (univ.filter (fun j : Fin n => j.val < y ∧ u' j = a)).card

/-- Rank of an occurrence of the inserted letter `a` at or before the insertion point. -/
theorem rank_insertNth_le (u' : Fin n → Fin N) (a : Fin N) (p x : Fin (n + 1)) (hx : x ≤ p)
    (hux : Fin.insertNth (α := fun _ => Fin N) p a u' x = a) :
    rank (Fin.insertNth (α := fun _ => Fin N) p a u') x = cntLt u' a + cntEq u' a x.val := by
  unfold rank cntLt cntEq
  rw [card_filter, Fin.sum_univ_succAbove _ p]
  simp only [key_lt_iff, hux, Fin.insertNth_apply_same, lt_irrefl, true_and, false_or,
    Fin.insertNth_apply_succAbove]
  rw [ite_eq_right (not_lt.2 hx), zero_add, ← card_filter, ← card_union_of_disjoint]
  · congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_union]
    have : p.succAbove j < x ↔ j.val < x.val := by
      by_cases hjp : j.castSucc < p
      · rw [Fin.succAbove_of_castSucc_lt p j hjp, Fin.lt_def]; simp
      · rw [Fin.succAbove_of_le_castSucc p j (not_lt.1 hjp), Fin.lt_def]
        rw [not_lt, Fin.le_def] at hjp
        rw [Fin.le_def] at hx
        simp only [Fin.val_castSucc, Fin.val_succ] at hjp ⊢
        lia
    rw [this]
    tauto
  · rw [disjoint_filter]
    rintro j _ h1 ⟨_, h2⟩
    rw [h2] at h1; exact lt_irrefl _ h1

theorem isFixed_insertNth_iff (u' : Fin n → Fin N) (a : Fin N) (p : Fin (n + 1)) :
    IsFixed (Fin.insertNth (α := fun _ => Fin N) p a u') p ↔
      cntLt u' a + cntEq u' a p.val = p.val := by
  rw [IsFixed, rank_insertNth_le u' a p p le_rfl (by simp)]

theorem cntEq_le (u' : Fin n → Fin N) (a : Fin N) (y : ℕ) : cntEq u' a y ≤ y := by
  unfold cntEq
  calc (univ.filter (fun j : Fin n => j.val < y ∧ u' j = a)).card
      ≤ (univ.filter (fun j : Fin n => j.val < y)).card :=
        card_le_card (fun j hj => by simp only [mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.1⟩)
    _ = min n y := Fin.card_filter_val_lt
    _ ≤ y := min_le_right _ _

theorem cntEq_mono (u' : Fin n → Fin N) (a : Fin N) {y z : ℕ} (h : y ≤ z) :
    cntEq u' a y ≤ cntEq u' a z :=
  card_le_card (fun j hj => by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact ⟨by lia, hj.2⟩)

theorem cntLt_add_cntEq_le (u' : Fin n → Fin N) (a : Fin N) : cntLt u' a + cntEq u' a n ≤ n := by
  unfold cntLt cntEq
  rw [← card_union_of_disjoint]
  · calc _ ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
      _ = n := by simp
  · rw [disjoint_filter]
    rintro j _ h1 ⟨_, h2⟩
    rw [h2] at h1; exact lt_irrefl _ h1

/-- There is always a position at which inserting `a` creates a fixed position. -/
theorem exists_insPos (u' : Fin n → Fin N) (a : Fin N) :
    ∃ p : Fin (n + 1), IsFixed (Fin.insertNth (α := fun _ => Fin N) p a u') p := by
  classical
  have hex : ∃ y, y ≤ n ∧ cntLt u' a ≤ y - cntEq u' a y :=
    ⟨n, le_rfl, by have := cntLt_add_cntEq_le u' a; lia⟩
  set y0 := Nat.find hex with hy0
  have hspec := Nat.find_spec hex
  rw [← hy0] at hspec
  have heq : cntLt u' a + cntEq u' a y0 = y0 := by
    rcases Nat.eq_zero_or_eq_succ_pred y0 with h0 | h0
    · rw [h0] at hspec ⊢
      have := cntEq_le u' a 0
      lia
    · have hmin := Nat.find_min hex (show y0 - 1 < y0 by lia)
      have h1 := cntEq_le u' a y0
      have h2 := cntEq_le u' a (y0 - 1)
      have h3 := cntEq_mono u' a (show y0 - 1 ≤ y0 by lia)
      have h4 : ¬ cntLt u' a ≤ y0 - 1 - cntEq u' a (y0 - 1) := fun h => hmin ⟨by lia, h⟩
      lia
  refine ⟨⟨y0, by lia⟩, ?_⟩
  rw [isFixed_insertNth_iff]
  exact heq

/-- If inserting `a` at `q < p` and at `p` both create fixed positions, the letter at `q`
is `a`. -/
theorem eq_of_two_insPos (u' : Fin n → Fin N) (a : Fin N) (q p : ℕ) (hqp : q < p) (hp : p ≤ n)
    (hq' : cntLt u' a + cntEq u' a q = q) (hp' : cntLt u' a + cntEq u' a p = p) :
    u' ⟨q, by lia⟩ = a := by
  by_contra hne
  have hsub : univ.filter (fun j : Fin n => j.val < p ∧ u' j = a) ⊆
      univ.filter (fun j : Fin n => j.val < q ∧ u' j = a) ∪
        univ.filter (fun j : Fin n => q < j.val ∧ j.val < p) := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
    rcases lt_trichotomy j.val q with h | h | h
    · exact Or.inl ⟨h, hj.2⟩
    · exfalso; apply hne
      have : j = ⟨q, by lia⟩ := Fin.ext h
      rw [← this]; exact hj.2
    · exact Or.inr ⟨h, hj.1⟩
  have hc := card_le_card hsub
  have hc2 := card_union_le (univ.filter (fun j : Fin n => j.val < q ∧ u' j = a))
    (univ.filter (fun j : Fin n => q < j.val ∧ j.val < p))
  have hc3 : (univ.filter (fun j : Fin n => q < j.val ∧ j.val < p)).card ≤ p - q - 1 := by
    calc _ ≤ (Finset.Ioo q p).card := by
          apply card_le_card_of_injOn (fun j => j.val)
          · intro j hj
            simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj
            simpa using hj
          · intro a _ b _ hab; exact Fin.ext hab
      _ = p - q - 1 := Nat.card_Ioo _ _
  unfold cntEq at hq' hp'
  lia

/-- The first fixed position carrying the letter `a`. -/
noncomputable def firstFix (u : Fin (n + 1) → Fin N) (a : Fin N) (h : a ∈ bad u) : Fin (n + 1) :=
  (univ.filter (fun x => IsFixed u x ∧ u x = a)).min' (by
    simp only [bad, mem_image, mem_filter, mem_univ, true_and] at h
    obtain ⟨x, hx, hxa⟩ := h
    exact ⟨x, by simp [hx, hxa]⟩)

theorem firstFix_spec (u : Fin (n + 1) → Fin N) (a : Fin N) (h : a ∈ bad u) :
    IsFixed u (firstFix u a h) ∧ u (firstFix u a h) = a ∧
      ∀ x, IsFixed u x → u x = a → firstFix u a h ≤ x := by
  have hmem := Finset.min'_mem (univ.filter (fun x => IsFixed u x ∧ u x = a)) (by
    simp only [bad, mem_image, mem_filter, mem_univ, true_and] at h
    obtain ⟨x, hx, hxa⟩ := h
    exact ⟨x, by simp [hx, hxa]⟩)
  simp only [mem_filter, mem_univ, true_and] at hmem
  refine ⟨hmem.1, hmem.2, fun x hx hxa => ?_⟩
  exact Finset.min'_le _ _ (by simp [hx, hxa])

/-- The first position at which inserting `a` creates a fixed position. -/
noncomputable def insPos (u' : Fin n → Fin N) (a : Fin N) : Fin (n + 1) :=
  (univ.filter (fun p => IsFixed (Fin.insertNth (α := fun _ => Fin N) p a u') p)).min' (by
    obtain ⟨p, hp⟩ := exists_insPos u' a
    exact ⟨p, by simp [hp]⟩)

theorem insPos_spec (u' : Fin n → Fin N) (a : Fin N) :
    IsFixed (Fin.insertNth (α := fun _ => Fin N) (insPos u' a) a u') (insPos u' a) ∧
      ∀ q, IsFixed (Fin.insertNth (α := fun _ => Fin N) q a u') q → insPos u' a ≤ q := by
  have hmem := Finset.min'_mem
    (univ.filter (fun p => IsFixed (Fin.insertNth (α := fun _ => Fin N) p a u') p)) (by
    obtain ⟨p, hp⟩ := exists_insPos u' a
    exact ⟨p, by simp [hp]⟩)
  simp only [mem_filter, mem_univ, true_and] at hmem
  exact ⟨hmem, fun q hq => Finset.min'_le _ _ (by simp [hq])⟩

theorem insPos_removeNth (u : Fin (n + 1) → Fin N) (a : Fin N) (h : a ∈ bad u) :
    insPos (Fin.removeNth (firstFix u a h) u) a = firstFix u a h := by
  obtain ⟨hpf, hpa, hpmin⟩ := firstFix_spec u a h
  set p := firstFix u a h
  set u' := Fin.removeNth p u
  have hu : Fin.insertNth (α := fun _ => Fin N) p a u' = u := by
    rw [← hpa]; exact Fin.insertNth_self_removeNth p u
  obtain ⟨hq, hqmin⟩ := insPos_spec u' a
  set q := insPos u' a
  apply le_antisymm (hqmin p (by rw [hu]; exact hpf))
  by_contra hlt
  rw [not_le] at hlt
  have hq' := (isFixed_insertNth_iff u' a q).1 hq
  have hp' := (isFixed_insertNth_iff u' a p).1 (by rw [hu]; exact hpf)
  have hqp : q.val < p.val := hlt
  have hval := eq_of_two_insPos u' a q.val p.val hqp (by lia) hq' hp'
  have huq : u q = a := by
    rw [← hu]
    have hj : p.succAbove (⟨q.val, by lia⟩ : Fin n) = q := by
      rw [Fin.succAbove_of_castSucc_lt]
      · exact Fin.ext (by simp)
      · rw [Fin.lt_def]; simpa using hqp
    rw [← hj, Fin.insertNth_apply_succAbove]
    exact hval
  have hfixq : IsFixed u q := by
    unfold IsFixed
    rw [← hu, rank_insertNth_le u' a p q hlt.le (by rw [hu]; exact huq)]
    exact hq'
  exact absurd (hpmin q hfixq huq) (not_le.2 hlt)

theorem firstFix_insertNth (u' : Fin n → Fin N) (a : Fin N)
    (h : a ∈ bad (Fin.insertNth (α := fun _ => Fin N) (insPos u' a) a u')) :
    firstFix (Fin.insertNth (α := fun _ => Fin N) (insPos u' a) a u') a h = insPos u' a := by
  obtain ⟨hp, hpmin⟩ := insPos_spec u' a
  obtain ⟨hxf, hxa, hxmin⟩ := firstFix_spec _ a h
  have hxp := hxmin (insPos u' a) hp (Fin.insertNth_apply_same _ _ _)
  apply le_antisymm hxp
  apply hpmin
  rw [isFixed_insertNth_iff]
  have := rank_insertNth_le u' a (insPos u' a) _ hxp hxa
  unfold IsFixed at hxf
  rw [this] at hxf
  exact hxf

theorem bad_removeNth (u : Fin (n + 1) → Fin N) (p : Fin (n + 1)) (hp : IsFixed u p) :
    (bad u).erase (u p) ⊆ bad (Fin.removeNth p u) := by
  intro b hb
  rw [mem_erase] at hb
  simp only [bad, mem_image, mem_filter, mem_univ, true_and] at hb ⊢
  obtain ⟨hbne, x, hx, rfl⟩ := hb
  have hxp : x ≠ p := fun h => hbne (h ▸ rfl)
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxp
  exact ⟨i, (isFixed_removeNth u p hp i).2 hx, rfl⟩

theorem bad_insertNth (u' : Fin n → Fin N) (a : Fin N) (p : Fin (n + 1))
    (hp : IsFixed (Fin.insertNth (α := fun _ => Fin N) p a u') p) :
    insert a (bad u') ⊆ bad (Fin.insertNth (α := fun _ => Fin N) p a u') := by
  intro b hb
  rw [mem_insert] at hb
  simp only [bad, mem_image, mem_filter, mem_univ, true_and] at hb ⊢
  rcases hb with rfl | ⟨i, hi, rfl⟩
  · exact ⟨p, hp, by simp⟩
  · refine ⟨p.succAbove i, ?_, by simp⟩
    have := isFixed_removeNth (Fin.insertNth (α := fun _ => Fin N) p a u') p hp i
    rw [Fin.removeNth_insertNth] at this
    exact this.1 hi

/-- Removing the first fixed position carrying `a` is a bijection. -/
theorem card_bad_succ (J : Finset (Fin N)) (a : Fin N) (ha : a ∈ J) :
    (univ.filter (fun u : Fin (n + 1) → Fin N => J ⊆ bad u)).card
      = (univ.filter (fun u' : Fin n → Fin N => J.erase a ⊆ bad u')).card := by
  refine Finset.card_bij'
    (fun u hu => Fin.removeNth (firstFix u a (by
      simp only [mem_filter, mem_univ, true_and] at hu; exact hu ha)) u)
    (fun u' _ => Fin.insertNth (α := fun _ => Fin N) (insPos u' a) a u') ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    obtain ⟨hpf, hpa, -⟩ := firstFix_spec u a (hu ha)
    refine subset_trans ?_ (bad_removeNth u _ hpf)
    rw [hpa]
    exact erase_subset_erase a hu
  · intro u' hu'
    simp only [mem_filter, mem_univ, true_and] at hu' ⊢
    refine subset_trans ?_ (bad_insertNth u' a _ (insPos_spec u' a).1)
    intro b hb
    by_cases hba : b = a
    · rw [hba]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (hu' (mem_erase.2 ⟨hba, hb⟩))
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    rw [insPos_removeNth u a (hu ha)]
    obtain ⟨-, hpa, -⟩ := firstFix_spec u a (hu ha)
    conv_rhs => rw [← Fin.insertNth_self_removeNth (firstFix u a (hu ha)) u]
    rw [hpa]
  · intro u' hu'
    rw [firstFix_insertNth u' a]
    exact Fin.removeNth_insertNth _ _ _

theorem card_bad_superset (J : Finset (Fin N)) :
    (univ.filter (fun u : Fin n → Fin N => J ⊆ bad u)).card
      = if J.card ≤ n then N ^ (n - J.card) else 0 := by
  induction n generalizing J with
  | zero =>
    have hb : ∀ u : Fin 0 → Fin N, bad u = ∅ := fun u => by simp [bad]
    simp only [hb, subset_empty, nonpos_iff_eq_zero, card_eq_zero]
    by_cases hJ : J = ∅
    · subst hJ; simp
    · simp [hJ]
  | succ n ih =>
    rcases J.eq_empty_or_nonempty with hJ | ⟨a, ha⟩
    · subst hJ; simp
    · rw [card_bad_succ J a ha, ih, card_erase_of_mem ha]
      have hpos : 0 < J.card := card_pos.2 ⟨a, ha⟩
      by_cases h : J.card ≤ n + 1
      · rw [ite_eq_left (by lia), ite_eq_left h]
        congr 1; lia
      · rw [ite_eq_right (by lia), ite_eq_right h]

end RealRooted.FiniteWords
