/-
# Root-slot interval helper lemmas

Small order/list helper lemmas used by same-degree and succ-degree root-slot
combinatorics.
-/
import RealRooted.CommonInterleaverSeq

namespace RealRooted

lemma ici_inter_ici_nonempty (a b : ℝ) :
    (Set.Ici a ∩ Set.Ici b).Nonempty :=
  ⟨max a b, le_max_left a b, le_max_right a b⟩

lemma iic_inter_iic_nonempty (a b : ℝ) :
    (Set.Iic a ∩ Set.Iic b).Nonempty :=
  ⟨min a b, min_le_left a b, min_le_right a b⟩

lemma iic_inter_icc_nonempty_of_left
    {a b c : ℝ} (hba : b ≤ a) (hbc : b ≤ c) :
    (Set.Iic c ∩ Set.Icc b a).Nonempty :=
  ⟨b, hbc, le_rfl, hba⟩

lemma icc_inter_icc_nonempty_of_crossing
    {a a' b b' : ℝ} (haa' : a ≤ a') (hbb' : b ≤ b')
    (hab' : a ≤ b') (hba' : b ≤ a') :
    (Set.Icc a a' ∩ Set.Icc b b').Nonempty :=
  ⟨max a b,
    ⟨le_max_left a b, max_le haa' hba'⟩,
    ⟨le_max_right a b, max_le hab' hbb'⟩⟩

lemma list_getD_eq_getElem_of_lt
    {α : Type*} (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    xs.getD i d = xs.get ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (l := xs) (i := i) hi]
  simp

lemma getElem_le_getElem_of_getD_le
    {α : Type*} [Preorder α] {xs ys : List α} {i j : ℕ} {d : α}
    (h : xs.getD i d ≤ ys.getD j d) (hi : i < xs.length) (hj : j < ys.length) :
    xs.get ⟨i, hi⟩ ≤ ys.get ⟨j, hj⟩ := by
  rw [list_getD_eq_getElem_of_lt xs i d hi,
    list_getD_eq_getElem_of_lt ys j d hj] at h
  exact h

end RealRooted
