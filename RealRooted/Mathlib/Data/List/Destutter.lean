module

public import Mathlib.Data.List.Destutter

/-!
# Additional lemmas about list destuttering

This file contains compatibility lemmas intended for upstreaming to
`Mathlib.Data.List.Destutter`.
-/

public section

namespace List

private theorem singleton_prefix_destutter'
    {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (a : α) (l : List α) :
    [a] <+: l.destutter' R a := by
  induction l generalizing a with
  | nil =>
      exact ⟨[], rfl⟩
  | cons b l ih =>
      rw [List.destutter'_cons]
      by_cases hab : R a b
      · rw [if_pos hab]
        exact ⟨l.destutter' R b, rfl⟩
      · rw [if_neg hab]
        exact ih a

private theorem destutter'_prefix_append
    {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (a : α) (l t : List α) :
    l.destutter' R a <+: (l ++ t).destutter' R a := by
  induction l generalizing a with
  | nil =>
      exact singleton_prefix_destutter' R a t
  | cons b l ih =>
      simp only [List.cons_append]
      rw [List.destutter'_cons, List.destutter'_cons]
      by_cases hab : R a b
      · rw [if_pos hab, if_pos hab]
        rcases ih b with ⟨u, hu⟩
        exact ⟨u, by simpa using congrArg (List.cons a) hu⟩
      · rw [if_neg hab, if_neg hab]
        exact ih a

private theorem destutter_prefix_append
    {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (l t : List α) :
    l.destutter R <+: (l ++ t).destutter R := by
  cases l with
  | nil =>
      exact ⟨t.destutter R, by simp⟩
  | cons a l =>
      exact destutter'_prefix_append R a l t

/-- Destuttering preserves list prefixhood. -/
theorem IsPrefix.destutter
    {α : Type*} {R : α → α → Prop} [DecidableRel R]
    {l₁ l₂ : List α} (h : l₁ <+: l₂) :
    l₁.destutter R <+: l₂.destutter R := by
  rcases h with ⟨t, rfl⟩
  exact destutter_prefix_append R l₁ t

private theorem getLast?_cons_eq_tail_of_ne_nil
    {α : Type*} {a : α} {l : List α} (hl : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  rw [List.getLast?_cons, List.getLast?_eq_some_getLast hl]
  simp

private theorem getLast?_destutter'_ne
    {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    (l.destutter' (· ≠ ·) a).getLast? =
      (a :: l).getLast? := by
  induction l generalizing a with
  | nil =>
      simp
  | cons b l ih =>
      rw [List.destutter'_cons]
      by_cases hab : a ≠ b
      · rw [if_pos hab]
        calc
          (a :: l.destutter' (· ≠ ·) b).getLast? =
              (l.destutter' (· ≠ ·) b).getLast? :=
            getLast?_cons_eq_tail_of_ne_nil (List.destutter'_ne_nil _ _)
          _ = (b :: l).getLast? := ih b
          _ = (a :: b :: l).getLast? :=
            (getLast?_cons_eq_tail_of_ne_nil (by simp)).symm
      · have hab_eq : a = b := not_ne_iff.mp hab
        subst b
        rw [if_neg (by simp)]
        calc
          (l.destutter' (· ≠ ·) a).getLast? =
              (a :: l).getLast? := ih a
          _ = (a :: a :: l).getLast? :=
            (getLast?_cons_eq_tail_of_ne_nil (by simp)).symm

/-- Destuttering by disequality preserves the final element. -/
theorem getLast?_destutter_ne
    {α : Type*} [DecidableEq α] (l : List α) :
    (l.destutter (· ≠ ·)).getLast? = l.getLast? := by
  cases l with
  | nil =>
      simp
  | cons a l =>
      exact getLast?_destutter'_ne a l

/-- Equal-length destuttered prefixes have the same final element. -/
theorem IsPrefix.getLast?_eq_of_destutter_length_le
    {α : Type*} [DecidableEq α]
    {l₁ l₂ : List α} (h : l₁ <+: l₂)
    (hlen :
      (l₂.destutter (· ≠ ·)).length ≤
        (l₁.destutter (· ≠ ·)).length) :
    l₁.getLast? = l₂.getLast? := by
  have heq :
      l₁.destutter (· ≠ ·) =
        l₂.destutter (· ≠ ·) :=
    (h.destutter (R := fun x y : α => x ≠ y)).eq_of_length_le hlen
  simpa only [List.getLast?_destutter_ne] using
    congrArg List.getLast? heq

private theorem destutter'_append_cons_self_ne
    {α : Type*} [DecidableEq α] (b a : α) (l₁ l₂ : List α) :
    (l₁ ++ a :: a :: l₂).destutter' (· ≠ ·) b =
      (l₁ ++ a :: l₂).destutter' (· ≠ ·) b := by
  induction l₁ generalizing b with
  | nil =>
      by_cases hba : b = a
      · subst b
        simp
      · simp [hba]
  | cons c l ih =>
      simp only [cons_append, List.destutter'_cons]
      by_cases hbc : b ≠ c
      · rw [if_pos hbc, if_pos hbc, ih c]
      · rw [if_neg hbc, if_neg hbc, ih b]

/-- Deleting one of two adjacent equal entries does not change disequality destuttering. -/
theorem destutter_append_cons_self_ne
    {α : Type*} [DecidableEq α] (l₁ l₂ : List α) (a : α) :
    (l₁ ++ a :: a :: l₂).destutter (· ≠ ·) =
      (l₁ ++ a :: l₂).destutter (· ≠ ·) := by
  cases l₁ with
  | nil =>
      simp [List.destutter_cons']
  | cons b l =>
      simp only [cons_append, List.destutter_cons']
      exact destutter'_append_cons_self_ne b a l l₂

/-- Deleting the second of two adjacent equal entries after a fixed entry does not change
disequality destuttering. -/
theorem destutter_append_cons_cons_self_ne
    {α : Type*} [DecidableEq α] (l₁ l₂ : List α) (a b : α) :
    (l₁ ++ a :: b :: b :: l₂).destutter (· ≠ ·) =
      (l₁ ++ a :: b :: l₂).destutter (· ≠ ·) := by
  simpa only [append_assoc, singleton_append] using
    destutter_append_cons_self_ne (l₁ ++ [a]) l₂ b

/-- Prepending an entry increases the length after disequality destuttering by at most one. -/
theorem length_destutter_cons_ne_le_succ
    {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    ((a :: l).destutter (· ≠ ·)).length ≤
      (l.destutter (· ≠ ·)).length + 1 := by
  cases l with
  | nil =>
      simp
  | cons b l =>
      simp only [List.destutter_cons', List.destutter'_cons]
      by_cases hab : a ≠ b
      · rw [if_pos hab]
        simp
      · have hab_eq : a = b := not_ne_iff.mp hab
        subst b
        rw [if_neg (by simp)]
        lia

end List
