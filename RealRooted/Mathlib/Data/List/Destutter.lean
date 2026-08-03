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

private theorem getLast?_cons_of_ne_nil
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
            getLast?_cons_of_ne_nil (List.destutter'_ne_nil _ _)
          _ = (b :: l).getLast? := ih b
          _ = (a :: b :: l).getLast? :=
            (getLast?_cons_of_ne_nil (by simp)).symm
      · have hab_eq : a = b := not_ne_iff.mp hab
        subst b
        rw [if_neg (by simp)]
        calc
          (l.destutter' (· ≠ ·) a).getLast? =
              (a :: l).getLast? := ih a
          _ = (a :: a :: l).getLast? :=
            (getLast?_cons_of_ne_nil (by simp)).symm

/-- Destuttering by disequality preserves the final element. -/
theorem getLast?_destutter_ne
    {α : Type*} [DecidableEq α] (l : List α) :
    (l.destutter (· ≠ ·)).getLast? = l.getLast? := by
  cases l with
  | nil =>
      simp
  | cons a l =>
      exact getLast?_destutter'_ne a l

end List
