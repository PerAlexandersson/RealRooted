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

end List
