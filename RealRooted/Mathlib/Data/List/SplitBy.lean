import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.Infix

/-!
# Adjacent elements of a `splitBy` block

This Mathlib-shaped shim records that a true adjacent relation remains inside
one block of `List.splitBy`.
-/

namespace List

private theorem mem_splitByLoop_of_mem_acc {α : Type*} (r : α → α → Bool)
    (l : List α) (a : α) (g : List α) (acc : List (List α))
    {q : List α} (hq : q ∈ acc) :
    q ∈ splitBy.loop r l a g acc := by
  induction l generalizing a g acc with
  | nil =>
      simp [splitBy.loop, hq]
  | cons b l ih =>
      simp only [splitBy.loop]
      split
      · exact ih _ _ _ hq
      · exact ih _ _ _ (by simp [hq])

private theorem exists_mem_splitByLoop_of_mem_current {α : Type*} (r : α → α → Bool)
    (l : List α) (a : α) (g : List α) (acc : List (List α))
    {x y : α} (hx : x ∈ a :: g) (hy : y ∈ a :: g) :
    ∃ q ∈ splitBy.loop r l a g acc, x ∈ q ∧ y ∈ q := by
  induction l generalizing a g acc with
  | nil =>
      refine ⟨(a :: g).reverse, ?_, ?_, ?_⟩
      · simp [splitBy.loop]
      · simpa [or_comm] using hx
      · simpa [or_comm] using hy
  | cons b l ih =>
      simp only [splitBy.loop]
      split
      · apply ih
        · simp [hx]
        · simp [hy]
      · refine ⟨(a :: g).reverse,
          mem_splitByLoop_of_mem_acc r l b [] ((a :: g).reverse :: acc) (by simp), ?_, ?_⟩
        · simpa [or_comm] using hx
        · simpa [or_comm] using hy

/-- If two adjacent entries are related, they belong to one `splitBy` block. -/
theorem exists_mem_splitBy_of_rel {α : Type*} (r : α → α → Bool)
    (a b : α) (l : List α) (h : r a b = true) :
    ∃ q ∈ (a :: b :: l).splitBy r, a ∈ q ∧ b ∈ q := by
  unfold splitBy
  dsimp
  change ∃ q ∈ (match r a b with
    | true => splitBy.loop r l b [a] []
    | false => splitBy.loop r l b [] [[a]]), a ∈ q ∧ b ∈ q
  rw [h]
  exact exists_mem_splitByLoop_of_mem_current r l b [a] [] (by simp) (by simp)

private theorem exists_infix_splitByLoop_of_infix_current {α : Type*} (r : α → α → Bool)
    (l : List α) (a : α) (g : List α) (acc : List (List α))
    {x y : α} (hxy : [x, y] <:+: (a :: g).reverse) :
    ∃ q ∈ splitBy.loop r l a g acc, [x, y] <:+: q := by
  induction l generalizing a g acc with
  | nil =>
      exact ⟨(a :: g).reverse, by simp [splitBy.loop], hxy⟩
  | cons b l ih =>
      simp only [splitBy.loop]
      split
      · apply ih
        rcases hxy with ⟨s, t, hst⟩
        refine ⟨s, t ++ [b], ?_⟩
        simpa [reverse_cons, append_assoc] using congrArg (fun u => u ++ [b]) hst
      · exact ⟨(a :: g).reverse,
          mem_splitByLoop_of_mem_acc r l b [] ((a :: g).reverse :: acc) (by simp), hxy⟩

/-- If two adjacent entries are related, they occur in that order in one
`splitBy` block. -/
theorem exists_infix_splitBy_of_rel {α : Type*} (r : α → α → Bool)
    (a b : α) (l : List α) (h : r a b = true) :
    ∃ q ∈ (a :: b :: l).splitBy r, [a, b] <:+: q := by
  unfold splitBy
  dsimp
  change ∃ q ∈ (match r a b with
    | true => splitBy.loop r l b [a] []
    | false => splitBy.loop r l b [] [[a]]), [a, b] <:+: q
  rw [h]
  exact exists_infix_splitByLoop_of_infix_current r l b [a] [] ⟨[], [], rfl⟩

private theorem exists_infix_splitByLoop_of_rel {α : Type*} (r : α → α → Bool)
    (pre suffix : List α) (a : α) (g : List α) (acc : List (List α))
    (x y : α) (hxy : r x y = true) :
    ∃ q ∈ splitBy.loop r (pre ++ x :: y :: suffix) a g acc, [x, y] <:+: q := by
  induction pre generalizing a g acc with
  | nil =>
      simp only [nil_append, splitBy.loop]
      split
      · simp only [hxy]
        apply exists_infix_splitByLoop_of_infix_current
        exact ⟨g.reverse ++ [a], [], by simp [reverse_cons, append_assoc]⟩
      · simp only [hxy]
        apply exists_infix_splitByLoop_of_infix_current
        exact ⟨[], [], rfl⟩
  | cons b pre ih =>
      simp only [cons_append, splitBy.loop]
      split
      · exact ih _ _ _
      · exact ih _ _ _

/-- If two adjacent entries are related inside a list, they occur in that
order in one `splitBy` block. -/
theorem exists_infix_splitBy_of_rel_of_append {α : Type*} (r : α → α → Bool)
    (pre suffix : List α) (a b : α) (h : r a b = true) :
    ∃ q ∈ (pre ++ a :: b :: suffix).splitBy r, [a, b] <:+: q := by
  cases pre with
  | nil => exact exists_infix_splitBy_of_rel r a b suffix h
  | cons c pre =>
      unfold splitBy
      dsimp
      apply exists_infix_splitByLoop_of_rel r pre suffix c [] [] a b h

/-- If two adjacent entries are related inside a list, they occur in that
order in one `splitBy` block. -/
theorem exists_infix_splitBy_of_rel_of_infix {α : Type*} (r : α → α → Bool)
    (l : List α) (a b : α) (hinfix : [a, b] <:+: l) (h : r a b = true) :
    ∃ q ∈ l.splitBy r, [a, b] <:+: q := by
  obtain ⟨pre, suffix, rfl⟩ := hinfix
  rw [append_assoc]
  exact exists_infix_splitBy_of_rel_of_append r pre suffix a b h

end List
