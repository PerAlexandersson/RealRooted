module

public import Mathlib.Data.List.Zip
public import Mathlib.Order.Basic

/-!
# List zip lemmas

Small list lemmas that are candidates for upstreaming to Mathlib.
-/

public section

namespace List

/-- If a pair occurs in the zip of two lists, then its first coordinate occurs
in the first list. -/
theorem fst_mem_of_mem_zip {α β : Type*} {xs : List α} {ys : List β}
    {p : α × β} (hp : p ∈ xs.zip ys) : p.1 ∈ xs := by
  induction xs generalizing ys with
  | nil =>
      simp at hp
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hp
      | cons _ ys =>
          simp only [zip_cons_cons, mem_cons] at hp
          rcases hp with hp | hp
          · simp [hp]
          · exact List.mem_cons_of_mem x (ih hp)

/-- If a pair occurs in the zip of two lists, then its second coordinate occurs
in the second list. -/
theorem snd_mem_of_mem_zip {α β : Type*} {xs : List α} {ys : List β}
    {p : α × β} (hp : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil =>
      simp at hp
  | cons _ xs ih =>
      cases ys with
      | nil =>
          simp at hp
      | cons y ys =>
          simp only [zip_cons_cons, mem_cons] at hp
          rcases hp with hp | hp
          · simp [hp]
          · exact List.mem_cons_of_mem y (ih hp)

/-- A pair in `xs.zip xs.tail` consists of adjacent entries, so an `IsChain`
proof relates its two coordinates. -/
theorem rel_of_mem_zip_tail_of_isChain {α : Type*} {r : α → α → Prop}
    {xs : List α} (hxs : xs.IsChain r)
    {a b : α} (hab : (a, b) ∈ xs.zip xs.tail) :
    r a b := by
  induction xs with
  | nil =>
      simp at hab
  | cons _ xs ih =>
      cases xs with
      | nil =>
          simp at hab
      | cons _ ys =>
          simp only [tail_cons, zip_cons_cons, mem_cons] at hab
          rcases hab with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            exact List.IsChain.rel hxs
          · exact ih (List.IsChain.of_cons hxs) htail

/-- No member of a strictly increasing list lies strictly between two adjacent
entries of the list. -/
theorem not_mem_of_mem_zip_tail_of_pairwise_lt
    {α : Type*} [LinearOrder α] {xs : List α}
    (hxs : xs.Pairwise (· < ·))
    {left right z : α} (hab : (left, right) ∈ xs.zip xs.tail)
    (hleft : left < z) (hzright : z < right) :
    z ∉ xs := by
  induction xs with
  | nil =>
      simp at hab
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp at hab
      | cons y ys =>
          simp only [tail_cons, zip_cons_cons, mem_cons] at hab
          rcases hab with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            rw [pairwise_cons] at hxs
            intro hz
            rcases List.mem_cons.mp hz with hz_eq | hz_tail
            · rw [hz_eq] at hleft
              exact (lt_irrefl left hleft).elim
            · rcases List.mem_cons.mp hz_tail with hz_eq | hz_ys
              · rw [hz_eq] at hzright
                exact (lt_irrefl right hzright).elim
              · have hright_z : right < z := (pairwise_cons.mp hxs.2).1 z hz_ys
                exact (not_lt_of_ge (le_of_lt hzright)) hright_z
          · rw [pairwise_cons] at hxs
            intro hz
            rcases List.mem_cons.mp hz with hz_eq | hz_tail
            · have hleft_mem : left ∈ y :: ys :=
                fst_mem_of_mem_zip htail
              have hxleft : x < left := hxs.1 left hleft_mem
              have hbad : x < x := by
                exact lt_trans hxleft (by simpa [hz_eq] using hleft)
              exact (lt_irrefl x hbad).elim
            · exact ih hxs.2 htail hz_tail

end List
