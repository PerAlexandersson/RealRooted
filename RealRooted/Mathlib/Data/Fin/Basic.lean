module

public import Mathlib.Data.Fin.SuccPred

/-!
# Additional lemmas about finite indices

This file contains compatibility lemmas intended for upstreaming to
`Mathlib.Data.Fin.Basic`.
-/

public section

namespace Fin

/-- `succAbove` preserves three consecutive coordinates lying before the omitted index. -/
theorem succAbove_triple_eq_castSucc_of_right_lt
    {n : ℕ} (p : Fin (n + 3)) (i : Fin n)
    (h : i.succ.succ.castSucc < p) :
    p.succAbove i.castSucc.castSucc = i.castSucc.castSucc.castSucc ∧
      p.succAbove i.succ.castSucc = i.succ.castSucc.castSucc ∧
      p.succAbove i.succ.succ = i.succ.succ.castSucc := by
  change (i : ℕ) + 2 < (p : ℕ) at h
  have hleft : i.castSucc.castSucc.castSucc < p := by
    change (i : ℕ) < (p : ℕ)
    lia
  have hcenter : i.succ.castSucc.castSucc < p := by
    change (i : ℕ) + 1 < (p : ℕ)
    lia
  exact ⟨Fin.succAbove_of_castSucc_lt p _ hleft,
    Fin.succAbove_of_castSucc_lt p _ hcenter,
    Fin.succAbove_of_castSucc_lt p _ h⟩

/-- `succAbove` shifts three consecutive coordinates lying after the omitted index. -/
theorem succAbove_triple_eq_succ_of_le_left
    {n : ℕ} (p : Fin (n + 3)) (i : Fin n)
    (h : p ≤ i.castSucc.castSucc.castSucc) :
    p.succAbove i.castSucc.castSucc = i.castSucc.castSucc.succ ∧
      p.succAbove i.succ.castSucc = i.succ.castSucc.succ ∧
      p.succAbove i.succ.succ = i.succ.succ.succ := by
  change (p : ℕ) ≤ (i : ℕ) at h
  have hcenter : p ≤ i.succ.castSucc.castSucc := by
    change (p : ℕ) ≤ (i : ℕ) + 1
    lia
  have hright : p ≤ i.succ.succ.castSucc := by
    change (p : ℕ) ≤ (i : ℕ) + 2
    lia
  exact ⟨Fin.succAbove_of_le_castSucc p _ h,
    Fin.succAbove_of_le_castSucc p _ hcenter,
    Fin.succAbove_of_le_castSucc p _ hright⟩

/-- Omitting an interior center sends the corresponding new center to its old right
neighbor. -/
theorem succAbove_center_eq_right (i : Fin n) :
    (i.succ.castSucc.castSucc).succAbove i.succ.castSucc =
      i.succ.succ.castSucc := by
  rw [Fin.succAbove_of_le_castSucc _ _ le_rfl]
  congr

/-- Omitting the old right neighbor sends the corresponding new center to its old value. -/
theorem succAbove_center_eq_left (i : Fin n) :
    (i.succ.succ.castSucc).succAbove i.succ.castSucc =
      i.succ.castSucc.castSucc := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by
    change (i : ℕ) + 1 < (i : ℕ) + 2
    lia)]

/-- Deleting an interior full-vector coordinate agrees with deleting its
corresponding interior coordinate. -/
theorem succAbove_succ_castSucc
    {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :
    k.succ.castSucc.succAbove i.succ.castSucc =
      (k.succAbove i).succ.castSucc := by
  by_cases h : i.castSucc < k
  · have h' : i.succ.castSucc.castSucc < k.succ.castSucc := by
      change (i : ℕ) + 1 < (k : ℕ) + 1
      exact Nat.succ_lt_succ h
    rw [Fin.succAbove_of_castSucc_lt _ _ h',
      Fin.succAbove_of_castSucc_lt _ _ h]
    apply Fin.ext
    rfl
  · have hki : k ≤ i.castSucc := le_of_not_gt h
    have h' : k.succ.castSucc ≤ i.succ.castSucc.castSucc := by
      change (k : ℕ) + 1 ≤ (i : ℕ) + 1
      exact Nat.succ_le_succ hki
    rw [Fin.succAbove_of_le_castSucc _ _ h',
      Fin.succAbove_of_le_castSucc _ _ hki]
    apply Fin.ext
    rfl

end Fin
