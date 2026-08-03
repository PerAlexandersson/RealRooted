module

public import Mathlib.Data.Fin.Basic

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
  have hleft : i.castSucc.castSucc.castSucc < p := by
    apply lt_of_le_of_lt _ h
    change (i : ℕ) ≤ (i : ℕ) + 2
    lia
  have hcenter : i.succ.castSucc.castSucc < p := by
    apply lt_of_le_of_lt _ h
    change (i : ℕ) + 1 ≤ (i : ℕ) + 2
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
  have hcenter : p ≤ i.succ.castSucc.castSucc := by
    apply le_trans h
    change (i : ℕ) ≤ (i : ℕ) + 1
    lia
  have hright : p ≤ i.succ.succ.castSucc := by
    apply le_trans h
    change (i : ℕ) ≤ (i : ℕ) + 2
    lia
  exact ⟨Fin.succAbove_of_le_castSucc p _ h,
    Fin.succAbove_of_le_castSucc p _ hcenter,
    Fin.succAbove_of_le_castSucc p _ hright⟩

end Fin
