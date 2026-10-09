import RealRooted.Mathlib.Combinatorics.Enumerative.PermSum

noncomputable section

namespace List

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- The descent count after prepending two entries. -/
theorem descentCount_cons_cons (a b : α) (l : List α) :
    (a :: b :: l).descentCount = (if b < a then 1 else 0) + (b :: l).descentCount := by
  simp only [descentCount]
  rw [descentSet_cons_cons]
  have hdisj : _root_.Disjoint (if b < a then ({0} : Finset ℕ) else ∅)
      ((b :: l).descentSet.map ⟨Nat.succ, Nat.succ_injective⟩) := by
    split_ifs <;> simp [Finset.disjoint_left]
  calc
    _ = (if b < a then ({0} : Finset ℕ) else ∅).card +
        ((b :: l).descentSet.map ⟨Nat.succ, Nat.succ_injective⟩).card :=
      Finset.card_union_of_disjoint hdisj
    _ = _ := by rw [Finset.card_map]; split_ifs <;> simp

/-- The descent count of an append, with the possible junction descent exposed. -/
theorem descentCount_append_cons (l₁ : List α) (b : α) (l₂ : List α) :
    (l₁ ++ b :: l₂).descentCount = l₁.descentCount + (b :: l₂).descentCount +
      (if ∃ a, l₁.getLast? = some a ∧ b < a then 1 else 0) := by
  induction l₁ with
  | nil => simp [descentCount]
  | cons a l₁ ih =>
    cases l₁ with
    | nil =>
      simp only [List.singleton_append, descentCount_cons_cons, getLast?_singleton]
      by_cases h : b < a <;> simp [descentCount, h, Nat.add_comm]
    | cons c l₁ =>
      simp only [List.cons_append, descentCount_cons_cons]
      have ih' := ih
      rw [List.cons_append] at ih'
      rw [ih']
      have hlast : (a :: c :: l₁).getLast? = (c :: l₁).getLast? := by
        rw [getLast?_cons, getLast?_eq_some_getLast (by simp)]
        simp
      rw [hlast]
      simp [getLast?_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Strictly monotone relabelling preserves the descent count. -/
theorem descentCount_map_strictMono (l : List α) (f : α → β) (hf : StrictMono f) :
    (l.map f).descentCount = l.descentCount := by
  simp only [descentCount, descentSet_map_strictMono l f hf]

private theorem not_last_lt_of_forall_lt {l : List α} {b : α}
    (h : ∀ x ∈ l, x < b) : ¬∃ a, l.getLast? = some a ∧ b < a := by
  rintro ⟨a, ha, hba⟩
  obtain ⟨t, ht⟩ := getLast?_eq_some_iff.mp ha
  subst l
  have hlt := h a (by simp)
  exact (not_lt_of_ge (le_of_lt hlt)) hba

private theorem exists_last_lt_of_forall_gt {l : List α} {b : α} (hl : l ≠ [])
    (h : ∀ x ∈ l, b < x) : ∃ a, l.getLast? = some a ∧ b < a := by
  refine ⟨l.getLast hl, getLast?_eq_some_getLast hl, h _ (getLast_mem hl)⟩

end List

namespace Equiv.Perm

/-- The descent count of a direct sum is the sum of the two descent counts. -/
theorem descentCount_directSum {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (hn : 0 < n) :
    (directSum σ τ).descentCount = σ.descentCount + τ.descentCount := by
  have hτ : List.ofFn τ ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    lia
  obtain ⟨b, t, ht⟩ := List.exists_cons_of_ne_nil hτ
  rw [descentCount_eq_list, directSum_toList, ht, List.map_cons]
  rw [List.descentCount_append_cons]
  have hcast : StrictMono (Fin.castAdd n : Fin m → Fin (m + n)) := by
    intro x y hxy
    exact hxy
  have hshift : StrictMono (Fin.natAdd m : Fin n → Fin (m + n)) := by
    intro x y hxy
    change m + x.val < m + y.val
    exact Nat.add_lt_add_left hxy m
  change (List.map (Fin.castAdd n) (List.ofFn σ)).descentCount +
      ((b :: t).map (Fin.natAdd m)).descentCount + _ = _
  rw [List.descentCount_map_strictMono (List.ofFn σ) (Fin.castAdd n) hcast,
    List.descentCount_map_strictMono (b :: t) (Fin.natAdd m) hshift]
  have hcross : ∀ x ∈ (List.ofFn σ).map (Fin.castAdd n), Fin.natAdd m b > x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    apply Fin.mk_lt_mk.mpr
    lia
  have hnojunction := List.not_last_lt_of_forall_lt hcross
  have hτcount : (b :: t).descentCount = τ.descentCount := by
    rw [← ht]
    exact (descentCount_eq_list τ).symm
  simp only [hnojunction, ite_false, Nat.add_zero, hτcount]
  rw [descentCount_eq_list σ, descentCount_eq_list τ]

/-- The descent count of a skew sum is the sum of the two counts plus one. -/
theorem descentCount_skewSum {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (hm : 0 < m) (hn : 0 < n) :
    (skewSum σ τ).descentCount = σ.descentCount + τ.descentCount + 1 := by
  have hτ : List.ofFn τ ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    lia
  obtain ⟨b, t, ht⟩ := List.exists_cons_of_ne_nil hτ
  rw [descentCount_eq_list]
  have hvalSum : StrictMono (Fin.val : Fin (m + n) → ℕ) := Fin.val_strictMono
  rw [← List.descentCount_map_strictMono (List.ofFn (skewSum σ τ)) Fin.val hvalSum]
  rw [skewSum_toNatList, ht, List.map_cons]
  rw [List.descentCount_append_cons]
  have hval : StrictMono (Fin.val : Fin m → ℕ) := Fin.val_strictMono
  have hvalτ : StrictMono (Fin.val : Fin n → ℕ) := Fin.val_strictMono
  have hshift : StrictMono (fun x : ℕ => n + x) := by
    intro x y hxy
    lia
  change ((((List.ofFn σ).map Fin.val).map (fun x => n + x)).descentCount) +
      ((b :: t).map Fin.val).descentCount + _ = _
  rw [List.descentCount_map_strictMono ((List.ofFn σ).map Fin.val) (fun x => n + x)
      hshift, List.descentCount_map_strictMono (List.ofFn σ) Fin.val hval]
  have hσne : ((List.ofFn σ).map Fin.val).map (fun x => n + x) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_map, List.length_ofFn, List.length_nil] at hlen
    lia
  have hcross : ∀ x ∈ ((List.ofFn σ).map Fin.val).map (fun x => n + x), b.val < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    lia
  have hjunction := List.exists_last_lt_of_forall_gt hσne hcross
  have hτcount : (b :: t).descentCount = τ.descentCount := by
    rw [← ht]
    exact (descentCount_eq_list τ).symm
  have hτcount' : ((b :: t).map Fin.val).descentCount = τ.descentCount := by
    calc
      ((b :: t).map Fin.val).descentCount = (b :: t).descentCount :=
        List.descentCount_map_strictMono (b :: t) Fin.val hvalτ
      _ = τ.descentCount := hτcount
  simp only [hjunction, ite_true, hτcount']
  rw [descentCount_eq_list σ]

end Equiv.Perm
