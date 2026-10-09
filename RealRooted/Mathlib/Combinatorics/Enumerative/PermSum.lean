import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith

namespace List

variable {α : Type*}

/-- The embedding of natural indices obtained by adding a fixed left offset. -/
def addLeftEmbedding (m : ℕ) : ℕ ↪ ℕ :=
  ⟨fun i => m + i, fun _ _ h => Nat.add_left_cancel h⟩

/-- The descent predicate at the junction of two words. -/
def junctionDescent [LT α] (l₁ l₂ : List α) : Prop :=
  ∃ a b, l₁.getLast? = some a ∧ l₂.head? = some b ∧ b < a

private theorem junctionDescent_iff [LinearOrder α] {l₁ l₂ : List α} :
    junctionDescent l₁ l₂ ↔
      ∃ h₁ : l₁ ≠ [], ∃ h₂ : l₂ ≠ [], l₂.head h₂ < l₁.getLast h₁ := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have h₁ : l₁ ≠ [] := by
      intro h
      simp [h] at ha
    have h₂ : l₂ ≠ [] := by
      intro h
      simp [h] at hb
    refine ⟨h₁, h₂, ?_⟩
    have ha' := Option.some.inj (ha.symm.trans (getLast?_eq_some_getLast h₁))
    have hb' := Option.some.inj (hb.symm.trans (head?_eq_some_head h₂))
    simpa only [ha', hb'] using hab
  · rintro ⟨h₁, h₂, hab⟩
    refine ⟨l₁.getLast h₁, l₂.head h₂, getLast?_eq_some_getLast h₁,
      head?_eq_some_head h₂, hab⟩

end List

namespace Equiv.Perm

private def sumFinEquiv (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  { toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
    invFun := Fin.addCases Sum.inl Sum.inr
    left_inv := by
      intro x
      cases x <;> simp
    right_inv := by
      intro i
      exact Fin.addCases (fun j => by simp) (fun j => by simp) i }

/-! Direct and skew sums use the zero-based one-line notation of permutations. -/

/-- The direct sum of permutations, with the second block shifted above the first. -/
def directSum {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) : Perm (Fin (m + n)) :=
  (sumFinEquiv m n).symm.trans ((Equiv.sumCongr σ τ).trans (sumFinEquiv m n))

/-- The skew sum of permutations, with the first block shifted above the second. -/
def skewSum {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) : Perm (Fin (m + n)) :=
  complement (directSum (complement σ) (complement τ))

private theorem rev_natAdd_rev {m n : ℕ} (j : Fin n) :
    Fin.rev (Fin.natAdd m j.rev) =
      Fin.cast (Nat.add_comm m n).symm (Fin.castAdd m j) := by
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_natAdd, Fin.val_cast, Fin.val_castAdd]
  have hj : j.val + 1 ≤ n := by lia
  have hs : n - (j.val + 1) + (j.val + 1) = n := Nat.sub_add_cancel hj
  have hb : m + (n - (j.val + 1)) + 1 ≤ m + n := by lia
  rw [Nat.sub_eq_iff_eq_add hb]
  lia

/-! ### Values and one-line words -/

/-- The left-block value of a direct sum. -/
@[simp] theorem directSum_apply_left {m n : ℕ} (σ : Perm (Fin m))
    (τ : Perm (Fin n)) (i : Fin m) :
    directSum σ τ (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  simp [directSum, sumFinEquiv]

/-- The right-block value of a direct sum. -/
@[simp] theorem directSum_apply_right {m n : ℕ} (σ : Perm (Fin m))
    (τ : Perm (Fin n)) (j : Fin n) :
    directSum σ τ (Fin.natAdd m j) = Fin.natAdd m (τ j) := by
  simp [directSum, sumFinEquiv]

/-- The left-block value of a skew sum. -/
@[simp] theorem skewSum_apply_left {m n : ℕ} (σ : Perm (Fin m))
    (τ : Perm (Fin n)) (i : Fin m) :
    skewSum σ τ (Fin.castAdd n i) =
      Fin.cast (Nat.add_comm m n).symm (Fin.natAdd n (σ i)) := by
  simp only [skewSum, complement, Equiv.trans_apply, directSum_apply_left,
    Fin.revPerm_apply]
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_rev]
  lia

/-- The right-block value of a skew sum. -/
@[simp] theorem skewSum_apply_right {m n : ℕ} (σ : Perm (Fin m))
    (τ : Perm (Fin n)) (j : Fin n) :
    skewSum σ τ (Fin.natAdd m j) =
      Fin.cast (Nat.add_comm m n).symm (Fin.castAdd m (τ j)) := by
  simp only [skewSum, complement, Equiv.trans_apply, directSum_apply_right,
    Fin.revPerm_apply]
  exact rev_natAdd_rev (τ j)

private theorem list_ofFn_sum {α : Type*} {m n : ℕ} (f : Fin (m + n) → α) :
    List.ofFn f = List.ofFn (fun i : Fin m => f (Fin.castAdd n i)) ++
      List.ofFn (fun j : Fin n => f (Fin.natAdd m j)) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.length_ofFn, List.length_append] at hi₁ hi₂ ⊢
    by_cases h : i < m
    · rw [List.getElem_append_left (by simpa using h)]
      simp only [List.getElem_ofFn]
      rfl
    · have hmn : m ≤ i := by lia
      rw [List.getElem_append_right (by simpa using hmn)]
      simp only [List.getElem_ofFn]
      apply congrArg f
      apply Fin.ext
      have hleft :
          (List.ofFn (fun i : Fin m => f (Fin.castAdd n i))).length = m := by
        simp
      simp only [hleft] at *
      simp only [Fin.val_natAdd]
      lia

/-- The one-line word of a direct sum is the concatenation of its blocks. -/
theorem directSum_toList {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    List.ofFn (directSum σ τ) =
      (List.ofFn σ).map (Fin.castAdd n) ++
        (List.ofFn τ).map (Fin.natAdd m) := by
  rw [list_ofFn_sum]
  simp only [directSum_apply_left, directSum_apply_right]
  simp only [List.ofFn_comp']

/-- The natural-valued one-line word of a direct sum is shifted by `m`. -/
theorem directSum_toNatList {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    (List.ofFn (directSum σ τ)).map Fin.val =
      (List.ofFn σ).map Fin.val ++ ((List.ofFn τ).map Fin.val).map (fun x => m + x) := by
  rw [directSum_toList]
  simp [Function.comp_def]

/-- The one-line word of a skew sum, with both blocks viewed in `Fin (m+n)`. -/
theorem skewSum_toList {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    List.ofFn (skewSum σ τ) =
      (List.ofFn σ).map (fun i => Fin.cast (Nat.add_comm m n).symm (Fin.natAdd n i)) ++
        (List.ofFn τ).map (Fin.cast (Nat.add_comm m n).symm ∘ Fin.castAdd m) := by
  rw [list_ofFn_sum]
  simp only [skewSum_apply_left, skewSum_apply_right, List.ofFn_comp']
  simp only [List.map_map]
  congr 1

/-- The natural-valued one-line word of a skew sum has the first block shifted by `n`. -/
theorem skewSum_toNatList {m n : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    (List.ofFn (skewSum σ τ)).map Fin.val =
      ((List.ofFn σ).map Fin.val).map (fun x => n + x) ++ (List.ofFn τ).map Fin.val := by
  rw [skewSum_toList]
  simp [Function.comp_def, Nat.add_comm]

/-! ### Small kernel checks -/

example :
    (directSum (Equiv.swap (0 : Fin 2) 1) (Equiv.refl (Fin 1))).descentCount = 1 := by
  decide

example :
    (skewSum (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1))).descentCount = 1 := by
  decide

end Equiv.Perm

namespace Equiv.Perm

/-- The pattern `2413` in zero-based one-line notation. -/
def pattern2413 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

/-- The pattern `3142` in zero-based one-line notation. -/
def pattern3142 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

end Equiv.Perm
