import RealRooted.HosterStump.Chow
import RealRooted.HosterStump.PosetBasic

/-!
# Hoster--Stump: permutations with descent set in a reflected set

Peeling the first letter with `Equiv.Perm.decomposeFin'` (`desSet_decomposeFin'Symm`) gives a
recursion for `desLeCount`; induction on `n` then yields the closed form
`desLeCount_reflectSet`, whose hockey-stick step is the binomial recursion of
`gapMultinomial`.  This is identity (F5) of Phase F: the permutations with `w 0 = k` and descent
set in `reflectSet n T` number `C(n - k, n - m - 1) * gapMultinomial (m + 1) (T \ {m})`,
`m = max T`; and only the identity has no descents (`desLeCount_empty`).
-/

open Finset

namespace RealRooted.HosterStump

private lemma subset_union_image_succ_iff (c : Prop) [Decidable c] (D E : Finset ℕ) :
    (if c then ({0} : Finset ℕ) else ∅) ∪ D.image Nat.succ ⊆ E ↔
      (c → 0 ∈ E) ∧ D ⊆ shiftDown E := by
  simp only [Finset.subset_iff, Finset.mem_union, Finset.mem_image, mem_shiftDown]
  split_ifs with h <;> grind

/-- Peeling off the first letter of a permutation. -/
private lemma desLeCount_succ_aux {n k : ℕ} (hk : k ≤ n + 1) (E : Finset ℕ) :
    desLeCount (n + 1) k E = ∑ j ∈ range (n + 1),
      if (j < k → 0 ∈ E) then desLeCount n j (shiftDown E) else 0 := by
  have hk' : k < n + 2 := by lia
  have h1 : ∀ j ∈ range (n + 1), desLeCount n j (shiftDown E) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        if (σ 0 : ℕ) = j ∧ desSet σ ⊆ shiftDown E then 1 else 0 := by
    intro j _
    unfold desLeCount
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl fun j hj => by rw [h1 j hj]]
  have h2 : ∀ j ∈ range (n + 1), (if (j < k → 0 ∈ E) then
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        if (σ 0 : ℕ) = j ∧ desSet σ ⊆ shiftDown E then 1 else 0
      else 0) = ∑ σ : Equiv.Perm (Fin (n + 1)),
      if (σ 0 : ℕ) = j ∧ (j < k → 0 ∈ E) ∧ desSet σ ⊆ shiftDown E then 1 else 0 := by
    intro j _
    by_cases h : j < k → 0 ∈ E
    · simp only [eq_true h, ↓reduceIte, true_and]
    · simp only [eq_false h, ↓reduceIte, false_and, and_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  have h3 : ∀ σ : Equiv.Perm (Fin (n + 1)), (∑ j ∈ range (n + 1),
      if (σ 0 : ℕ) = j ∧ (j < k → 0 ∈ E) ∧ desSet σ ⊆ shiftDown E then 1 else 0) =
      if ((σ 0 : ℕ) < k → 0 ∈ E) ∧ desSet σ ⊆ shiftDown E then 1 else 0 := by
    intro σ
    have : (σ 0 : ℕ) < n + 1 := (σ 0).2
    rw [Finset.sum_eq_single (σ 0 : ℕ)]
    · simp only [true_and]
    · intro b _ hb
      simp only [Ne.symm hb, false_and, ↓reduceIte]
    · intro h
      exact absurd (Finset.mem_range.mpr this) h
  rw [Finset.sum_congr rfl fun σ _ => h3 σ]
  unfold desLeCount
  rw [Finset.card_filter, ← Equiv.sum_comp Equiv.Perm.decomposeFin'.symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm]
  rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin (n + 2))]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [desSet_decomposeFin'Symm, Equiv.Perm.decomposeFin'Symm_zero,
      subset_union_image_succ_iff, true_and]
  · intro i _ hne
    refine Finset.sum_eq_zero fun σ _ => ?_
    refine ite_eq_right_iff.mpr ?_
    rw [Equiv.Perm.decomposeFin'Symm_zero]
    rintro ⟨h, -⟩
    exact absurd (Fin.ext h) hne
  · simp


private lemma shiftDown_reflectSet {n : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range (n + 1)) :
    shiftDown (reflectSet (n + 1) T) = reflectSet n (T.erase n) := by
  have hT' : T.erase n ⊆ Finset.range n := fun x hx => by
    have h1 := hT (Finset.mem_erase.mp hx).2
    have h2 := (Finset.mem_erase.mp hx).1
    simp only [Finset.mem_range] at h1 ⊢
    lia
  ext i
  rw [mem_shiftDown, mem_reflectSet hT, mem_reflectSet hT', Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by lia, by lia, by lia⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by lia, by lia⟩

private lemma zero_mem_reflectSet {n : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range (n + 1)) :
    0 ∈ reflectSet (n + 1) T ↔ n ∈ T := by
  rw [mem_reflectSet hT]
  simp only [Nat.add_one_sub_one, Nat.sub_zero, Nat.zero_lt_succ, true_and]

private lemma sum_range_choose_succ (N r : ℕ) :
    ∑ i ∈ Finset.range N, i.choose r = N.choose (r + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, add_comm]

private lemma sum_Ico_choose_sub (n r k : ℕ) :
    ∑ j ∈ Finset.Ico k (n + 1), (n - j).choose r = (n + 1 - k).choose (r + 1) := by
  rw [Finset.sum_Ico_eq_sum_range, ← sum_range_choose_succ]
  rw [← Finset.sum_range_reflect (fun i => i.choose r) (n + 1 - k)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  congr 1
  lia


private lemma gapMultinomial_empty (r : ℕ) : gapMultinomial r ∅ = 1 := by
  rw [gapMultinomial, dite_eq_right_iff.mpr fun h => absurd h Finset.not_nonempty_empty]

private lemma gapMultinomial_of_nonempty (r : ℕ) {U : Finset ℕ} (h : U.Nonempty) :
    gapMultinomial r U = Nat.choose r (U.max' h + 1) *
      gapMultinomial (U.max' h + 1) (U.erase (U.max' h)) := by
  rw [gapMultinomial]
  simp only [h, ↓reduceDIte]

private lemma desLeCount_succ_reflectSet_of_mem {n k : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Finset.range (n + 1)) (hk : k ≤ n + 1) (hn : n ∈ T) :
    desLeCount (n + 1) k (reflectSet (n + 1) T) =
      ∑ j ∈ Finset.range (n + 1), desLeCount n j (reflectSet n (T.erase n)) := by
  rw [desLeCount_succ_aux hk, shiftDown_reflectSet hT]
  have h0 : 0 ∈ reflectSet (n + 1) T := (zero_mem_reflectSet hT).mpr hn
  exact Finset.sum_congr rfl fun j _ => by simp only [h0, implies_true, ↓reduceIte]

private lemma desLeCount_succ_reflectSet_of_not_mem {n k : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Finset.range (n + 1)) (hk : k ≤ n + 1) (hn : n ∉ T) :
    desLeCount (n + 1) k (reflectSet (n + 1) T) =
      ∑ j ∈ Finset.Ico k (n + 1), desLeCount n j (reflectSet n (T.erase n)) := by
  rw [desLeCount_succ_aux hk, shiftDown_reflectSet hT]
  have h0 : 0 ∉ reflectSet (n + 1) T := fun h => hn ((zero_mem_reflectSet hT).mp h)
  have hI : Finset.Ico k (n + 1) = (Finset.range (n + 1)).filter fun j => ¬ j < k := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    lia
  rw [hI, Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by simp only [h0, imp_false]

private lemma desLeCount_reflectSet_aux (n : ℕ) : ∀ (k : ℕ) (T : Finset ℕ),
    T ⊆ Finset.range n → k ≤ n → desLeCount n k (reflectSet n T) =
      if h : T.Nonempty then Nat.choose (n - k) (n - T.max' h - 1) *
        gapMultinomial (T.max' h + 1) (T.erase (T.max' h))
      else if k = 0 then 1 else 0 := by
  induction n with
  | zero =>
    intro k T hT hk
    have hT0 : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    subst hT0
    have hk0 : k = 0 := by lia
    subst hk0
    simp only [reflectSet, Finset.image_empty, Finset.not_nonempty_empty, dite_false, ↓reduceIte]
    decide
  | succ n ih =>
    intro k T hT hk
    have hT' : T.erase n ⊆ Finset.range n := fun x hx => by
      have h1 := hT (Finset.mem_erase.mp hx).2
      have h2 := (Finset.mem_erase.mp hx).1
      simp only [Finset.mem_range] at h1 ⊢
      lia
    by_cases hn : n ∈ T
    · rw [desLeCount_succ_reflectSet_of_mem hT hk hn]
      have hne : T.Nonempty := ⟨n, hn⟩
      have hm : T.max' hne = n := le_antisymm
        (Finset.max'_le T hne n fun y hy => Nat.lt_succ_iff.mp (Finset.mem_range.mp (hT hy)))
        (Finset.le_max' _ _ hn)
      simp only [hne, ↓reduceDIte, hm]
      by_cases hne' : (T.erase n).Nonempty
      · have hlt : (T.erase n).max' hne' < n := by
          have h1 := Finset.mem_erase.mp (Finset.max'_mem _ hne')
          have h2 := Finset.mem_range.mp (hT h1.2)
          lia
        rw [gapMultinomial_of_nonempty _ hne']
        have hs : ∑ j ∈ Finset.range (n + 1), desLeCount n j (reflectSet n (T.erase n)) =
            ∑ j ∈ Finset.range (n + 1), (n - j).choose (n - (T.erase n).max' hne' - 1) *
              gapMultinomial ((T.erase n).max' hne' + 1)
                ((T.erase n).erase ((T.erase n).max' hne')) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [ih j (T.erase n) hT' (by have := Finset.mem_range.mp hj; lia)]
          simp only [hne', ↓reduceDIte]
        rw [hs, ← Finset.sum_mul, Finset.range_eq_Ico, sum_Ico_choose_sub, Nat.sub_zero,
          ← mul_assoc]
        have e1 : n + 1 - n - 1 = 0 := by lia
        have e2 : (n + 1).choose (n - (T.erase n).max' hne' - 1 + 1) =
            (n + 1).choose ((T.erase n).max' hne' + 1) := by
          rw [Nat.choose_symm_of_eq_add]
          lia
        rw [e1, e2, Nat.choose_zero_right, one_mul]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne', gapMultinomial_empty]
        have hs : ∑ j ∈ Finset.range (n + 1), desLeCount n j (reflectSet n ∅) =
            ∑ j ∈ Finset.range (n + 1), if j = 0 then 1 else 0 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [ih j ∅ (Finset.empty_subset _) (by have := Finset.mem_range.mp hj; lia)]
          simp only [Finset.not_nonempty_empty, ↓reduceDIte]
        have e1 : n + 1 - n - 1 = 0 := by lia
        rw [hs, Finset.sum_ite_eq', e1, Nat.choose_zero_right]
        simp only [Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte, mul_one]
    · rw [desLeCount_succ_reflectSet_of_not_mem hT hk hn, Finset.erase_eq_of_notMem hn]
      have hTn : T ⊆ Finset.range n := fun x hx => by
        have h1 := Finset.mem_range.mp (hT hx)
        have h2 : x ≠ n := fun h => hn (h ▸ hx)
        exact Finset.mem_range.mpr (by lia)
      by_cases hne : T.Nonempty
      · have hlt : T.max' hne < n := Finset.mem_range.mp (hTn (Finset.max'_mem _ hne))
        have hs : ∑ j ∈ Finset.Ico k (n + 1), desLeCount n j (reflectSet n T) =
            ∑ j ∈ Finset.Ico k (n + 1), (n - j).choose (n - T.max' hne - 1) *
              gapMultinomial (T.max' hne + 1) (T.erase (T.max' hne)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [ih j T hTn (by have := Finset.mem_Ico.mp hj; lia)]
          simp only [hne, ↓reduceDIte]
        rw [hs, ← Finset.sum_mul, sum_Ico_choose_sub]
        simp only [hne, ↓reduceDIte]
        have e1 : n - T.max' hne - 1 + 1 = n + 1 - T.max' hne - 1 := by lia
        rw [e1]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        have hs : ∑ j ∈ Finset.Ico k (n + 1), desLeCount n j (reflectSet n ∅) =
            ∑ j ∈ Finset.Ico k (n + 1), if j = 0 then 1 else 0 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [ih j ∅ (Finset.empty_subset _) (by have := Finset.mem_Ico.mp hj; lia)]
          simp only [Finset.not_nonempty_empty, ↓reduceDIte]
        rw [hs, Finset.sum_ite_eq']
        simp only [Finset.mem_Ico, Finset.not_nonempty_empty, ↓reduceDIte]
        by_cases hk0 : k = 0 <;> simp [hk0]


/-- Only the identity permutation has no descents. -/
theorem desLeCount_empty (n k : ℕ) : desLeCount n k ∅ = if k = 0 then 1 else 0 := by
  by_cases hk : k ≤ n
  · have := desLeCount_reflectSet_aux n k ∅ (Finset.empty_subset _) hk
    simpa only [reflectSet, Finset.image_empty, Finset.not_nonempty_empty, ↓reduceDIte]
      using this
  · have hk' : k ≠ 0 := by lia
    simp only [hk', ↓reduceIte]
    unfold desLeCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _ hw
    have := (w 0).2
    lia

/-- The number of permutations of `n + 1` letters with first letter `k` whose descent set lies
in the reflection of `T`: the first block, with minimum `k`, takes `n - m - 1` further values
among the `n - k` larger ones, and the remaining blocks are an ordered set partition counted by
`gapMultinomial`. -/
theorem desLeCount_reflectSet {n k : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range n)
    (hne : T.Nonempty) (hk : k ≤ n) :
    desLeCount n k (reflectSet n T) = Nat.choose (n - k) (n - T.max' hne - 1) *
      gapMultinomial (T.max' hne + 1) (T.erase (T.max' hne)) := by
  have := desLeCount_reflectSet_aux n k T hT hk
  simpa only [hne, ↓reduceDIte] using this

end RealRooted.HosterStump
