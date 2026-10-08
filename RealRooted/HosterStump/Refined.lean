import RealRooted.Basic.Coefficients

/-!
# Hoster--Stump refined polynomials

The refined family `p^{S ⊆ T}_{n,k}` of Section 3 of Hoster and Stump,
*Chow polynomials of simplicial posets* (arXiv:2508.15538), defined by their recursion
started at `n = 0`.  Descent positions are `0`-based: the paper's position `i` is `i - 1`
here, and the paper's shift `S - 1` is `shiftDown S`.

The recursion computes `∑ x ^ des w` over permutations `w` of `n + 1` letters with
`w 1 = k + 1`, isolated descent set `D` and `S ⊆ D ⊆ T`.  The definition has been checked
against exact diagram rows computed by an independent generator (which itself agrees with
brute-force permutation enumeration for all `S ⊆ T`, `n ≤ 5`): all entries of `D_2(range 1)`
and `D_2(range 2)`
(`Diagram.lean`, lemmas `e1_*`, `e2_*`) and of `D_3(range 2)` and `D_3(range 3)`
(regression `example`s below) are verified in Lean.
-/

open Polynomial

noncomputable section

namespace RealRooted.HosterStump

/-- `shiftDown S = {i | i + 1 ∈ S}`: delete the position `0` and lower all others by one. -/
def shiftDown (S : Finset ℕ) : Finset ℕ := (S.filter (· ≠ 0)).image (· - 1)

/-- Membership in `shiftDown S`. -/
@[simp]
lemma mem_shiftDown {S : Finset ℕ} {i : ℕ} : i ∈ shiftDown S ↔ i + 1 ∈ S := by
  unfold shiftDown
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hj' := Finset.mem_filter.mp hj
    have : j - 1 + 1 = j := by lia
    simp_all
  · intro h
    exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_filter.mpr ⟨h, by lia⟩, by lia⟩

/-- Erasing `0` does not change `shiftDown`. -/
@[simp]
lemma shiftDown_erase_zero (T : Finset ℕ) : shiftDown (T.erase 0) = shiftDown T := by
  ext i
  simp

/-- `shiftDown` of the singleton `{0}` is empty. -/
@[simp]
lemma shiftDown_singleton_zero : shiftDown {0} = ∅ := by
  ext i
  simp

/-- `shiftDown` of the empty set is empty. -/
@[simp]
lemma shiftDown_empty : shiftDown ∅ = ∅ := by
  ext i
  simp

/-- `shiftDown` of an initial segment. -/
@[simp]
lemma shiftDown_range (m : ℕ) : shiftDown (Finset.range (m + 1)) = Finset.range m := by
  ext i
  simp

/-- `shiftDown` commutes with erasing a positive position. -/
lemma shiftDown_erase_succ (S : Finset ℕ) (s : ℕ) :
    shiftDown (S.erase (s + 1)) = (shiftDown S).erase s := by
  ext i
  simp only [mem_shiftDown, Finset.mem_erase]
  grind

/-- The refined family `p^{S ⊆ T}_{n,k}` of Hoster--Stump, Section 3, by the recursion started
at `n = 0` (`0`-based descent positions; the paper's `S - 1` is `shiftDown S`). -/
noncomputable def refined : ℕ → ℕ → Finset ℕ → Finset ℕ → ℝ[X]
  | 0, k, S, _ => if k = 0 ∧ S = ∅ then 1 else 0
  | n + 1, k, S, T =>
      (if 0 ∈ T then
        X * ∑ j ∈ Finset.range k, refined n j (shiftDown S) ((shiftDown T).erase 0) else 0) +
      (if 0 ∈ S then 0 else
        ∑ j ∈ Finset.Ico k (n + 1), refined n j (shiftDown S) (shiftDown T))

/-- The base case `n = 0` of `refined`. -/
lemma refined_zero (k : ℕ) (S T : Finset ℕ) :
    refined 0 k S T = if k = 0 ∧ S = ∅ then 1 else 0 := by
  rw [refined]

/-- The two-summand unfolding of `refined` at level `n + 1`. -/
lemma refined_succ (n k : ℕ) (S T : Finset ℕ) :
    refined (n + 1) k S T =
      (if 0 ∈ T then
        X * ∑ j ∈ Finset.range k, refined n j (shiftDown S) ((shiftDown T).erase 0) else 0) +
      (if 0 ∈ S then 0 else
        ∑ j ∈ Finset.Ico k (n + 1), refined n j (shiftDown S) (shiftDown T)) := by
  rw [refined]

/-- Regression check (`n = 2`, paper `T = [1, 2]`): `p^{∅ ⊆ {0,1}}_{2,1} = 2 x`. -/
example : refined 2 1 ∅ {0, 1} = C 2 * X := by
  rw [map_ofNat C 2, two_mul]
  simp [refined, mem_shiftDown]

/-! ### Regression checks against the exact rows (`n = 3`)

All 24 entries of the diagrams `D_3(range 3)` and `D_3(range 2)` (the paper's `D_3([1, 3])`,
`D_3([1, 2])`; rows `top = refined _ _ ∅ (T.erase 0)`, `mid = refined _ _ ∅ T`,
`bot = refined _ _ {0} T`) agree with the exact generator. -/

example : refined 3 0 ∅ ((Finset.range 3).erase 0) = 1 + 4 * X := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 1 ∅ ((Finset.range 3).erase 0) = 3 * X := by
  simp [refined, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  ring

example : refined 3 2 ∅ ((Finset.range 3).erase 0) = X := by
  simp [refined]

example : refined 3 3 ∅ ((Finset.range 3).erase 0) = 0 := by
  simp [refined]

example : refined 3 0 ∅ (Finset.range 3) = 1 + 4 * X := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 1 ∅ (Finset.range 3) = 4 * X + X ^ 2 := by
  simp [refined, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  ring

example : refined 3 2 ∅ (Finset.range 3) = 2 * X + 2 * X ^ 2 := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 3 ∅ (Finset.range 3) = X + 2 * X ^ 2 := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 0 {0} (Finset.range 3) = 0 := by
  simp [refined]

example : refined 3 1 {0} (Finset.range 3) = X + X ^ 2 := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 2 {0} (Finset.range 3) = X + 2 * X ^ 2 := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 3 {0} (Finset.range 3) = X + 2 * X ^ 2 := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 0 ∅ ((Finset.range 2).erase 0) = 1 + 2 * X := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 1 ∅ ((Finset.range 2).erase 0) = 2 * X := by
  simp [refined, Finset.sum_Ico_eq_sum_range]

example : refined 3 2 ∅ ((Finset.range 2).erase 0) = X := by
  simp [refined]

example : refined 3 3 ∅ ((Finset.range 2).erase 0) = 0 := by
  simp [refined]

example : refined 3 0 ∅ (Finset.range 2) = 1 + 2 * X := by
  simp [refined, Finset.sum_range_succ]
  ring

example : refined 3 1 ∅ (Finset.range 2) = 3 * X := by
  simp [refined, Finset.sum_Ico_eq_sum_range]
  ring

example : refined 3 2 ∅ (Finset.range 2) = 2 * X := by
  simp [refined]
  ring

example : refined 3 3 ∅ (Finset.range 2) = X := by
  simp [refined]

example : refined 3 0 {0} (Finset.range 2) = 0 := by
  simp [refined]

example : refined 3 1 {0} (Finset.range 2) = X := by
  simp [refined]

example : refined 3 2 {0} (Finset.range 2) = X := by
  simp [refined]

example : refined 3 3 {0} (Finset.range 2) = X := by
  simp [refined]

/-! ### Nonnegativity and vanishing -/

/-- Every refined polynomial has nonnegative coefficients. -/
theorem hasNonnegCoeffs_refined (n k : ℕ) (S T : Finset ℕ) :
    HasNonnegCoeffs (refined n k S T) := by
  induction n generalizing k S T with
  | zero =>
    rw [refined_zero]
    split_ifs
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_zero
  | succ n ih =>
    rw [refined_succ]
    refine HasNonnegCoeffs.add ?_ ?_
    · split_ifs
      · exact HasNonnegCoeffs.mul hasNonnegCoeffs_X
          (hasNonnegCoeffs_finsetSum _ _ fun j _ => ih _ _ _)
      · exact hasNonnegCoeffs_zero
    · split_ifs
      · exact hasNonnegCoeffs_zero
      · exact hasNonnegCoeffs_finsetSum _ _ fun j _ => ih _ _ _

/-- If `S` is not contained in `T`, the refined polynomial vanishes. -/
theorem refined_eq_zero_of_not_subset {n : ℕ} (k : ℕ) {S T : Finset ℕ} (h : ¬S ⊆ T) :
    refined n k S T = 0 := by
  induction n generalizing k S T with
  | zero =>
    rw [refined_zero]
    have : S ≠ ∅ := by
      rintro rfl
      exact h (Finset.empty_subset _)
    simp [this]
  | succ n ih =>
    rw [refined_succ]
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp h
    by_cases h0 : 0 ∈ S
    · by_cases hT0 : 0 ∈ T
      · have hi0 : i ≠ 0 := by
          rintro rfl
          exact hiT hT0
        have hsub : ¬shiftDown S ⊆ (shiftDown T).erase 0 := by
          intro hsub
          have := hsub (mem_shiftDown.mpr (show (i - 1) + 1 ∈ S by
            rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0)]))
          have h2 := Finset.mem_erase.mp this
          have := mem_shiftDown.mp h2.2
          rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0)] at this
          exact hiT this
        simp [h0, hT0, ih _ hsub]
      · simp [h0, hT0]
    · have hi0 : i ≠ 0 := by
        rintro rfl
        exact h0 hiS
      have hi1 : (i - 1) + 1 = i := Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0)
      have hsub : ¬shiftDown S ⊆ shiftDown T := by
        intro hsub
        have := mem_shiftDown.mp (hsub (mem_shiftDown.mpr (by rwa [hi1])))
        rw [hi1] at this
        exact hiT this
      have hsub' : ¬shiftDown S ⊆ (shiftDown T).erase 0 := fun hs =>
        hsub (hs.trans (Finset.erase_subset _ _))
      simp [h0, ih _ hsub, ih _ hsub']

/-- Above the diagonal `n < k`, with `0 ∉ T`, the refined polynomial vanishes. -/
theorem refined_eq_zero_of_lt_of_not_mem {n k : ℕ} (S : Finset ℕ) {T : Finset ℕ} (hk : n < k)
    (hT : 0 ∉ T) : refined n k S T = 0 := by
  cases n with
  | zero =>
    rw [refined_zero]
    simp [show k ≠ 0 by lia]
  | succ n =>
    rw [refined_succ]
    simp [hT, Finset.Ico_eq_empty_of_le (show n + 1 ≤ k by lia)]

/-! ### The deletion identity -/

/-- Deletion identity: for `s ∈ S`,
`p^{S ∖ s ⊆ T}_{n,k} = p^{S ⊆ T}_{n,k} + p^{S ∖ s ⊆ T ∖ s}_{n,k}`. -/
theorem refined_erase {n k : ℕ} {S : Finset ℕ} (T : Finset ℕ) {s : ℕ} (hs : s ∈ S) :
    refined n k (S.erase s) T = refined n k S T + refined n k (S.erase s) (T.erase s) := by
  induction n generalizing k S T s with
  | zero =>
    have hS : S ≠ ∅ := Finset.ne_empty_of_mem hs
    simp [refined_zero, hS]
  | succ n ih =>
    rcases s with _ | s
    · have hS0 : (0 : ℕ) ∈ S := hs
      simp [refined_succ, hS0]
    · have hs' : s ∈ shiftDown S := mem_shiftDown.mpr hs
      have h1 : ∑ j ∈ Finset.range k,
            refined n j ((shiftDown S).erase s) ((shiftDown T).erase 0) =
          ∑ j ∈ Finset.range k, refined n j (shiftDown S) ((shiftDown T).erase 0) +
          ∑ j ∈ Finset.range k, refined n j ((shiftDown S).erase s)
            (((shiftDown T).erase 0).erase s) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => ih _ hs'
      have h2 : ∑ j ∈ Finset.Ico k (n + 1), refined n j ((shiftDown S).erase s) (shiftDown T) =
          ∑ j ∈ Finset.Ico k (n + 1), refined n j (shiftDown S) (shiftDown T) +
          ∑ j ∈ Finset.Ico k (n + 1), refined n j ((shiftDown S).erase s)
            ((shiftDown T).erase s) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => ih _ hs'
      have hSm : (0 ∈ S.erase (s + 1)) ↔ 0 ∈ S := by simp
      have hTm : (0 ∈ T.erase (s + 1)) ↔ 0 ∈ T := by simp
      have hc : ((shiftDown T).erase s).erase 0 = ((shiftDown T).erase 0).erase s :=
        Finset.erase_right_comm
      simp only [refined_succ, shiftDown_erase_succ, hSm, hTm, hc, h1, h2]
      by_cases hT0 : 0 ∈ T <;> by_cases hS0 : 0 ∈ S <;>
        simp only [hT0, hS0, ↓reduceIte, mul_add] <;> abel

/-! ### Constant coefficient and degree -/

/-- The constant coefficient of `refined n k S T`: it is `1` exactly when `k = 0` and
`S = ∅` (the identity permutation), and `0` otherwise. -/
theorem coeff_zero_refined (n k : ℕ) (S T : Finset ℕ) :
    (refined n k S T).coeff 0 = if k = 0 ∧ S = ∅ then 1 else 0 := by
  induction n generalizing k S T with
  | zero => rw [refined_zero]; split_ifs <;> simp
  | succ n ih =>
    rw [refined_succ, coeff_add]
    have hx : (if 0 ∈ T then
        X * ∑ j ∈ Finset.range k, refined n j (shiftDown S) ((shiftDown T).erase 0)
        else 0).coeff 0 = 0 := by
      split_ifs <;> simp
    rw [hx, zero_add]
    by_cases h0 : 0 ∈ S
    · have hS : S ≠ ∅ := Finset.ne_empty_of_mem h0
      simp [h0, hS]
    · have hS : shiftDown S = ∅ ↔ S = ∅ := by
        constructor
        · intro h
          ext i
          cases i with
          | zero => simpa using h0
          | succ i =>
            have : i ∉ shiftDown S := by simp [h]
            simpa using this
        · rintro rfl
          simp
      simp only [h0, ↓reduceIte, finsetSum_coeff]
      simp only [ih, hS]
      by_cases hSe : S = ∅
      · simp [hSe]
      · simp [hSe]

/-- The degree bound behind `natDegree_refined_le`, with the sharper bound when `0 ∉ T`. -/
private theorem natDegree_refined_le_aux (n : ℕ) :
    ∀ (m k : ℕ) (S T : Finset ℕ), T ⊆ Finset.range m →
      (refined n k S T).natDegree ≤ (m + 1) / 2 ∧
        (0 ∉ T → (refined n k S T).natDegree ≤ m / 2) := by
  induction n with
  | zero =>
    intro m k S T _
    rw [refined_zero]
    split_ifs <;> simp
  | succ n ih =>
    intro m k S T hT
    have hT' : shiftDown T ⊆ Finset.range (m - 1) := by
      intro i hi
      have := hT (mem_shiftDown.mp hi)
      simp only [Finset.mem_range] at this ⊢
      lia
    have hT'' : (shiftDown T).erase 0 ⊆ Finset.range (m - 1) :=
      (Finset.erase_subset _ _).trans hT'
    have hsecond : (if 0 ∈ S then (0 : ℝ[X]) else
        ∑ j ∈ Finset.Ico k (n + 1), refined n j (shiftDown S) (shiftDown T)).natDegree
          ≤ m / 2 := by
      split_ifs
      · simp
      · refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        have := (ih (m - 1) j (shiftDown S) (shiftDown T) hT').1
        lia
    have hfirst : 0 ∈ T → (if 0 ∈ T then X * ∑ j ∈ Finset.range k,
        refined n j (shiftDown S) ((shiftDown T).erase 0) else 0).natDegree ≤ (m + 1) / 2 := by
      intro h0T
      have hm : 0 < m := by
        have := hT h0T
        simpa using this
      simp only [h0T, ↓reduceIte]
      refine (natDegree_mul_le_of_le natDegree_X_le (m := 1) (n := (m - 1) / 2) ?_).trans
        (by lia)
      refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      exact (ih (m - 1) j (shiftDown S) _ hT'').2 (by simp)
    rw [refined_succ]
    constructor
    · refine natDegree_add_le_of_degree_le ?_ (hsecond.trans (by lia))
      by_cases h0T : 0 ∈ T
      · exact hfirst h0T
      · simp [h0T]
    · intro h0T
      refine natDegree_add_le_of_degree_le ?_ hsecond
      simp [h0T]

/-- Degree bound: if all positions of `T` are below `m`, the degree is at most `(m + 1) / 2`. -/
theorem natDegree_refined_le {m : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range m) (n k : ℕ)
    (S : Finset ℕ) : (refined n k S T).natDegree ≤ (m + 1) / 2 :=
  (natDegree_refined_le_aux n m k S T hT).1

end RealRooted.HosterStump
