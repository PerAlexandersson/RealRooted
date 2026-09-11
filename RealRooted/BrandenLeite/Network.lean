import RealRooted.BrandenLeite.Resolvable

/-!
# Brändén--Saud Leite triangular networks

This file gives the literal finite path model used in Theorem 2.1 of
Brändén--Saud Leite. A path from `(n, 0)` to `(k, k)` is encoded by the finite
set of its `k` horizontal step times. It defines the associated weighted path
matrix, proves its lower-unitriangular and entrywise-nonnegative boundaries,
and proves the first-step recurrence for its resolving polynomials.

The Lindström--Gessel--Viennot total-nonnegativity theorem, the identification
with an arbitrary totally nonnegative matrix, and normalized weight uniqueness
are intentionally later steps.
-/

open BigOperators Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- The finite collection of paths from `(n, 0)` to `(k, k)`, encoded by
their horizontal step times. -/
def networkPaths (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter fun horizontalSteps =>
    horizontalSteps.card = k

/-- Number of horizontal steps strictly before a time. -/
def horizontalBefore {n : ℕ} (horizontalSteps : Finset (Fin n)) (t : Fin n) : ℕ :=
  (horizontalSteps.filter fun i => i < t).card

/-- Paths from `(n, k)` to `(j, j)`, encoded by horizontal step times. -/
def networkPathsFrom (n k j : ℕ) : Finset (Finset (Fin (n - k))) :=
  if k ≤ j ∧ j ≤ n then
    (Finset.univ : Finset (Fin (n - k))).powerset.filter fun horizontalSteps =>
      horizontalSteps.card = j - k
  else ∅

/-- Weight of the path encoded by a set of horizontal step times in the
triangular network. Horizontal edges have weight `1`; vertical edges have the
given array weight. -/
def networkPathWeight {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R)
    {n : ℕ} (horizontalSteps : Finset (Fin n)) : R :=
  ∏ t, if t ∈ horizontalSteps then 1 else
    weights (n - (t.val - horizontalBefore horizontalSteps t) - 1)
      (horizontalBefore horizontalSteps t)

/-- Weight of a path from `(n, k)` to a diagonal vertex. -/
def networkPathWeightFrom {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R)
    (n k : ℕ) {length : ℕ} (horizontalSteps : Finset (Fin length)) : R :=
  ∏ t, if t ∈ horizontalSteps then 1 else
    weights (n - (t.val - horizontalBefore horizontalSteps t) - 1)
      (k + horizontalBefore horizontalSteps t)

/-- Weighted path count from `(n, 0)` to `(k, k)`. -/
noncomputable def networkPathSum {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k : ℕ) : R := by
  classical
  exact ∑ horizontalSteps ∈ networkPaths n k, networkPathWeight weights horizontalSteps

/-- Weighted path count from `(n, k)` to `(j, j)`. -/
noncomputable def networkPathSumFrom {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k j : ℕ) : R :=
  ∑ horizontalSteps ∈ networkPathsFrom n k j,
    networkPathWeightFrom weights n k horizontalSteps

/-- The infinite matrix of weighted triangular-network path counts. -/
def networkMatrix {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R) :
    LowerTriangularMatrix R :=
  networkPathSum weights

/-- The resolving polynomial obtained from weighted paths starting at `(n, k)`. -/
def networkResolvingPolynomial (weights : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (networkPathSumFrom weights n k j) * X ^ j

private theorem networkPath_card_le {n k : ℕ} {horizontalSteps : Finset (Fin n)}
    (hpath : horizontalSteps ∈ networkPaths n k) : k ≤ n := by
  classical
  rw [← (Finset.mem_filter.mp hpath).2]
  simpa using Finset.card_le_univ horizontalSteps

private theorem networkPaths_self (n : ℕ) :
    networkPaths n n = {Finset.univ} := by
  ext horizontalSteps
  simp only [networkPaths, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_singleton]
  constructor
  · intro h
    apply (Finset.card_eq_iff_eq_univ _).mp
    simpa using h.2
  · rintro rfl
    simp

private theorem networkPathsFrom_self (n : ℕ) :
    networkPathsFrom n n n = {Finset.univ} := by
  ext horizontalSteps
  simp only [networkPathsFrom, le_refl, and_self, if_true, Finset.mem_filter,
    Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · intro h
    apply (Finset.card_eq_iff_eq_univ _).mp
    simpa using h.2
  · rintro rfl
    simp

/-- No path from `(n, 0)` can reach `(k, k)` when `k > n`. -/
theorem networkPathSum_eq_zero_of_lt {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k : ℕ} (h : n < k) :
    networkPathSum weights n k = 0 := by
  classical
  unfold networkPathSum
  apply Finset.sum_eq_zero
  intro horizontalSteps hpath
  exact (not_le_of_gt h (networkPath_card_le hpath)).elim

/-- A path count is zero when its target diagonal vertex lies left of its
starting column. -/
theorem networkPathSumFrom_eq_zero_of_lt_left {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k j : ℕ} (hjk : j < k) :
    networkPathSumFrom weights n k j = 0 := by
  unfold networkPathSumFrom networkPathsFrom
  rw [if_neg]
  · simp
  · exact fun h => (not_le_of_gt hjk h.1).elim

/-- A path count is zero when its target diagonal vertex lies beyond its row. -/
theorem networkPathSumFrom_eq_zero_of_lt_right {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k j : ℕ} (hnj : n < j) :
    networkPathSumFrom weights n k j = 0 := by
  unfold networkPathSumFrom networkPathsFrom
  rw [if_neg]
  · simp
  · exact fun h => (not_le_of_gt hnj h.2).elim

/-- Starting in column zero recovers the path counts defining `networkMatrix`. -/
theorem networkPathSumFrom_zero_eq {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n j : ℕ} (hj : j ≤ n) :
    networkPathSumFrom weights n 0 j = networkPathSum weights n j := by
  classical
  unfold networkPathSumFrom networkPathsFrom networkPathSum networkPaths
    networkPathWeightFrom networkPathWeight
  simp only [Nat.zero_le, true_and, if_pos hj, Nat.sub_zero, zero_add]

private theorem sum_powersetCard_succ_insert {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] {x : α} {s : Finset α} (hx : x ∉ s) (r : ℕ)
    (f : Finset α → M) :
    ∑ t ∈ (insert x s).powersetCard r.succ, f t =
      (∑ t ∈ s.powersetCard r.succ, f t) +
        ∑ t ∈ s.powersetCard r, f (insert x t) := by
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union]
  · rw [Finset.sum_image]
    intro u hu v hv huv
    have hxu : x ∉ u := fun hxu => hx ((Finset.mem_powersetCard.mp hu).1 hxu)
    have hxv : x ∉ v := fun hxv => hx ((Finset.mem_powersetCard.mp hv).1 hxv)
    simpa only [Finset.erase_insert hxu, Finset.erase_insert hxv] using
      congrArg (fun z : Finset α => z.erase x) huv
  · refine Finset.disjoint_left.mpr ?_
    intro t ht hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact hx ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _))

private theorem univ_succ_eq_insert_succ_map (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

private theorem filter_succ_map_lt {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    (s.map (Fin.succEmb n)).filter fun i => i < t.succ =
      (s.filter fun i => i < t).map (Fin.succEmb n) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨⟨a, ha, hai⟩, hlt⟩
    subst i
    exact ⟨a, ⟨ha, Fin.succ_lt_succ_iff.mp hlt⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hat⟩, hai⟩
    subst i
    exact ⟨⟨a, ha, rfl⟩, Fin.succ_lt_succ_iff.mpr hat⟩

private theorem horizontalBefore_succ_map {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    horizontalBefore (s.map (Fin.succEmb n)) t.succ = horizontalBefore s t := by
  unfold horizontalBefore
  rw [filter_succ_map_lt, Finset.card_map]

private theorem horizontalBefore_zero_insert_succ_map {n : ℕ} (s : Finset (Fin n))
    (t : Fin n) :
    horizontalBefore (insert 0 (s.map (Fin.succEmb n))) t.succ =
      horizontalBefore s t + 1 := by
  unfold horizontalBefore
  have hzero : (0 : Fin (n + 1)) ∉
      (s.map (Fin.succEmb n)).filter fun i => i < t.succ := by
    simp
  rw [Finset.filter_insert, if_pos (Fin.succ_pos _)]
  rw [Finset.card_insert_of_notMem hzero]
  apply congrArg (fun u : ℕ => u + 1)
  rw [filter_succ_map_lt, Finset.card_map]

private theorem horizontalBefore_le {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    horizontalBefore s t ≤ t.val := by
  unfold horizontalBefore
  rw [← Fin.card_Iio]
  apply Finset.card_le_card
  intro i hi
  simpa using (Finset.mem_filter.mp hi).2

private theorem networkPathWeightFrom_succ_map {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k : ℕ) {length : ℕ} (s : Finset (Fin length)) :
    networkPathWeightFrom weights (n + 1) k (s.map (Fin.succEmb length)) =
      weights n k * networkPathWeightFrom weights n k s := by
  unfold networkPathWeightFrom
  rw [Fin.prod_univ_succ]
  have hzero : (0 : Fin (length + 1)) ∉ s.map (Fin.succEmb length) := by
    simp only [Finset.mem_map]
    rintro ⟨t, ht, h⟩
    exact Fin.succ_ne_zero t h
  have hbefore_zero : horizontalBefore (s.map (Fin.succEmb length)) 0 = 0 := by
    unfold horizontalBefore
    simp
  rw [if_neg hzero, hbefore_zero]
  simp only [Fin.val_zero, Nat.zero_sub]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  have hmem : t.succ ∈ s.map (Fin.succEmb length) ↔ t ∈ s := by
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, h⟩
      exact (Fin.succEmb length).injective (by simpa using h) ▸ hu
    · intro ht
      exact ⟨t, ht, rfl⟩
  by_cases ht : t ∈ s
  · have hsucc : t.succ ∈ s.map (Fin.succEmb length) := hmem.mpr ht
    simp [ht, hsucc]
  · have hsucc : t.succ ∉ s.map (Fin.succEmb length) := fun h => ht (hmem.mp h)
    rw [if_neg hsucc, if_neg ht, horizontalBefore_succ_map]
    have hbefore : horizontalBefore s t ≤ t.val := horizontalBefore_le s t
    have hshift : t.succ.val - horizontalBefore s t =
        (t.val - horizontalBefore s t) + 1 := by
      rw [Fin.val_succ, Nat.succ_sub hbefore]
    rw [hshift, Nat.succ_sub_succ]

private theorem networkPathWeightFrom_zero_insert_succ_map {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k : ℕ) {length : ℕ} (s : Finset (Fin length)) :
    networkPathWeightFrom weights (n + 1) k (insert 0 (s.map (Fin.succEmb length))) =
      networkPathWeightFrom weights (n + 1) (k + 1) s := by
  unfold networkPathWeightFrom
  rw [Fin.prod_univ_succ]
  rw [if_pos (by simp), one_mul]
  apply Finset.prod_congr rfl
  intro t _
  have hmem : t.succ ∈ insert 0 (s.map (Fin.succEmb length)) ↔ t ∈ s := by
    simp only [Finset.mem_insert, Finset.mem_map]
    constructor
    · rintro (hzero | ⟨u, hu, h⟩)
      · exact (Fin.succ_ne_zero t hzero).elim
      · exact (Fin.succEmb length).injective (by simpa using h) ▸ hu
    · intro ht
      exact Or.inr ⟨t, ht, rfl⟩
  by_cases ht : t ∈ s
  · have hsucc : t.succ ∈ insert 0 (s.map (Fin.succEmb length)) := hmem.mpr ht
    simp [ht, hsucc]
  · have hsucc : t.succ ∉ insert 0 (s.map (Fin.succEmb length)) := fun h => ht (hmem.mp h)
    rw [if_neg hsucc, if_neg ht, horizontalBefore_zero_insert_succ_map]
    have hshift : t.succ.val - (horizontalBefore s t + 1) =
        t.val - horizontalBefore s t := by
      rw [Fin.val_succ, Nat.succ_sub_succ]
    rw [hshift]
    congr 1
    lia

private theorem sum_networkPathWeightFrom_succ {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k r : ℕ) {length : ℕ} :
    ∑ h ∈ (Finset.univ : Finset (Fin (length + 1))).powersetCard r.succ,
      networkPathWeightFrom weights (n + 1) k h =
      weights n k *
        (∑ s ∈ (Finset.univ : Finset (Fin length)).powersetCard r.succ,
          networkPathWeightFrom weights n k s) +
        ∑ s ∈ (Finset.univ : Finset (Fin length)).powersetCard r,
          networkPathWeightFrom weights (n + 1) (k + 1) s := by
  rw [univ_succ_eq_insert_succ_map, sum_powersetCard_succ_insert]
  · rw [Finset.powersetCard_map, Finset.sum_map]
    rw [Finset.powersetCard_map, Finset.sum_map, Finset.mul_sum]
    change
      (∑ x ∈ (Finset.univ : Finset (Fin length)).powersetCard r.succ,
          networkPathWeightFrom weights (n + 1) k (x.map (Fin.succEmb length))) +
        ∑ x ∈ (Finset.univ : Finset (Fin length)).powersetCard r,
          networkPathWeightFrom weights (n + 1) k (insert 0 (x.map (Fin.succEmb length))) = _
    simp_rw [networkPathWeightFrom_succ_map, networkPathWeightFrom_zero_insert_succ_map]
  · simp

private theorem networkPathsFrom_eq_powersetCard {n k j : ℕ} (hkj : k ≤ j)
    (hjn : j ≤ n) :
    networkPathsFrom n k j =
      (Finset.univ : Finset (Fin (n - k))).powersetCard (j - k) := by
  unfold networkPathsFrom
  rw [if_pos ⟨hkj, hjn⟩]
  ext s
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]

private theorem networkPathsFrom_eq_powersetCard_of_le_left {n k j : ℕ}
    (hkn : k ≤ n) (hkj : k ≤ j) :
    networkPathsFrom n k j =
      (Finset.univ : Finset (Fin (n - k))).powersetCard (j - k) := by
  by_cases hjn : j ≤ n
  · exact networkPathsFrom_eq_powersetCard hkj hjn
  · ext s
    rw [networkPathsFrom, if_neg (fun h => hjn h.2)]
    simp only [Finset.mem_powersetCard]
    constructor
    · simp
    · intro hs
      exfalso
      have hcard : s.card ≤ n - k := by
        calc
          s.card ≤ (Finset.univ : Finset (Fin (n - k))).card := Finset.card_le_card hs.1
          _ = n - k := Fintype.card_fin _
      rw [hs.2] at hcard
      lia

private theorem networkPathSumFrom_succ_target {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k : ℕ} (hkn : k ≤ n) (r : ℕ) :
    networkPathSumFrom weights (n + 1) k (k + r + 1) =
      weights n k * networkPathSumFrom weights n k (k + r + 1) +
        networkPathSumFrom weights (n + 1) (k + 1) (k + r + 1) := by
  unfold networkPathSumFrom
  rw [networkPathsFrom_eq_powersetCard_of_le_left (Nat.le_succ_of_le hkn) (by lia)]
  rw [networkPathsFrom_eq_powersetCard_of_le_left hkn (by lia)]
  rw [networkPathsFrom_eq_powersetCard_of_le_left (by lia) (by lia)]
  have hsub : k + (r + 1) - (k + 1) = r := by
    have hadd : k + (r + 1) = (k + 1) + r := by lia
    rw [hadd, Nat.add_sub_cancel_left]
  have hsub1 : k + r + 1 - k = r + 1 := by
    simpa only [Nat.add_assoc] using Nat.add_sub_cancel_left k (r + 1)
  have hsub2 : k + r + 1 - (k + 1) = r := by
    rw [Nat.add_assoc]
    exact hsub
  have hlen1 : n + 1 - k = n - k + 1 := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_sub hkn
  have hlen2' : n.succ - k.succ = n - k := Nat.succ_sub_succ n k
  convert sum_networkPathWeightFrom_succ weights n k r (length := n - k) using 1
  · rw [hsub1]
    simp only [Nat.succ_eq_add_one]
    rw [hlen1]
  · rw [hsub1, hsub2]
    simp only [Nat.succ_eq_add_one]
    rw [hlen2']

private theorem networkPathSumFrom_same_target {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k : ℕ} (hkn : k ≤ n) :
    networkPathSumFrom weights (n + 1) k k =
      weights n k * networkPathSumFrom weights n k k +
        networkPathSumFrom weights (n + 1) (k + 1) k := by
  have hzero := networkPathSumFrom_eq_zero_of_lt_left weights
    (n := n + 1) (k := k + 1) (j := k) (by lia)
  rw [hzero]
  unfold networkPathSumFrom
  rw [networkPathsFrom_eq_powersetCard_of_le_left (Nat.le_succ_of_le hkn) le_rfl]
  rw [networkPathsFrom_eq_powersetCard_of_le_left hkn le_rfl]
  simp only [Nat.succ_eq_add_one, tsub_self, Finset.powersetCard_zero,
    Finset.sum_singleton, add_zero]
  have hlen1 : n + 1 - k = n - k + 1 := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_sub hkn
  rw [hlen1]
  simpa using networkPathWeightFrom_succ_map weights n k (∅ : Finset (Fin (n - k)))

/-- A path count satisfies the first-step resolution recurrence. -/
theorem networkPathSumFrom_step {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k : ℕ} (hkn : k ≤ n) (j : ℕ) :
    networkPathSumFrom weights (n + 1) k j =
      weights n k * networkPathSumFrom weights n k j +
        networkPathSumFrom weights (n + 1) (k + 1) j := by
  by_cases hjk : j < k
  · rw [networkPathSumFrom_eq_zero_of_lt_left weights (n := n + 1) (k := k) hjk]
    rw [networkPathSumFrom_eq_zero_of_lt_left weights (n := n) (k := k) hjk]
    rw [networkPathSumFrom_eq_zero_of_lt_left weights (n := n + 1) (k := k + 1)
      (lt_of_lt_of_le hjk (Nat.le_succ _))]
    simp
  by_cases hj : j = k
  · subst j
    exact networkPathSumFrom_same_target weights hkn
  have hkj : k < j := lt_of_le_of_ne (Nat.le_of_not_gt hjk) (Ne.symm hj)
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hkj)
  subst j
  cases r with
  | zero => simp at hkj
  | succ r => simpa [Nat.add_assoc] using networkPathSumFrom_succ_target weights hkn r

private theorem coeff_networkResolvingPolynomial (weights : ℕ → ℕ → ℝ) (n k j : ℕ)
    (hj : j ≤ n) :
    (networkResolvingPolynomial weights n k).coeff j = networkPathSumFrom weights n k j := by
  unfold networkResolvingPolynomial
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · exact (hij h.symm).elim
    · rfl
  · simp [hj]

private theorem coeff_networkResolvingPolynomial_eq_zero (weights : ℕ → ℕ → ℝ)
    (n k j : ℕ) (hj : n < j) :
    (networkResolvingPolynomial weights n k).coeff j = 0 := by
  unfold networkResolvingPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact (not_le_of_gt hj (by simpa [h] using hin)).elim
  · rfl

/-- The literal path polynomials satisfy the Brändén--Saud Leite resolution
recurrence. -/
theorem networkResolvingPolynomial_step (weights : ℕ → ℕ → ℝ) {n k : ℕ}
    (hkn : k ≤ n) :
    networkResolvingPolynomial weights (n + 1) k =
      networkResolvingPolynomial weights (n + 1) (k + 1) +
        C (weights n k) * networkResolvingPolynomial weights n k := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  by_cases hj : j ≤ n
  · rw [coeff_networkResolvingPolynomial weights (n + 1) k j (Nat.le_succ_of_le hj)]
    rw [coeff_networkResolvingPolynomial weights (n + 1) (k + 1) j
      (Nat.le_succ_of_le hj)]
    rw [coeff_networkResolvingPolynomial weights n k j hj]
    simpa only [add_comm] using networkPathSumFrom_step weights hkn j
  by_cases hjs : j ≤ n + 1
  · have hj_eq : j = n + 1 := by lia
    subst j
    rw [coeff_networkResolvingPolynomial weights (n + 1) k (n + 1) le_rfl]
    rw [coeff_networkResolvingPolynomial weights (n + 1) (k + 1) (n + 1) le_rfl]
    rw [coeff_networkResolvingPolynomial_eq_zero weights n k (n + 1) (by lia)]
    rw [networkPathSumFrom_step weights hkn (n + 1)]
    rw [networkPathSumFrom_eq_zero_of_lt_right weights (n := n) (by lia)]
    simp
  · rw [coeff_networkResolvingPolynomial_eq_zero weights (n + 1) k j (by lia)]
    rw [coeff_networkResolvingPolynomial_eq_zero weights (n + 1) (k + 1) j (by lia)]
    rw [coeff_networkResolvingPolynomial_eq_zero weights n k j (by lia)]
    simp

/-- Every weighted triangular-network path matrix is lower triangular. -/
theorem isLowerTriangular_networkMatrix {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) :
    LowerTriangularMatrix.IsLowerTriangular (networkMatrix weights) := by
  intro n k hnk
  exact networkPathSum_eq_zero_of_lt weights hnk

/-- The unique path from `(n, 0)` to `(n, n)` uses only horizontal edges. -/
theorem networkPathSum_self {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n : ℕ) :
    networkPathSum weights n n = 1 := by
  classical
  unfold networkPathSum
  rw [networkPaths_self, Finset.sum_singleton]
  unfold networkPathWeight
  simp

/-- The only path from `(n, n)` to the diagonal is the empty path. -/
theorem networkPathSumFrom_self {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n : ℕ) :
    networkPathSumFrom weights n n n = 1 := by
  unfold networkPathSumFrom
  rw [networkPathsFrom_self, Finset.sum_singleton]
  unfold networkPathWeightFrom
  simp

/-- Over the reals, every weighted triangular-network path matrix is lower
unitriangular. -/
theorem isLowerUnitriangular_networkMatrix (weights : ℕ → ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerUnitriangular (networkMatrix weights) :=
  ⟨isLowerTriangular_networkMatrix weights, networkPathSum_self weights⟩

/-- The path polynomial in column zero is the row-generating polynomial of the
associated path matrix. -/
theorem networkResolvingPolynomial_zero (weights : ℕ → ℕ → ℝ) (n : ℕ) :
    networkResolvingPolynomial weights n 0 =
      LowerTriangularMatrix.rowPolynomial (networkMatrix weights) n := by
  unfold networkResolvingPolynomial LowerTriangularMatrix.rowPolynomial networkMatrix
  apply Finset.sum_congr rfl
  intro j hj
  rw [networkPathSumFrom_zero_eq weights (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

/-- The diagonal path polynomial is `X ^ n`. -/
theorem networkResolvingPolynomial_self (weights : ℕ → ℕ → ℝ) (n : ℕ) :
    networkResolvingPolynomial weights n n = X ^ n := by
  unfold networkResolvingPolynomial
  rw [Finset.sum_eq_single n]
  · rw [networkPathSumFrom_self]
    simp
  · intro j hj hjn
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [networkPathSumFrom_eq_zero_of_lt_left weights (lt_of_le_of_ne hjle hjn)]
    simp
  · simp

/-- Every path polynomial from `(n, k)` is divisible by `X ^ k`. -/
theorem X_pow_dvd_networkResolvingPolynomial (weights : ℕ → ℕ → ℝ)
    (n k : ℕ) :
    X ^ k ∣ networkResolvingPolynomial weights n k := by
  unfold networkResolvingPolynomial
  apply Finset.dvd_sum
  intro j hj
  by_cases hkj : k ≤ j
  · exact (pow_dvd_pow X hkj).mul_left _
  · rw [networkPathSumFrom_eq_zero_of_lt_left weights (Nat.lt_of_not_ge hkj)]
    simp

/-- Nonnegative edge weights give nonnegative weighted path counts. -/
theorem networkPathSum_nonneg {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R]
    (weights : ℕ → ℕ → R) (hweights : ∀ n k, 0 ≤ weights n k) (n k : ℕ) :
    0 ≤ networkPathSum weights n k := by
  classical
  unfold networkPathSum
  apply Finset.sum_nonneg
  intro horizontalSteps _
  unfold networkPathWeight
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact zero_le_one
  · exact hweights _ _

end

end RealRooted.BrandenLeite
