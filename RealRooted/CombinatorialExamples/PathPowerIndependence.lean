import RealRooted.Graph.IndependencePolynomial.ClawFree

/-!
# Independence polynomials of powers of a path

The `r`-th power of the path on `0, 1, …, N - 1` joins two distinct vertices when they are at
distance at most `r`. An independent set of size `k` is a choice of `k` vertices with gaps
larger than `r`, so the independence polynomial is

```text
I_{N,r}(x) = Σ_k C(N + r - r k, k) x^k.
```

Powers of a path are claw-free, so these polynomials are real-rooted by the
Chudnovsky–Seymour theorem (`RealRooted.Graph.supportIndepPoly_splits_of_clawFree`). In
particular, with `m = N + r`, every polynomial `Σ_k C(m - r k, k) x^k` is real-rooted. The
case `r = 1` gives the Fibonacci polynomials `Σ_k C(m - k, k) x^k`, and the case `r = 2` gives
`Σ_k C(m - 2k, k) x^k`, which satisfies `g (m + 3) = g (m + 2) + x g m`.
-/

open Polynomial Finset RealRooted.Graph

namespace RealRooted

/-- The `r`-th power of the path on `ℕ`: distinct vertices are adjacent when their distance is
at most `r`. -/
def pathPowerGraph (r : ℕ) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j => i ≤ j + r ∧ j ≤ i + r

@[simp]
theorem pathPowerGraph_adj {r i j : ℕ} :
    (pathPowerGraph r).Adj i j ↔ i ≠ j ∧ i ≤ j + r ∧ j ≤ i + r := by
  simp only [pathPowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> exact ⟨h, by lia, by lia⟩
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, Or.inl ⟨h1, h2⟩⟩

instance (r : ℕ) : DecidableRel (pathPowerGraph r).Adj := fun i j =>
  decidable_of_iff (i ≠ j ∧ i ≤ j + r ∧ j ≤ i + r) pathPowerGraph_adj.symm

/-- Every power of a path is claw-free: three neighbours of one vertex lie in an interval of
length `2 r`, so two of them are at distance at most `r`. -/
theorem clawFree_pathPowerGraph (r : ℕ) : ClawFree (pathPowerGraph r) := by
  intro v s hadj hind
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hind.card_eq
  have ha := hadj a (by simp)
  have hb := hadj b (by simp)
  have hc := hadj c (by simp)
  have nab : ¬ (pathPowerGraph r).Adj a b := hind.isIndepSet (by simp) (by simp) hab
  have nac : ¬ (pathPowerGraph r).Adj a c := hind.isIndepSet (by simp) (by simp) hac
  have nbc : ¬ (pathPowerGraph r).Adj b c := hind.isIndepSet (by simp) (by simp) hbc
  simp only [pathPowerGraph_adj] at ha hb hc nab nac nbc
  lia

/-- Deleting the last vertex of the path power on `0, …, N` gives the vertex-deletion
recurrence `I_{N+1} = I_N + x I_{N-r}`. -/
theorem indepPolyOn_pathPowerGraph_range_succ (r N : ℕ) :
    indepPolyOn (pathPowerGraph r) (range (N + 1)) =
      indepPolyOn (pathPowerGraph r) (range N) +
        X * indepPolyOn (pathPowerGraph r) (range (N - r)) := by
  rw [indepPolyOn_erase (pathPowerGraph r) (v := N) (by simp)]
  congr 3
  · ext w
    simp only [mem_erase, mem_range]
    lia
  · ext w
    simp only [deleteClosedNeighborSupport, mem_filter, mem_erase, mem_range, pathPowerGraph_adj]
    lia

/-- The coefficients of the independence polynomial of the `r`-th power of the path on
`N` vertices: there are `C(N + r - r k, k)` independent sets of size `k`. -/
theorem coeff_indepPolyOn_pathPowerGraph_range (r N k : ℕ) :
    (indepPolyOn (pathPowerGraph r) (range N)).coeff k = ((N + r - r * k).choose k : ℝ) := by
  induction N using Nat.strong_induction_on generalizing k with
  | _ N ih =>
  rcases N with _ | N
  · rw [range_zero, indepPolyOn_empty]
    rcases k with _ | k
    · simp
    · have hr : r ≤ r * (k + 1) := Nat.le_mul_of_pos_right r (Nat.succ_pos k)
      rw [Nat.sub_eq_zero_of_le (by lia), Nat.choose_zero_succ, Nat.cast_zero, coeff_one]
      simp
  rw [indepPolyOn_pathPowerGraph_range_succ, coeff_add]
  rcases k with _ | k
  · simp [ih N (by lia)]
  rw [coeff_X_mul, ih N (by lia), ih (N - r) (by lia)]
  rcases k with _ | j
  · simp only [zero_add, mul_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one]
    rw [show N + 1 + r - r = N + 1 by lia, show N + r - r = N by lia]
    push_cast
    ring
  have hmul : r * (j + 1 + 1) = r * (j + 1) + r := by ring
  have hr : r ≤ r * (j + 1) := Nat.le_mul_of_pos_right r (Nat.succ_pos j)
  rw [hmul]
  by_cases hN : r * (j + 1) ≤ N
  · rw [show N + 1 + r - (r * (j + 1) + r) = N - r * (j + 1) + 1 by lia,
      show N + r - (r * (j + 1) + r) = N - r * (j + 1) by lia,
      show N - r + r - r * (j + 1) = N - r * (j + 1) by lia, Nat.choose_succ_succ']
    push_cast
    ring
  · rw [show N + 1 + r - (r * (j + 1) + r) = 0 by lia, show N + r - (r * (j + 1) + r) = 0 by lia,
      show N - r + r - r * (j + 1) = 0 by lia]
    simp

/-- The coefficient of `x ^ n` in `Σ_{k ≤ m} C(m - r k, k) x^k` is `C(m - r n, n)`. -/
private theorem coeff_sum_choose_sub_mul (r m n : ℕ) :
    (∑ k ∈ range (m + 1), C (((m - r * k).choose k : ℕ) : ℝ) * X ^ k).coeff n =
      ((m - r * n).choose n : ℝ) := by
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero]

/-- **Powers of a path.** For all `r` and `m`, the polynomial `Σ_k C(m - r k, k) x^k` is
real-rooted. For `r ≤ m` it is the independence polynomial of the `r`-th power of the path on
`m - r` vertices, which is claw-free; for `m < r` it is the constant `1`. -/
theorem splits_sum_choose_sub_mul (r m : ℕ) :
    (∑ k ∈ range (m + 1), C (((m - r * k).choose k : ℕ) : ℝ) * X ^ k).Splits := by
  by_cases hm : r ≤ m
  · obtain ⟨N, rfl⟩ : ∃ N, m = N + r := ⟨m - r, by lia⟩
    have heq : ∑ k ∈ range (N + r + 1), C (((N + r - r * k).choose k : ℕ) : ℝ) * X ^ k =
        indepPolyOn (pathPowerGraph r) (range N) := by
      ext n
      rw [coeff_sum_choose_sub_mul, coeff_indepPolyOn_pathPowerGraph_range]
    rw [heq]
    exact supportIndepPoly_splits_of_clawFree (clawFree_pathPowerGraph r) _
  · apply Splits.of_natDegree_eq_zero
    refine derivative_eq_zero.mp ?_
    ext n
    have hr : r ≤ r * (n + 1) := Nat.le_mul_of_pos_right r (Nat.succ_pos n)
    rw [coeff_derivative, coeff_sum_choose_sub_mul, coeff_zero,
      Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, zero_mul]

/-- **The square of a path.** Every polynomial `Σ_k C(m - 2k, k) x^k` is real-rooted. -/
theorem splits_sum_choose_sub_two_mul (m : ℕ) :
    (∑ k ∈ range (m + 1), C (((m - 2 * k).choose k : ℕ) : ℝ) * X ^ k).Splits :=
  splits_sum_choose_sub_mul 2 m

end RealRooted
