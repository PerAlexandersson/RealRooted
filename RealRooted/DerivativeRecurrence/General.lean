import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.IntervalCases
import RealRooted.DerivativeRecurrence.Degree

/-!
# Degrees of general linear recurrences

Rows of a linear recurrence of any order, with polynomial coefficients and derivatives,

`P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))`  (`jₜ < k`),

have degree `D₀ + d * n` and positive leading coefficients when every summand has degree
at most `D₀ + d * (n + k)`, the first `k` rows have positive coefficients at `D₀ + d * j`,
and the top-coefficient multipliers, grouped by the lag `jₜ`, are nonnegative with a
positive sum.  The summands `(jₜ, iₜ, Aₜ)` form a list, so that a concrete recurrence
read off a definition is an instance by `simp`.

Further sections: positivity of solutions of scalar recurrences (`RealRooted.ScalarRec`,
nonnegative multipliers or a growth-ratio invariant), the same degree theorems for an
arbitrary degree law `D : ℕ → ℕ` (`*_of_degreeLaw`, covering periodic growth such as
`D n = D₀ + d * ((n + e) / p)`), and top coefficients controlled by a ratio invariant
(`natDegree_eq_and_leadingCoeff_pos_of_ratio`).

This generalizes `RealRooted.derivRec_leadingCoeff_pos` (first order),
`RealRooted.derivRec₂_leadingCoeff_pos` (second order) and
`RealRooted.threeTermPos_leadingCoeff_pos` (three-term) to any order and any mixture of
derivatives.
-/

open Polynomial

namespace RealRooted.LinRec

/-- The right side `∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` of a linear recurrence with summands
`t = (jₜ, iₜ, Aₜ)`. -/
noncomputable def rhs (terms : List (ℕ × ℕ × (ℕ → ℝ[X]))) (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  (terms.map fun t => t.2.2 n * derivative^[t.2.1] (P (n + t.1))).sum

/-- The top-coefficient multiplier of the summand `t = (j, i, A)` at step `n`: the
coefficient of `A n` at `d * (k - j) + i`, times the falling factorial
`N (N - 1) ⋯ (N - i + 1)` of the degree `N = D₀ + d * (n + j)` of the row it
differentiates. -/
noncomputable def topCoeff (k d D₀ n : ℕ) (t : ℕ × ℕ × (ℕ → ℝ[X])) : ℝ :=
  (t.2.2 n).coeff (d * (k - t.1) + t.2.1) *
    ∏ l ∈ Finset.range t.2.1, (((D₀ + d * (n + t.1) : ℕ) : ℝ) - l)

/-- The top-coefficient multiplier of the lag `j`: the sum of `topCoeff` over the
summands that act on the row `P (n + j)`. -/
noncomputable def lagMult (k d D₀ : ℕ) (terms : List (ℕ × ℕ × (ℕ → ℝ[X]))) (n j : ℕ) : ℝ :=
  ((terms.filter fun t => t.1 = j).map (topCoeff k d D₀ n)).sum

private theorem descFactorial_cast (N i : ℕ) :
    (N.descFactorial i : ℝ) = ∏ l ∈ Finset.range i, ((N : ℝ) - l) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Nat.descFactorial_succ, Finset.prod_range_succ, ← ih, Nat.cast_mul]
      rcases le_or_gt i N with h | h
      · rw [Nat.cast_sub h]
        ring
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
        simp

/-- One step: if the rows `P (n + j)`, `j < k`, have degree at most `D₀ + d * (n + j)`,
then so does the right side at `D₀ + d * (n + k)`, with top coefficient
`∑ₜ topCoeff t * (P (n + jₜ)).coeff (D₀ + d * (n + jₜ))`. -/
theorem rhs_step {k d D₀ : ℕ} {P : ℕ → ℝ[X]} (n : ℕ) :
    ∀ terms : List (ℕ × ℕ × (ℕ → ℝ[X])), (∀ t ∈ terms, t.1 < k) →
      (∀ t ∈ terms, (t.2.2 n).natDegree ≤ d * (k - t.1) + t.2.1) →
      (∀ j < k, (P (n + j)).natDegree ≤ D₀ + d * (n + j)) →
      (rhs terms P n).natDegree ≤ D₀ + d * (n + k) ∧
        (rhs terms P n).coeff (D₀ + d * (n + k)) =
          (terms.map fun t => topCoeff k d D₀ n t * (P (n + t.1)).coeff (D₀ + d * (n + t.1))).sum
  | [], _, _, _ => by simp [rhs]
  | t :: ts, hlag, hA, hP => by
      have hj := hlag t (by simp)
      have hN : D₀ + d * (n + t.1) + d * (k - t.1) = D₀ + d * (n + k) := by
        rw [add_assoc, ← mul_add, show n + t.1 + (k - t.1) = n + k by lia]
      have ih := rhs_step n ts (fun s hs => hlag s (by simp [hs]))
        (fun s hs => hA s (by simp [hs])) hP
      have h1 := natDegree_mul_iterate_derivative_le (d := d * (k - t.1)) (j := t.2.1)
        (hA t (by simp)) (hP t.1 hj)
      have h2 := coeff_mul_iterate_derivative_of_natDegree_le (d := d * (k - t.1)) (j := t.2.1)
        (hA t (by simp)) (hP t.1 hj)
      rw [hN] at h1 h2
      simp only [rhs, List.map_cons, List.sum_cons] at ih ⊢
      refine ⟨natDegree_add_le_of_degree_le h1 ih.1, ?_⟩
      rw [coeff_add, h2, ih.2, topCoeff, descFactorial_cast]

/-- Regroup a sum over the summands by their lags `j < k`. -/
private theorem sum_map_eq_sum_lag {k : ℕ} (f : ℕ × ℕ × (ℕ → ℝ[X]) → ℝ) (g : ℕ → ℝ) :
    ∀ terms : List (ℕ × ℕ × (ℕ → ℝ[X])), (∀ t ∈ terms, t.1 < k) →
      (terms.map fun t => f t * g t.1).sum =
        ∑ j ∈ Finset.range k, ((terms.filter fun t => t.1 = j).map f).sum * g j
  | [], _ => by simp
  | t :: ts, hlag => by
      rw [List.map_cons, List.sum_cons,
        sum_map_eq_sum_lag f g ts (fun s hs => hlag s (by simp [hs]))]
      have hj : t.1 ∈ Finset.range k := Finset.mem_range.mpr (hlag t (by simp))
      simp only [List.filter_cons, decide_eq_true_eq]
      rw [← Finset.add_sum_erase _ _ hj, ← Finset.add_sum_erase _ _ hj, ← add_assoc]
      congr 1
      · simp [add_mul]
      · refine Finset.sum_congr rfl fun j hj' => ?_
        simp [Ne.symm (Finset.ne_of_mem_erase hj')]

/-- Rows of `P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` have degree `D₀ + d * n` and
positive leading coefficients, when the summands have degree at most
`D₀ + d * (n + k)`, the first `k` rows have positive coefficients at `D₀ + d * j`, and
the lag multipliers `lagMult` are nonnegative with a positive sum. -/
theorem natDegree_eq_and_leadingCoeff_pos {k d D₀ : ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    (hrec : ∀ n, P (n + k) = rhs terms P n) (hlag : ∀ t ∈ terms, t.1 < k)
    (hA : ∀ t ∈ terms, ∀ n, (t.2.2 n).natDegree ≤ d * (k - t.1) + t.2.1)
    (hbase : ∀ j < k, (P j).natDegree ≤ D₀ + d * j ∧ 0 < (P j).coeff (D₀ + d * j))
    (hmult : ∀ n, ∀ j < k, 0 ≤ lagMult k d D₀ terms n j)
    (hpos : ∀ n, 0 < (terms.map (topCoeff k d D₀ n)).sum) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ 0 < (P n).leadingCoeff := by
  have key : ∀ m, (P m).natDegree ≤ D₀ + d * m ∧ 0 < (P m).coeff (D₀ + d * m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m k with hm | hm
      · exact hbase m hm
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by lia⟩
      have hP : ∀ j < k, (P (n + j)).natDegree ≤ D₀ + d * (n + j) :=
        fun j hj => (ih (n + j) (by lia)).1
      have hstep := rhs_step (D₀ := D₀) n terms hlag (fun t ht => hA t ht n) hP
      rw [hrec n]
      refine ⟨hstep.1, ?_⟩
      rw [hstep.2, sum_map_eq_sum_lag _ (fun j => (P (n + j)).coeff (D₀ + d * (n + j))) terms
        hlag]
      have htot : ∑ j ∈ Finset.range k, lagMult k d D₀ terms n j =
          (terms.map (topCoeff k d D₀ n)).sum := by
        have h := sum_map_eq_sum_lag (topCoeff k d D₀ n) (fun _ => 1) terms hlag
        simp only [mul_one] at h
        rw [h]
        rfl
      have hc : ∀ j ∈ Finset.range k, 0 < (P (n + j)).coeff (D₀ + d * (n + j)) :=
        fun j hj => (ih (n + j) (by have := Finset.mem_range.mp hj; lia)).2
      refine Finset.sum_pos' (fun j hj => mul_nonneg (hmult n j (Finset.mem_range.mp hj))
        (hc j hj).le) ?_
      by_contra hne
      push Not at hne
      have hle : ∑ j ∈ Finset.range k, lagMult k d D₀ terms n j ≤ 0 :=
        Finset.sum_nonpos fun j hj => by
          have h : lagMult k d D₀ terms n j * (P (n + j)).coeff (D₀ + d * (n + j)) ≤ 0 :=
            hne j hj
          nlinarith [hc j hj]
      linarith [hpos n]
  have h := key n
  have hdeg : (P n).natDegree = D₀ + d * n :=
    natDegree_eq_of_le_of_coeff_ne_zero h.1 h.2.ne'
  exact ⟨hdeg, by rw [leadingCoeff, hdeg]; exact h.2⟩

/-- Rows of `P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` have degree `D₀ + d * n` and
leading coefficient `c n`, when the summands have degree at most `D₀ + d * (n + k)`, the
first `k` rows have coefficient `c j` at `D₀ + d * j`, the sequence `c` never vanishes
and solves the scalar recurrence of the top coefficients.  This covers multipliers of
either sign, such as `c n = c₀ * ρ ^ n`. -/
theorem natDegree_eq_and_leadingCoeff_eq {k d D₀ : ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))} {c : ℕ → ℝ}
    (hrec : ∀ n, P (n + k) = rhs terms P n) (hlag : ∀ t ∈ terms, t.1 < k)
    (hA : ∀ t ∈ terms, ∀ n, (t.2.2 n).natDegree ≤ d * (k - t.1) + t.2.1)
    (hbase : ∀ j < k, (P j).natDegree ≤ D₀ + d * j ∧ (P j).coeff (D₀ + d * j) = c j)
    (hc : ∀ n, c (n + k) = ∑ j ∈ Finset.range k, lagMult k d D₀ terms n j * c (n + j))
    (hc0 : ∀ n, c n ≠ 0) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ (P n).leadingCoeff = c n := by
  have key : ∀ m, (P m).natDegree ≤ D₀ + d * m ∧ (P m).coeff (D₀ + d * m) = c m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m k with hm | hm
      · exact hbase m hm
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by lia⟩
      have hP : ∀ j < k, (P (n + j)).natDegree ≤ D₀ + d * (n + j) :=
        fun j hj => (ih (n + j) (by lia)).1
      have hstep := rhs_step (D₀ := D₀) n terms hlag (fun t ht => hA t ht n) hP
      rw [hrec n]
      refine ⟨hstep.1, ?_⟩
      rw [hstep.2, sum_map_eq_sum_lag _ (fun j => (P (n + j)).coeff (D₀ + d * (n + j))) terms
        hlag, hc n]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(ih (n + j) (by have := Finset.mem_range.mp hj; lia)).2]
      rfl
  have h := key n
  have hdeg : (P n).natDegree = D₀ + d * n :=
    natDegree_eq_of_le_of_coeff_ne_zero h.1 (h.2 ▸ hc0 n)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, h.2]⟩

end RealRooted.LinRec

/-!
## Scalar linear recurrences with a positivity invariant

Pure real-sequence layer for the top-coefficient recurrences that arise from linear
polynomial recurrences.  A sequence `c` solves the order-`k` recurrence with multipliers `m`
when `c (n + k) = ∑ j < k, m n j * c (n + j)`.  The multipliers may be negative; positivity of
`c` is then obtained from a growth-ratio invariant `ρ * c n ≤ c (n + 1)`, whose step is a
finite arithmetic condition on an abstract window `x`.
-/

namespace RealRooted.ScalarRec

/-- `c (n + k) = ∑_{j < k} m n j * c (n + j)`. -/
def IsSolution (k : ℕ) (m : ℕ → ℕ → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ n, c (n + k) = ∑ j ∈ Finset.range k, m n j * c (n + j)

/-- Nonnegative multipliers with positive total weight and positive initial values give a
positive solution. -/
theorem pos_of_nonneg {k : ℕ} {m : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc : IsSolution k m c)
    (hbase : ∀ j < k, 0 < c j) (hm : ∀ n, ∀ j < k, 0 ≤ m n j)
    (hsum : ∀ n, 0 < ∑ j ∈ Finset.range k, m n j) (n : ℕ) : 0 < c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < k
    · exact hbase n hn
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + k := ⟨n - k, by lia⟩
      rw [hc n]
      have hpos : ∀ j ∈ Finset.range k, 0 < c (n + j) := fun j hj =>
        ih _ (by have := Finset.mem_range.1 hj; lia)
      have hnn : ∀ j ∈ Finset.range k, 0 ≤ m n j * c (n + j) := fun j hj =>
        mul_nonneg (hm n j (Finset.mem_range.1 hj)) (hpos j hj).le
      obtain ⟨j, hj, hmj⟩ : ∃ j ∈ Finset.range k, 0 < m n j := by
        by_contra hcon
        push Not at hcon
        exact absurd (hsum n) (not_lt.2 (Finset.sum_nonpos hcon))
      exact Finset.sum_pos' hnn ⟨j, hj, mul_pos hmj (hpos j hj)⟩

/-- Growth-ratio invariant `ρ * c n ≤ c (n + 1)`, order `k`; the step condition is
stated for an abstract window `x` so that the tactic can close it by `nlinarith`
after unfolding the multipliers. For `k = 2` and `m n 0 ≤ 0` this is
`RealRooted.threeTermRatio_*`. -/
theorem pos_of_ratio {k : ℕ} {m : ℕ → ℕ → ℝ} {c : ℕ → ℝ} {ρ : ℝ} (hk : k ≠ 0) (hρ : 0 < ρ)
    (hc : IsSolution k m c) (h0 : 0 < c 0)
    (hbase : ∀ j, j + 1 < k → ρ * c j ≤ c (j + 1))
    (hstep : ∀ n (x : ℕ → ℝ), 0 < x 0 → (∀ j, j + 1 < k → ρ * x j ≤ x (j + 1)) →
      ρ * x (k - 1) ≤ ∑ j ∈ Finset.range k, m n j * x j) (n : ℕ) : 0 < c n := by
  have key : ∀ n, 0 < c n ∧ ∀ j, j + 1 < k → ρ * c (n + j) ≤ c (n + j + 1) := by
    intro n
    induction n with
    | zero => simpa using And.intro h0 hbase
    | succ n ih =>
      obtain ⟨hpos, hrat⟩ := ih
      have hlast : ρ * c (n + (k - 1)) ≤ c (n + (k - 1) + 1) := by
        have h := hstep n (fun j => c (n + j)) (by simpa using hpos)
          (fun j hj => by simpa only [← add_assoc] using hrat j hj)
        rw [← hc n] at h
        have e : n + (k - 1) + 1 = n + k := by lia
        rw [e]
        simpa using h
      have hext : ∀ j, j < k → ρ * c (n + j) ≤ c (n + j + 1) := by
        intro j hj
        by_cases h : j + 1 < k
        · exact hrat j h
        · obtain rfl : j = k - 1 := by lia
          exact hlast
      have hall : ∀ j, j ≤ k → 0 < c (n + j) := by
        intro j
        induction j with
        | zero => simpa using hpos
        | succ j ihj =>
          intro hj
          have h1 := hext j (by lia)
          have h2 := mul_pos hρ (ihj (by lia))
          exact h2.trans_le h1
      refine ⟨by simpa [add_comm] using hall 1 (by lia), fun j hj => ?_⟩
      have := hext (j + 1) hj
      simpa [add_assoc, add_comm, add_left_comm] using this
  exact (key n).1

/-- Two-sided version `ρ * c n ≤ c (n + 1) ≤ σ * c n` (A092879-type: `c = ⌊n/2⌋ + 1`). -/
theorem pos_of_ratio_bounds {k : ℕ} {m : ℕ → ℕ → ℝ} {c : ℕ → ℝ} {ρ σ : ℝ} (hk : k ≠ 0)
    (hρ : 0 < ρ) (hc : IsSolution k m c) (h0 : 0 < c 0)
    (hbase : ∀ j, j + 1 < k → ρ * c j ≤ c (j + 1) ∧ c (j + 1) ≤ σ * c j)
    (hstep : ∀ n (x : ℕ → ℝ), 0 < x 0 →
      (∀ j, j + 1 < k → ρ * x j ≤ x (j + 1) ∧ x (j + 1) ≤ σ * x j) →
      ρ * x (k - 1) ≤ ∑ j ∈ Finset.range k, m n j * x j ∧
        ∑ j ∈ Finset.range k, m n j * x j ≤ σ * x (k - 1)) (n : ℕ) : 0 < c n := by
  have key : ∀ n, 0 < c n ∧
      ∀ j, j + 1 < k → ρ * c (n + j) ≤ c (n + j + 1) ∧ c (n + j + 1) ≤ σ * c (n + j) := by
    intro n
    induction n with
    | zero => simpa using And.intro h0 hbase
    | succ n ih =>
      obtain ⟨hpos, hrat⟩ := ih
      have hlast : ρ * c (n + (k - 1)) ≤ c (n + (k - 1) + 1) ∧
          c (n + (k - 1) + 1) ≤ σ * c (n + (k - 1)) := by
        have h := hstep n (fun j => c (n + j)) (by simpa using hpos)
          (fun j hj => by simpa only [← add_assoc] using hrat j hj)
        rw [← hc n] at h
        have e : n + (k - 1) + 1 = n + k := by lia
        rw [e]
        simpa using h
      have hext : ∀ j, j < k →
          ρ * c (n + j) ≤ c (n + j + 1) ∧ c (n + j + 1) ≤ σ * c (n + j) := by
        intro j hj
        by_cases h : j + 1 < k
        · exact hrat j h
        · obtain rfl : j = k - 1 := by lia
          exact hlast
      have hall : ∀ j, j ≤ k → 0 < c (n + j) := by
        intro j
        induction j with
        | zero => simpa using hpos
        | succ j ihj =>
          intro hj
          have h1 := (hext j (by lia)).1
          have h2 := mul_pos hρ (ihj (by lia))
          exact h2.trans_le h1
      refine ⟨by simpa [add_comm] using hall 1 (by lia), fun j hj => ?_⟩
      have := hext (j + 1) hj
      simpa [add_assoc, add_comm, add_left_comm] using this
  exact (key n).1

/-! ### Examples -/

/-- Order three, negative multiplier `m n 0 = -1`: `c (n+3) = 2 c (n+2) - c n`. -/
example (c : ℕ → ℝ) (h : ∀ n, c (n + 3) = 2 * c (n + 2) - c n)
    (h0 : c 0 = 1) (h1 : c 1 = 2) (h2 : c 2 = 3) (n : ℕ) : 0 < c n := by
  refine pos_of_ratio (k := 3) (m := fun _ j => if j = 0 then -1 else if j = 1 then 0 else 2)
    (ρ := 1) (by norm_num) one_pos (fun n => ?_) (by simp [h0]) (fun j hj => ?_)
    (fun n x hx0 hx => ?_) n
  · simp [Finset.sum_range_succ, h n]
    ring
  · have hj' : j < 2 := by lia
    interval_cases j <;> norm_num [h0, h1, h2]
  · have h01 : x 0 ≤ x 1 := by simpa using hx 0 (by norm_num)
    have h12 : x 1 ≤ x 2 := by simpa using hx 1 (by norm_num)
    simp [Finset.sum_range_succ]
    linarith

/-- Order two: `c (n+2) = 2 c (n+1) - c n`, `c 0 = 1`, `c 1 = 2`. -/
example (c : ℕ → ℝ) (h : ∀ n, c (n + 2) = 2 * c (n + 1) - c n)
    (h0 : c 0 = 1) (h1 : c 1 = 2) (n : ℕ) : 0 < c n := by
  refine pos_of_ratio (k := 2) (m := fun _ j => if j = 0 then -1 else 2)
    (ρ := 1) (by norm_num) one_pos (fun n => ?_) (by simp [h0]) (fun j hj => ?_)
    (fun n x hx0 hx => ?_) n
  · simp [Finset.sum_range_succ, h n]
    ring
  · have hj' : j < 1 := by lia
    interval_cases j
    simp [h0, h1]
  · have h01 : x 0 ≤ x 1 := by simpa using hx 0 (by norm_num)
    simp [Finset.sum_range_succ]
    linarith

/-- Fibonacci-type top coefficients (A046741 top coefficients `1, 1, 2, 3, 5, ...`). -/
example (c : ℕ → ℝ) (h : ∀ n, c (n + 2) = c (n + 1) + c n)
    (h0 : c 0 = 1) (h1 : c 1 = 1) (n : ℕ) : 0 < c n := by
  refine pos_of_nonneg (k := 2) (m := fun _ _ => 1) (fun n => ?_) (fun j hj => ?_)
    (fun _ _ _ => zero_le_one) (fun n => ?_) n
  · simp [Finset.sum_range_succ, h n, add_comm]
  · have hj' : j < 2 := hj
    interval_cases j <;> simp [h0, h1]
  · simp

end RealRooted.ScalarRec

/-!
## Degrees of general linear recurrences with an arbitrary degree law

`RealRooted.LinRec.natDegree_eq_and_leadingCoeff_pos` and
`RealRooted.LinRec.natDegree_eq_and_leadingCoeff_eq` treat the linear degree law
`D n = D₀ + d * n`.  Here the degree law is an arbitrary function `D : ℕ → ℕ` that is
monotone along each window `D (n + j) ≤ D (n + k)`, `j < k`.  Periodic laws such as
`D n = D₀ + d * ((n + e) / p)` are the main application; the arithmetic of
`D (p * q + r + j)` is reduced to numerals by one residue decomposition.

The summand `t = (j, i, A)` of the recurrence
`P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` contributes to the top coefficient at
`D (n + k)` the coefficient of `A n` at `D (n + k) - D (n + j) + i`, times the falling
factorial of the degree `D (n + j)` of the row it differentiates.
-/

open Polynomial

namespace RealRooted.LinRec

/-- Top-coefficient multiplier of the summand `t = (j, i, A)` at step `n` for the
degree law `D`: the coefficient of `A n` at `D (n + k) - D (n + j) + i` times the
falling factorial `(D (n + j))_i`. -/
noncomputable def topCoeffD (k : ℕ) (D : ℕ → ℕ) (n : ℕ) (t : ℕ × ℕ × (ℕ → ℝ[X])) : ℝ :=
  (t.2.2 n).coeff (D (n + k) - D (n + t.1) + t.2.1) *
    ((D (n + t.1)).descFactorial t.2.1 : ℝ)

/-- The top-coefficient multiplier of the lag `j` for the degree law `D`: the sum of
`topCoeffD` over the summands that act on the row `P (n + j)`. -/
noncomputable def lagMultD (k : ℕ) (D : ℕ → ℕ) (terms : List (ℕ × ℕ × (ℕ → ℝ[X])))
    (n j : ℕ) : ℝ :=
  ((terms.filter fun t => t.1 = j).map (topCoeffD k D n)).sum

private theorem descFactorial_castD (N i : ℕ) :
    (N.descFactorial i : ℝ) = ∏ l ∈ Finset.range i, ((N : ℝ) - l) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Nat.descFactorial_succ, Finset.prod_range_succ, ← ih, Nat.cast_mul]
      rcases le_or_gt i N with h | h
      · rw [Nat.cast_sub h]
        ring
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
        simp

/-- One step for a degree law: if the rows `P (n + j)`, `j < k`, have degree at most
`D (n + j)`, then the right side has degree at most `D (n + k)`, with top coefficient
`∑ₜ topCoeffD t * (P (n + jₜ)).coeff (D (n + jₜ))`. -/
private theorem rhs_stepD {k : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]} (n : ℕ)
    (hD : ∀ j, j < k → D (n + j) ≤ D (n + k)) :
    ∀ terms : List (ℕ × ℕ × (ℕ → ℝ[X])), (∀ t ∈ terms, t.1 < k) →
      (∀ t ∈ terms, (t.2.2 n).natDegree ≤ D (n + k) - D (n + t.1) + t.2.1) →
      (∀ j < k, (P (n + j)).natDegree ≤ D (n + j)) →
      (rhs terms P n).natDegree ≤ D (n + k) ∧
        (rhs terms P n).coeff (D (n + k)) =
          (terms.map fun t => topCoeffD k D n t * (P (n + t.1)).coeff (D (n + t.1))).sum
  | [], _, _, _ => by simp [rhs]
  | t :: ts, hlag, hA, hP => by
      have hj := hlag t (by simp)
      have hN : D (n + t.1) + (D (n + k) - D (n + t.1)) = D (n + k) :=
        Nat.add_sub_cancel' (hD t.1 hj)
      have ih := rhs_stepD n hD ts (fun s hs => hlag s (by simp [hs]))
        (fun s hs => hA s (by simp [hs])) hP
      have h1 := natDegree_mul_iterate_derivative_le (d := D (n + k) - D (n + t.1))
        (j := t.2.1) (hA t (by simp)) (hP t.1 hj)
      have h2 := coeff_mul_iterate_derivative_of_natDegree_le
        (d := D (n + k) - D (n + t.1)) (j := t.2.1) (hA t (by simp)) (hP t.1 hj)
      rw [hN] at h1 h2
      simp only [rhs, List.map_cons, List.sum_cons] at ih ⊢
      refine ⟨natDegree_add_le_of_degree_le h1 ih.1, ?_⟩
      rw [coeff_add, h2, ih.2, topCoeffD]

/-- Regroup a sum over the summands by their lags `j < k`. -/
private theorem sum_map_eq_sum_lagD {k : ℕ} (f : ℕ × ℕ × (ℕ → ℝ[X]) → ℝ) (g : ℕ → ℝ) :
    ∀ terms : List (ℕ × ℕ × (ℕ → ℝ[X])), (∀ t ∈ terms, t.1 < k) →
      (terms.map fun t => f t * g t.1).sum =
        ∑ j ∈ Finset.range k, ((terms.filter fun t => t.1 = j).map f).sum * g j
  | [], _ => by simp
  | t :: ts, hlag => by
      rw [List.map_cons, List.sum_cons,
        sum_map_eq_sum_lagD f g ts (fun s hs => hlag s (by simp [hs]))]
      have hj : t.1 ∈ Finset.range k := Finset.mem_range.mpr (hlag t (by simp))
      simp only [List.filter_cons, decide_eq_true_eq]
      rw [← Finset.add_sum_erase _ _ hj, ← Finset.add_sum_erase _ _ hj, ← add_assoc]
      congr 1
      · simp [add_mul]
      · refine Finset.sum_congr rfl fun j hj' => ?_
        simp [Ne.symm (Finset.ne_of_mem_erase hj')]

/-- Degree bounds for every row and the scalar recurrence of the top coefficients, for an
arbitrary degree law `D`. -/
theorem natDegree_le_and_coeff_rec {k : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    (hrec : ∀ n, P (n + k) = rhs terms P n) (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms, ∀ n, (t.2.2 n).natDegree ≤ D (n + k) - D (n + t.1) + t.2.1)
    (hbase : ∀ j < k, (P j).natDegree ≤ D j) :
    (∀ n, (P n).natDegree ≤ D n) ∧
      ∀ n, (P (n + k)).coeff (D (n + k)) =
        ∑ j ∈ Finset.range k, lagMultD k D terms n j * (P (n + j)).coeff (D (n + j)) := by
  have hle : ∀ m, (P m).natDegree ≤ D m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m k with hm | hm
      · exact hbase m hm
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by lia⟩
      rw [hrec n]
      exact (rhs_stepD n (hD n) terms hlag (fun t ht => hA t ht n)
        fun j hj => ih (n + j) (by lia)).1
  refine ⟨hle, fun n => ?_⟩
  have hstep := rhs_stepD n (hD n) terms hlag (fun t ht => hA t ht n)
    fun j hj => hle (n + j)
  rw [hrec n, hstep.2]
  exact sum_map_eq_sum_lagD (topCoeffD k D n) (fun j => (P (n + j)).coeff (D (n + j))) terms
    hlag

/-- A degree bound together with a nonvanishing coefficient at the bound gives the degree
and the leading coefficient. -/
theorem natDegree_eq_and_leadingCoeff_eq_of_coeff {D : ℕ → ℕ} {P : ℕ → ℝ[X]} {c : ℕ → ℝ}
    (hle : ∀ n, (P n).natDegree ≤ D n) (hc : ∀ n, (P n).coeff (D n) = c n)
    (hc0 : ∀ n, c n ≠ 0) (n : ℕ) :
    (P n).natDegree = D n ∧ (P n).leadingCoeff = c n := by
  have hdeg : (P n).natDegree = D n :=
    natDegree_eq_of_le_of_coeff_ne_zero (hle n) (hc n ▸ hc0 n)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hc n]⟩

/-- Rows of `P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` have degree `D n` and positive
leading coefficients, for an arbitrary degree law `D`, when the summands have degree at
most `D (n + k) - D (n + jₜ) + iₜ`, the first `k` rows have positive coefficients at
`D j`, and the lag multipliers `lagMultD` are nonnegative with a positive sum. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_degreeLaw {k : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    (hrec : ∀ n, P (n + k) = rhs terms P n) (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms, ∀ n, (t.2.2 n).natDegree ≤ D (n + k) - D (n + t.1) + t.2.1)
    (hbase : ∀ j < k, (P j).natDegree ≤ D j ∧ 0 < (P j).coeff (D j))
    (hmult : ∀ n, ∀ j < k, 0 ≤ lagMultD k D terms n j)
    (hpos : ∀ n, 0 < ∑ j ∈ Finset.range k, lagMultD k D terms n j) (n : ℕ) :
    (P n).natDegree = D n ∧ 0 < (P n).leadingCoeff := by
  obtain ⟨hle, hcoef⟩ := natDegree_le_and_coeff_rec hrec hlag hD hA fun j hj => (hbase j hj).1
  have key : ∀ m, 0 < (P m).coeff (D m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m k with hm | hm
      · exact (hbase m hm).2
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by lia⟩
      rw [hcoef n]
      have hc : ∀ j ∈ Finset.range k, 0 < (P (n + j)).coeff (D (n + j)) :=
        fun j hj => ih (n + j) (by have := Finset.mem_range.mp hj; lia)
      refine Finset.sum_pos' (fun j hj => mul_nonneg (hmult n j (Finset.mem_range.mp hj))
        (hc j hj).le) ?_
      by_contra hne
      push Not at hne
      have hle' : ∑ j ∈ Finset.range k, lagMultD k D terms n j ≤ 0 :=
        Finset.sum_nonpos fun j hj => by
          have h : lagMultD k D terms n j * (P (n + j)).coeff (D (n + j)) ≤ 0 := hne j hj
          nlinarith [hc j hj]
      linarith [hpos n]
  have hdeg : (P n).natDegree = D n :=
    natDegree_eq_of_le_of_coeff_ne_zero (hle n) (key n).ne'
  exact ⟨hdeg, by rw [leadingCoeff, hdeg]; exact key n⟩

/-- Rows of `P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` have degree `D n` and leading
coefficient `c n`, for an arbitrary degree law `D`, when the first `k` rows have
coefficient `c j` at `D j`, and the nonvanishing sequence `c` solves the scalar recurrence
of the top coefficients.  This covers multipliers of either sign. -/
theorem natDegree_eq_and_leadingCoeff_eq_of_degreeLaw {k : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))} {c : ℕ → ℝ}
    (hrec : ∀ n, P (n + k) = rhs terms P n) (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms, ∀ n, (t.2.2 n).natDegree ≤ D (n + k) - D (n + t.1) + t.2.1)
    (hbase : ∀ j < k, (P j).natDegree ≤ D j ∧ (P j).coeff (D j) = c j)
    (hc : ∀ n, c (n + k) = ∑ j ∈ Finset.range k, lagMultD k D terms n j * c (n + j))
    (hc0 : ∀ n, c n ≠ 0) (n : ℕ) :
    (P n).natDegree = D n ∧ (P n).leadingCoeff = c n := by
  obtain ⟨hle, hcoef⟩ := natDegree_le_and_coeff_rec hrec hlag hD hA fun j hj => (hbase j hj).1
  have key : ∀ m, (P m).coeff (D m) = c m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m k with hm | hm
      · exact (hbase m hm).2
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by lia⟩
      rw [hcoef n, hc n]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih (n + j) (by have := Finset.mem_range.mp hj; lia)]
  exact natDegree_eq_and_leadingCoeff_eq_of_coeff hle key hc0 n

/-- The linear law is the special case `D n = D₀ + d * n`: `lagMultD` is `lagMult`. -/
theorem lagMultD_linear (k d D₀ : ℕ) (terms : List (ℕ × ℕ × (ℕ → ℝ[X]))) (n j : ℕ) :
    lagMultD k (fun n => D₀ + d * n) terms n j = lagMult k d D₀ terms n j := by
  have h : ∀ t : ℕ × ℕ × (ℕ → ℝ[X]), topCoeffD k (fun n => D₀ + d * n) n t =
      topCoeff k d D₀ n t := by
    intro t
    have hsub : D₀ + d * (n + k) - (D₀ + d * (n + t.1)) = d * (k - t.1) := by
      rw [Nat.add_sub_add_left, ← Nat.mul_sub, Nat.add_sub_add_left]
    rw [topCoeffD, topCoeff, hsub, descFactorial_castD]
  unfold lagMultD lagMult
  exact congrArg List.sum (List.map_congr_left fun t _ => h t)

/-- Monotonicity of a periodic degree law `D n = D₀ + d * ((n + e) / p)` along a window,
the first side condition `hD` of the degree-law theorems. -/
theorem degreeLaw_periodic_mono {p D₀ d e k : ℕ} :
    ∀ n j, j < k →
      D₀ + d * ((n + j + e) / p) ≤ D₀ + d * ((n + k + e) / p) := by
  intro n j hj
  have : (n + j + e) / p ≤ (n + k + e) / p := Nat.div_le_div_right (by lia)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left d this) D₀

/-- Residue decomposition of a periodic degree law: shifting by `p * q` shifts the value
by `d * q`. -/
theorem degreeLaw_periodic_decomp {p D₀ d e : ℕ} (hp : 0 < p) (q r c : ℕ) :
    D₀ + d * ((p * q + r + c + e) / p) = D₀ + d * (q + (r + c + e) / p) := by
  rw [add_assoc (p * q + r) c e, add_assoc (p * q) r (c + e), Nat.mul_add_div hp,
    ← add_assoc r c e]

/-- Example (A102547): `P (n + 3) = P (n + 2) + X * P n` with `P 0 = P 1 = P 2 = 1` has
`natDegree (P n) = n / 3` and positive leading coefficients. -/
example (P : ℕ → ℝ[X]) (h0 : P 0 = 1) (h1 : P 1 = 1) (h2 : P 2 = 1)
    (hP : ∀ n, P (n + 3) = P (n + 2) + X * P n) (n : ℕ) :
    (P n).natDegree = n / 3 ∧ 0 < (P n).leadingCoeff := by
  refine natDegree_eq_and_leadingCoeff_pos_of_degreeLaw (k := 3) (D := fun n => n / 3)
    (terms := [(2, 0, fun _ => 1), (0, 0, fun _ => X)]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ n
  · intro n
    simp [rhs, hP]
  · simp
  · intro n j hj
    exact Nat.div_le_div_right (by lia)
  · intro t ht n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp
    · simp only [natDegree_X, add_zero]
      lia
  · intro j hj
    interval_cases j <;> simp [h0, h1, h2]
  · intro n j hj
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r := ⟨n / 3, n % 3, by lia, by lia⟩
    interval_cases j <;> interval_cases r <;>
      simp [lagMultD, topCoeffD, coeff_one, Nat.add_assoc, Nat.mul_add_div]
  · intro n
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r := ⟨n / 3, n % 3, by lia, by lia⟩
    interval_cases r <;>
      simp [lagMultD, topCoeffD, coeff_one, Finset.sum_range_succ, Nat.add_assoc,
        Nat.mul_add_div]

end RealRooted.LinRec

/-!
## Rows of general linear recurrences with negative multipliers

Bridge between the top-coefficient recurrence of `RealRooted.LinRec.natDegree_le_and_coeff_rec`
and the growth-ratio invariant `RealRooted.ScalarRec.pos_of_ratio`: the lag multipliers
`lagMultD` may be negative, as long as the top coefficients `(P n).coeff (D n)` satisfy
`ρ * c n ≤ c (n + 1)` along the recurrence.
-/

open Polynomial

namespace RealRooted.LinRec

/-- Rows of `P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` have degree `D n` and positive leading
coefficients for an arbitrary degree law `D` when the lag multipliers `lagMultD` may be
negative but preserve the growth-ratio invariant `ρ * c n ≤ c (n + 1)` of the top coefficients
`c n = (P n).coeff (D n)`.  The step hypothesis `hstep` is stated for an abstract window `x`. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_ratio {k : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))} {ρ : ℝ} (hk : k ≠ 0) (hρ : 0 < ρ)
    (hrec : ∀ n, P (n + k) = rhs terms P n) (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms, ∀ n, (t.2.2 n).natDegree ≤ D (n + k) - D (n + t.1) + t.2.1)
    (hbase : ∀ j < k, (P j).natDegree ≤ D j) (h0 : 0 < (P 0).coeff (D 0))
    (hb : ∀ j, j + 1 < k → ρ * (P j).coeff (D j) ≤ (P (j + 1)).coeff (D (j + 1)))
    (hstep : ∀ n (x : ℕ → ℝ), 0 < x 0 → (∀ j, j + 1 < k → ρ * x j ≤ x (j + 1)) →
      ρ * x (k - 1) ≤ ∑ j ∈ Finset.range k, lagMultD k D terms n j * x j) (n : ℕ) :
    (P n).natDegree = D n ∧ 0 < (P n).leadingCoeff := by
  obtain ⟨hle, hcoef⟩ := natDegree_le_and_coeff_rec hrec hlag hD hA hbase
  have hpos : ∀ m, 0 < (P m).coeff (D m) :=
    RealRooted.ScalarRec.pos_of_ratio (m := lagMultD k D terms) hk hρ hcoef h0 hb hstep
  obtain ⟨hdeg, hlc⟩ := natDegree_eq_and_leadingCoeff_eq_of_coeff hle (fun m => rfl)
    (fun m => (hpos m).ne') n
  exact ⟨hdeg, hlc ▸ hpos n⟩

/-- Example: `P (n + 3) = 2 X * P (n + 2) - X ^ 3 * P n` (multiplier `-1` on the top
coefficient of `P n`) with `P 0 = 1`, `P 1 = 2 X`, `P 2 = 3 X ^ 2` has `natDegree (P n) = n`
and positive leading coefficients; the top coefficients satisfy `c (n + 3) = 2 c (n + 2) - c n`. -/
example (P : ℕ → ℝ[X]) (h0 : P 0 = 1) (h1 : P 1 = C 2 * X) (h2 : P 2 = C 3 * X ^ 2)
    (hP : ∀ n, P (n + 3) = C 2 * X * P (n + 2) - X ^ 3 * P n) (n : ℕ) :
    (P n).natDegree = n ∧ 0 < (P n).leadingCoeff := by
  refine natDegree_eq_and_leadingCoeff_pos_of_ratio (k := 3) (D := fun n => n)
    (terms := [(2, 0, fun _ => C 2 * X), (0, 0, fun _ => - X ^ 3)]) (ρ := 1) (by norm_num)
    one_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ n
  · intro n
    simp [rhs, hP]
    ring
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> norm_num
  · intro n j hj
    lia
  · intro t ht n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp only [Nat.add_sub_add_left]
      exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp only [natDegree_neg, natDegree_X_pow]
      lia
  · intro j hj
    interval_cases j <;> simp [h0, h1, h2]
  · simp [h0]
  · intro j hj
    have hj' : j < 2 := by lia
    interval_cases j <;> norm_num [h0, h1, h2]
  · intro n x hx0 hx
    have h01 : x 0 ≤ x 1 := by simpa using hx 0 (by norm_num)
    have h12 : x 1 ≤ x 2 := by simpa using hx 1 (by norm_num)
    simp [lagMultD, topCoeffD, Finset.sum_range_succ]
    linarith

end RealRooted.LinRec
