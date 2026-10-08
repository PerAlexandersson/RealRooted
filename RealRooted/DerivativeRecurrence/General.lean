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
