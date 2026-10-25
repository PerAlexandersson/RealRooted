module

public import RealRooted.DerivativeRecurrence.General

/-!
# Multi-lag cancellation degree laws

This file extends the cancellation degree argument for a linear polynomial recurrence from
one possible excess degree and one fixed ratio invariant to an arbitrary finite excess window
and an arbitrary state predicate.  In applications the state records the coefficients in a
finite window below the proposed degree.  The local step may combine all lags before proving
that every coefficient above the target cancels.
-/

@[expose] public section

open Polynomial

namespace RealRooted.LinRec

/-- If every input row has degree at most its value under `D`, then a `LinRec` right side
whose individual summands allow `e` excess degrees has degree at most `D (n + k) + e`.
The bound is deliberately applied before summing, so no sign condition is imposed on the
summands. -/
theorem rhs_natDegree_le_add_of_degreeLaw {k e : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))} (n : ℕ)
    (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms,
      (t.2.2 n).natDegree ≤ D (n + k) + e - D (n + t.1) + t.2.1)
    (hP : ∀ j < k, (P (n + j)).natDegree ≤ D (n + j)) :
    (rhs terms P n).natDegree ≤ D (n + k) + e := by
  induction terms with
  | nil => simp [rhs]
  | cons t ts ih =>
      have ht : t.1 < k := hlag t (by simp)
      have hDt : D (n + t.1) ≤ D (n + k) + e :=
        (hD t.1 ht).trans (Nat.le_add_right _ _)
      have hterm := natDegree_mul_iterate_derivative_le
        (d := D (n + k) + e - D (n + t.1)) (j := t.2.1)
        (hA t (by simp)) (hP t.1 ht)
      have hsum := ih (fun s hs => hlag s (by simp [hs]))
        (fun s hs => hA s (by simp [hs]))
      simp only [rhs, List.map_cons, List.sum_cons]
      refine (natDegree_add_le _ _).trans (max_le ?_ hsum)
      exact hterm.trans (Nat.add_sub_of_le hDt).le

/-- A polynomial of degree at most `N + e` whose coefficients in the whole excess window
`N + 1, ..., N + e` vanish has degree at most `N`. -/
theorem natDegree_le_of_le_add_of_coeff_window_eq_zero {p : ℝ[X]} {N e : ℕ}
    (hle : p.natDegree ≤ N + e)
    (hzero : ∀ r, 0 < r → r ≤ e → p.coeff (N + r) = 0) :
    p.natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  by_cases hje : j ≤ N + e
  · have hrpos : 0 < j - N := by lia
    have hrle : j - N ≤ e := by lia
    have h := hzero (j - N) hrpos hrle
    rwa [Nat.add_sub_of_le (by lia : N ≤ j)] at h
  · exact coeff_eq_zero_of_natDegree_lt (hle.trans_lt (by lia))

/-- Multi-lag cancellation degree law with a finite top-window state.

Each recurrence summand may reach as high as `D (n + k) + e`.  The step certificate is
checked only after all summands and lags have been combined: it kills every coefficient in
the excess window, proves positivity at the target degree, and evolves an arbitrary state
`S`.  The state can encode any finite vector of coefficients below the target together with
a cone invariant or a parity-dependent matrix update. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_topWindow {k e : ℕ} {D : ℕ → ℕ}
    {P : ℕ → ℝ[X]} {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    {S : ℕ → ℝ[X] → Prop}
    (hrec : ∀ n, P (n + k) = rhs terms P n)
    (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms, ∀ n,
      (t.2.2 n).natDegree ≤ D (n + k) + e - D (n + t.1) + t.2.1)
    (hbase : ∀ j < k,
      (P j).natDegree ≤ D j ∧ 0 < (P j).coeff (D j) ∧ S j (P j))
    (hstep : ∀ n,
      (∀ j < k,
        (P (n + j)).natDegree ≤ D (n + j) ∧
          0 < (P (n + j)).coeff (D (n + j)) ∧ S (n + j) (P (n + j))) →
      (∀ r, 0 < r → r ≤ e →
          (rhs terms P n).coeff (D (n + k) + r) = 0) ∧
        0 < (rhs terms P n).coeff (D (n + k)) ∧ S (n + k) (rhs terms P n))
    (n : ℕ) :
    (P n).natDegree = D n ∧ 0 < (P n).leadingCoeff ∧ S n (P n) := by
  have key : ∀ m,
      (P m).natDegree ≤ D m ∧ 0 < (P m).coeff (D m) ∧ S m (P m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm : m < k
        · exact hbase m hm
        · obtain ⟨q, rfl⟩ : ∃ q, m = q + k := ⟨m - k, by lia⟩
          have hprev : ∀ j < k,
              (P (q + j)).natDegree ≤ D (q + j) ∧
                0 < (P (q + j)).coeff (D (q + j)) ∧ S (q + j) (P (q + j)) := by
            intro j hj
            exact ih (q + j) (by lia)
          obtain ⟨hcancel, hpos, hstate⟩ := hstep q hprev
          rw [hrec q]
          exact ⟨natDegree_le_of_le_add_of_coeff_window_eq_zero
            (rhs_natDegree_le_add_of_degreeLaw q hlag (hD q)
              (fun t ht => hA t ht q) (fun j hj => (hprev j hj).1)) hcancel,
            hpos, hstate⟩
  obtain ⟨hle, hpos, hstate⟩ := key n
  have hdeg : (P n).natDegree = D n :=
    natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne'
  refine ⟨hdeg, ?_, hstate⟩
  rw [leadingCoeff, hdeg]
  exact hpos

/-- Multi-lag cancellation with a finite excess window and a top-two coefficient invariant.
The ratio may depend on the row index, so the theorem also covers periodic degree laws. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_topTwo
    {k e : ℕ} {D : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))} {rho : ℕ → ℝ}
    (hrec : ∀ n, P (n + k) = rhs terms P n)
    (hlag : ∀ t ∈ terms, t.1 < k)
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ t ∈ terms, ∀ n,
      (t.2.2 n).natDegree ≤ D (n + k) + e - D (n + t.1) + t.2.1)
    (hbase : ∀ j < k,
      (P j).natDegree ≤ D j ∧ 0 < (P j).coeff (D j) ∧
        HasNonnegCoeffs (P j) ∧
        rho j * (P j).coeff (D j) ≤ (P j).coeff (D j - 1))
    (hstep : ∀ n,
      (∀ j < k,
        (P (n + j)).natDegree ≤ D (n + j) ∧
          0 < (P (n + j)).coeff (D (n + j)) ∧
          HasNonnegCoeffs (P (n + j)) ∧
          rho (n + j) * (P (n + j)).coeff (D (n + j)) ≤
            (P (n + j)).coeff (D (n + j) - 1)) →
      (∀ r, 0 < r → r ≤ e →
          (rhs terms P n).coeff (D (n + k) + r) = 0) ∧
        0 < (rhs terms P n).coeff (D (n + k)) ∧
        HasNonnegCoeffs (rhs terms P n) ∧
        rho (n + k) * (rhs terms P n).coeff (D (n + k)) ≤
          (rhs terms P n).coeff (D (n + k) - 1))
    (n : ℕ) :
    (P n).natDegree = D n ∧ 0 < (P n).leadingCoeff ∧
      HasNonnegCoeffs (P n) ∧
      rho n * (P n).coeff (D n) ≤ (P n).coeff (D n - 1) := by
  exact natDegree_eq_and_leadingCoeff_pos_of_topWindow
    (S := fun m p => HasNonnegCoeffs p ∧
      rho m * p.coeff (D m) ≤ p.coeff (D m - 1))
    hrec hlag hD hA hbase hstep n


/-- A parity-split top-window induction.  Each half-step may first bound its new row by
`D m + e`, then cancel the whole excess window after all recurrence summands have been
combined.  The even and odd rows carry separate state predicates. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_parity_topWindows
    {evenExcess oddExcess : ℕ} {evenDegree oddDegree : ℕ → ℕ}
    {P : ℕ → ℝ[X]} {EvenState OddState : ℕ → ℝ[X] → Prop}
    (hbase :
      ((P 0).natDegree ≤ evenDegree 0 ∧
        0 < (P 0).coeff (evenDegree 0) ∧ EvenState 0 (P 0)) ∧
      ((P 1).natDegree ≤ oddDegree 0 ∧
        0 < (P 1).coeff (oddDegree 0) ∧ OddState 0 (P 1)))
    (hstep : ∀ m,
      ((P (2 * m)).natDegree ≤ evenDegree m ∧
          0 < (P (2 * m)).coeff (evenDegree m) ∧ EvenState m (P (2 * m))) →
      ((P (2 * m + 1)).natDegree ≤ oddDegree m ∧
          0 < (P (2 * m + 1)).coeff (oddDegree m) ∧ OddState m (P (2 * m + 1))) →
      ((P (2 * (m + 1))).natDegree ≤ evenDegree (m + 1) + evenExcess ∧
          (∀ r, 0 < r → r ≤ evenExcess →
            (P (2 * (m + 1))).coeff (evenDegree (m + 1) + r) = 0) ∧
          0 < (P (2 * (m + 1))).coeff (evenDegree (m + 1)) ∧
          EvenState (m + 1) (P (2 * (m + 1)))) ∧
        ((P (2 * (m + 1) + 1)).natDegree ≤ oddDegree (m + 1) + oddExcess ∧
          (∀ r, 0 < r → r ≤ oddExcess →
            (P (2 * (m + 1) + 1)).coeff (oddDegree (m + 1) + r) = 0) ∧
          0 < (P (2 * (m + 1) + 1)).coeff (oddDegree (m + 1)) ∧
          OddState (m + 1) (P (2 * (m + 1) + 1))))
    (m : ℕ) :
    ((P (2 * m)).natDegree = evenDegree m ∧
        0 < (P (2 * m)).leadingCoeff ∧ EvenState m (P (2 * m))) ∧
      ((P (2 * m + 1)).natDegree = oddDegree m ∧
        0 < (P (2 * m + 1)).leadingCoeff ∧ OddState m (P (2 * m + 1))) := by
  have hpair : ∀ j,
      ((P (2 * j)).natDegree ≤ evenDegree j ∧
          0 < (P (2 * j)).coeff (evenDegree j) ∧ EvenState j (P (2 * j))) ∧
        ((P (2 * j + 1)).natDegree ≤ oddDegree j ∧
          0 < (P (2 * j + 1)).coeff (oddDegree j) ∧ OddState j (P (2 * j + 1))) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
        obtain ⟨heven, hodd⟩ := hstep j ih.1 ih.2
        exact ⟨⟨natDegree_le_of_le_add_of_coeff_window_eq_zero heven.1 heven.2.1,
            heven.2.2.1, heven.2.2.2⟩,
          ⟨natDegree_le_of_le_add_of_coeff_window_eq_zero hodd.1 hodd.2.1,
            hodd.2.2.1, hodd.2.2.2⟩⟩
  obtain ⟨⟨hevenDegree, hevenPos, hevenState⟩,
    ⟨hoddDegree, hoddPos, hoddState⟩⟩ := hpair m
  have hevenEq : (P (2 * m)).natDegree = evenDegree m :=
    natDegree_eq_of_le_of_coeff_ne_zero hevenDegree hevenPos.ne'
  have hoddEq : (P (2 * m + 1)).natDegree = oddDegree m :=
    natDegree_eq_of_le_of_coeff_ne_zero hoddDegree hoddPos.ne'
  refine ⟨⟨hevenEq, ?_, hevenState⟩, ⟨hoddEq, ?_, hoddState⟩⟩
  · rw [leadingCoeff, hevenEq]
    exact hevenPos
  · rw [leadingCoeff, hoddEq]
    exact hoddPos

end RealRooted.LinRec
