module

public import RealRooted.DerivativeRecurrence.General
public import RealRooted.DerivativeRecurrence.Interlacing

/-!
# Regression examples for the cancellation degree law

The rows of OEIS A008970 and A094503 have a summand of degree one more than the claimed
degree; `LinRec.natDegree_eq_and_leadingCoeff_pos_of_cancel` still gives their exact degree
and positive leading coefficient (issue #1321).
-/

public section

open Polynomial

namespace RealRooted.LinRec

/-- The cancellation certificate specializes to the recurrence of OEIS A008970. -/
example (P : ℕ → ℝ[X]) (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) = (X - X ^ 3) * (P n).derivative +
      (1 + C 2 * X + C (n : ℝ) * X ^ 2) * P n)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (n : ℕ) :
    (P n).natDegree = n ∧ 0 < (P n).leadingCoeff := by
  let terms : List (ℕ × ℕ × (ℕ → ℝ[X])) :=
    [(0, 1, fun _ => X - X ^ 3),
      (0, 0, fun q => 1 + C 2 * X + C (q : ℝ) * X ^ 2)]
  have hAdeg : (X - X ^ 3 : ℝ[X]).natDegree ≤ 3 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have hBdeg : ∀ q : ℕ, (1 + C 2 * X + C (q : ℝ) * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
    intro q
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · simp
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have h := natDegree_eq_and_leadingCoeff_pos_of_cancel
    (k := 1) (D := fun q => q) (P := P) (terms := terms) (rho := fun _ => 0)
    (fun q => by simp [terms, rhs, hrec])
    (by intro t ht; simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ht;
        rcases ht with rfl | rfl <;> norm_num)
    (by intro q j hj; lia)
    (by
      intro t ht q
      simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hAdeg.trans (by lia)
      · exact (hBdeg q).trans (by lia))
    (by
      intro j hj
      have : j = 0 := by lia
      subst j
      refine ⟨by simp [hzero], by simp [hzero], hnn 0, by simp [hzero]⟩)
    (by
      intro q hprev
      obtain ⟨hle, hpos, -, -⟩ := hprev 0 (by norm_num)
      simp only [add_zero] at hle hpos
      have hdeg : (P q).natDegree = q :=
        natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne'
      have hlc : 0 < (P q).leadingCoeff := by
        rw [leadingCoeff, hdeg]
        exact hpos
      have hlocal := derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos_step_of_cancel
        (f := P q) (A := X - X ^ 3)
        (B := 1 + C 2 * X + C (q : ℝ) * X ^ 2) (d := q) (d' := q + 1) (m := 2)
        (by norm_num) hAdeg
        (hBdeg q) (hnn q) hdeg hlc (by
          right
          simp only [coeff_sub, coeff_X, coeff_X_pow, coeff_add, coeff_one, coeff_C_mul]
          push_cast
          norm_num)
      have hrhs : rhs terms P q = (X - X ^ 3) * (P q).derivative +
          (1 + C 2 * X + C (q : ℝ) * X ^ 2) * P q := by
        simp [terms, rhs]
      rw [hrhs]
      have hnn' : HasNonnegCoeffs
          ((X - X ^ 3) * (P q).derivative +
            (1 + C 2 * X + C (q : ℝ) * X ^ 2) * P q) := by
        rw [← hrec q]
        exact hnn (q + 1)
      refine ⟨coeff_eq_zero_of_natDegree_lt (hlocal.1 ▸ by lia), ?_, hnn', ?_⟩
      · rw [← hlocal.1, coeff_natDegree]
        exact hlocal.2
      · simpa using hnn' q)
    n
  exact ⟨h.1, h.2.1⟩

/-- The same certificate handles the alternating cancellation in the recurrence of
OEIS A094503, whose degree law is `n / 2`. -/
example (P : ℕ → ℝ[X]) (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) = (X - C 2 * X ^ 2) * (P n).derivative +
      (1 + C (n : ℝ) * X) * P n)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (n : ℕ) :
    (P n).natDegree = n / 2 ∧ 0 < (P n).leadingCoeff := by
  let terms : List (ℕ × ℕ × (ℕ → ℝ[X])) :=
    [(0, 1, fun _ => X - C 2 * X ^ 2),
      (0, 0, fun q => 1 + C (q : ℝ) * X)]
  have hAdeg : (X - C 2 * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have hBdeg : ∀ q : ℕ, (1 + C (q : ℝ) * X : ℝ[X]).natDegree ≤ 1 := by
    intro q
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have h := natDegree_eq_and_leadingCoeff_pos_of_cancel
    (k := 1) (D := fun q => q / 2) (P := P) (terms := terms) (rho := fun _ => 0)
    (fun q => by simp [terms, rhs, hrec])
    (by intro t ht; simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ht;
        rcases ht with rfl | rfl <;> norm_num)
    (by
      intro q j hj
      have hjzero : j = 0 := by lia
      subst j
      exact Nat.div_le_div_right (by lia))
    (by
      intro t ht q
      simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hAdeg.trans (by
          have hmono : q / 2 ≤ (q + 1) / 2 := Nat.div_le_div_right (by lia)
          lia)
      · exact (hBdeg q).trans (by
          have hmono : q / 2 ≤ (q + 1) / 2 := Nat.div_le_div_right (by lia)
          lia))
    (by
      intro j hj
      have : j = 0 := by lia
      subst j
      refine ⟨by simp [hzero], by simp [hzero], hnn 0, by simp [hzero]⟩)
    (by
      intro q hprev
      obtain ⟨hle, hpos, -, -⟩ := hprev 0 (by norm_num)
      simp only [add_zero] at hle hpos
      have hdeg : (P q).natDegree = q / 2 :=
        natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne'
      have hlc : 0 < (P q).leadingCoeff := by
        rw [leadingCoeff, hdeg]
        exact hpos
      have hlocal := derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos_step_of_cancel
        (f := P q) (A := X - C 2 * X ^ 2) (B := 1 + C (q : ℝ) * X)
        (d := q / 2) (d' := (q + 1) / 2) (m := 1) (by norm_num) hAdeg (hBdeg q)
        (hnn q) hdeg hlc (by
          simp only [coeff_sub, coeff_X, coeff_C_mul, coeff_X_pow, coeff_add, coeff_one]
          push_cast
          rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
          · right
            refine ⟨?_, ?_, ?_, ?_⟩
            · norm_num
              have hdiv : q / 2 = r := by lia
              have hcast : (q : ℝ) = (r : ℝ) + r := by exact_mod_cast hr
              rw [hdiv]
              linarith
            · lia
            · norm_num
            · positivity
          · left
            refine ⟨?_, ?_⟩
            · norm_num
              have hdiv : q / 2 = r := by lia
              have hcast : (q : ℝ) = 2 * (r : ℝ) + 1 := by exact_mod_cast hr
              rw [hdiv]
              linarith
            · lia)
      have hrhs : rhs terms P q = (X - C 2 * X ^ 2) * (P q).derivative +
          (1 + C (q : ℝ) * X) * P q := by
        simp [terms, rhs]
      rw [hrhs]
      have hnn' : HasNonnegCoeffs
          ((X - C 2 * X ^ 2) * (P q).derivative + (1 + C (q : ℝ) * X) * P q) := by
        rw [← hrec q]
        exact hnn (q + 1)
      refine ⟨coeff_eq_zero_of_natDegree_lt (hlocal.1 ▸ by lia), ?_, hnn', ?_⟩
      · rw [← hlocal.1, coeff_natDegree]
        exact hlocal.2
      · simpa using hnn' ((q + 1) / 2 - 1))
    n
  exact ⟨h.1, h.2.1⟩

end RealRooted.LinRec
