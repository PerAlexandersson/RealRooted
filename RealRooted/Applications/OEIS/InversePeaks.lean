import RealRooted.DerivativeRecurrence.QuadraticLagStrict
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# The recurrence-defined inverse-peak polynomial family

We formalize the polynomial recurrence with virtual seed `K_{-1}=0` and
`K_0=1`.  The local natural-number definition starts at `K_0`; its two base
rows and successor theorem recover the virtual-seed presentation exactly.
No inverse-permutation or peak-statistic interpretation is asserted here.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined inverse-peak polynomial family. -/
def inversePeakEulerian : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C 2 * X + C (-2) * X ^ 2) * (inversePeakEulerian (n + 1)).derivative +
        (C 1 + C ((n : ℝ) + 2) * X) * inversePeakEulerian (n + 1) +
          X * inversePeakEulerian n

@[simp]
theorem inversePeakEulerian_zero : inversePeakEulerian 0 = 1 := rfl

@[simp]
theorem inversePeakEulerian_one : inversePeakEulerian 1 = 1 + X := rfl

/-- The exact recurrence after the virtual `K_{-1}=0` transition. -/
theorem inversePeakEulerian_recurrence (n : ℕ) :
    inversePeakEulerian (n + 2) =
      (C 2 * X + C (-2) * X ^ 2) * (inversePeakEulerian (n + 1)).derivative +
        (C 1 + C ((n : ℝ) + 2) * X) * inversePeakEulerian (n + 1) +
          X * inversePeakEulerian n := rfl

/-- The omitted virtual seed is exactly `K_{-1}=0`: substituting it into the
displayed `m=0` recurrence gives the checked linear base row. -/
theorem inversePeakEulerian_one_from_virtual_seed :
    inversePeakEulerian 1 =
      (C 2 * X + C (-2) * X ^ 2) * (inversePeakEulerian 0).derivative +
        (C 1 + X) * inversePeakEulerian 0 + X * 0 := by
  simp

private theorem inversePeakEulerian_affine_recurrence (n : ℕ) :
    inversePeakEulerian (n + 2) =
      (C 2 * X + C (-2) * X ^ 2) * (inversePeakEulerian (n + 1)).derivative +
        (C 1 + C ((n : ℝ) + 2) * X) * inversePeakEulerian (n + 1) +
          (C 1 * X) * inversePeakEulerian n := by
  simpa using inversePeakEulerian_recurrence n

/-- The first recurrence row after the linear base. -/
theorem inversePeakEulerian_two : inversePeakEulerian 2 = 1 + C 6 * X := by
  norm_num [inversePeakEulerian, map_ofNat]
  ring

/-- Coefficient recurrence for positive exponents. -/
theorem inversePeakEulerian_coeff_succ_succ (n k : ℕ) :
    (inversePeakEulerian (n + 2)).coeff (k + 1) =
      ((2 : ℝ) * (k + 1) + 1) * (inversePeakEulerian (n + 1)).coeff (k + 1) +
        ((n : ℝ) + 2 - 2 * k) * (inversePeakEulerian (n + 1)).coeff k +
          (inversePeakEulerian n).coeff k := by
  rw [inversePeakEulerian_recurrence, coeff_add,
    Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  rw [show X * inversePeakEulerian n = C 1 * (X * inversePeakEulerian n) by simp]
  simp only [coeff_C_mul, coeff_X_mul]
  ring

/-- Every row has constant coefficient one. -/
@[simp]
theorem inversePeakEulerian_coeff_zero :
    ∀ n : ℕ, (inversePeakEulerian n).coeff 0 = 1
  | 0 => by simp
  | 1 => by simp [coeff_add]
  | n + 2 => by
      have ih := inversePeakEulerian_coeff_zero (n + 1)
      rw [inversePeakEulerian_recurrence]
      simp_all

/-- Coefficients are positive through `(n+1)/2` and vanish above it. -/
theorem inversePeakEulerian_coeff_support :
    ∀ n : ℕ,
      (∀ k ≤ (n + 1) / 2, 0 < (inversePeakEulerian n).coeff k) ∧
        (∀ k > (n + 1) / 2, (inversePeakEulerian n).coeff k = 0) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · intro k hk
        have : k = 0 := by simpa using hk
        subst k
        simp
      · intro k hk
        simp [coeff_one, show k ≠ 0 by lia]
  | one =>
      constructor
      · intro k hk
        interval_cases k <;> norm_num [inversePeakEulerian, coeff_add, coeff_one, coeff_X]
      · intro k hk
        rw [inversePeakEulerian_one]
        simp [coeff_add, coeff_one, coeff_X,
          show k ≠ 0 by lia, show 1 ≠ k by lia]
  | more n ih0 ih1 =>
      constructor
      · intro k hk
        rcases k with _ | k
        · simp
        · rw [inversePeakEulerian_coeff_succ_succ]
          have hmul : (k + 1) * 2 ≤ n + 3 :=
            (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk
          have hkprev : k ≤ (n + 2) / 2 :=
            (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by lia)
          have hfactor : 0 < (n : ℝ) + 2 - 2 * k := by
            have hmulReal : (((k + 1) * 2 : ℕ) : ℝ) ≤ (n + 3 : ℕ) := by
              exact_mod_cast hmul
            push_cast at hmulReal
            linarith
          have hfirst :
              0 ≤ ((2 : ℝ) * (k + 1) + 1) *
                (inversePeakEulerian (n + 1)).coeff (k + 1) := by
            refine mul_nonneg (by positivity) ?_
            by_cases hsupp : k + 1 ≤ (n + 2) / 2
            · exact (ih1.1 (k + 1) hsupp).le
            · rw [ih1.2 (k + 1) (by lia)]
          have hmiddle :
              0 < ((n : ℝ) + 2 - 2 * k) *
                (inversePeakEulerian (n + 1)).coeff k :=
            mul_pos hfactor (ih1.1 k hkprev)
          have hlast : 0 ≤ (inversePeakEulerian n).coeff k := by
            by_cases hsupp : k ≤ (n + 1) / 2
            · exact (ih0.1 k hsupp).le
            · rw [ih0.2 k (by lia)]
          linarith
      · intro m hm
        rcases m with _ | k
        · simp at hm
        · rw [inversePeakEulerian_coeff_succ_succ]
          have hmul : n + 3 < (k + 1) * 2 :=
            (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hm
          have hprevDegree : (n + 2) / 2 ≤ (n + 3) / 2 :=
            Nat.div_le_div_right (by lia)
          have hk1 : (n + 2) / 2 < k + 1 := by lia
          rw [ih1.2 (k + 1) hk1]
          have hlag : (n + 1) / 2 < k := by
            apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
            lia
          rw [ih0.2 k hlag]
          by_cases hk : k ≤ (n + 2) / 2
          · have hkmul : k * 2 ≤ n + 2 :=
              (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk
            have heq : (n : ℝ) + 2 - 2 * k = 0 := by
              have heqNat : k * 2 = n + 2 := by lia
              have heqReal : ((k * 2 : ℕ) : ℝ) = (n + 2 : ℕ) := by
                exact_mod_cast heqNat
              push_cast at heqReal
              linarith
            rw [heq]
            ring
          · rw [ih1.2 k (by lia)]
            ring

/-- The inverse-peak row `n` has degree `(n+1)/2`. -/
@[simp]
theorem inversePeakEulerian_natDegree (n : ℕ) :
    (inversePeakEulerian n).natDegree = (n + 1) / 2 := by
  rcases inversePeakEulerian_coeff_support n with ⟨hpos, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => habove k hk)
    (hpos ((n + 1) / 2) le_rfl).ne'

/-- Coefficients are positive exactly on the degree support. -/
theorem inversePeakEulerian_coeff_pos_iff (n k : ℕ) :
    0 < (inversePeakEulerian n).coeff k ↔ k ≤ (n + 1) / 2 := by
  constructor
  · intro hpos
    by_contra hk
    rw [(inversePeakEulerian_coeff_support n).2 k (by lia)] at hpos
    linarith
  · exact (inversePeakEulerian_coeff_support n).1 k

/-- Every inverse-peak row has nonnegative coefficients. -/
theorem inversePeakEulerian_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (inversePeakEulerian n) := by
  intro k
  by_cases hk : k ≤ (n + 1) / 2
  · exact ((inversePeakEulerian_coeff_support n).1 k hk).le
  · rw [(inversePeakEulerian_coeff_support n).2 k (by lia)]

/-- Every inverse-peak row has positive leading coefficient. -/
theorem inversePeakEulerian_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (inversePeakEulerian n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, inversePeakEulerian_natDegree]
  exact (inversePeakEulerian_coeff_support n).1 ((n + 1) / 2) le_rfl

/-- Every real root is strictly negative. -/
theorem inversePeakEulerian_root_neg (n : ℕ) {r : ℝ}
    (hr : (inversePeakEulerian n).IsRoot r) : r < 0 := by
  have hpos := inversePeakEulerian_hasPosLeadingCoeff n
  have hmem : r ∈ (inversePeakEulerian n).roots := (mem_roots hpos.ne_zero).mpr hr
  have hrle := roots_nonpos_of_hasNonnegCoeffs
    (inversePeakEulerian_hasNonnegCoeffs n) r hmem
  apply lt_of_le_of_ne hrle
  intro hr0
  subst r
  rw [Polynomial.IsRoot.def] at hr
  have heval : eval 0 (inversePeakEulerian n) = 1 := by
    rw [← coeff_zero_eq_eval_zero, inversePeakEulerian_coeff_zero]
  simp_all

private theorem inversePeakEulerian_degree_step (n : ℕ) :
    (inversePeakEulerian (n + 1)).natDegree = (inversePeakEulerian n).natDegree ∨
      (inversePeakEulerian (n + 1)).natDegree = (inversePeakEulerian n).natDegree + 1 := by
  rw [inversePeakEulerian_natDegree, inversePeakEulerian_natDegree]
  rw [show n + 2 = (n + 1) + 1 by lia, Nat.succ_div]
  split_ifs <;> simp

private theorem half_two_mul_add_one (j : ℕ) : (2 * j + 1) / 2 = j := by
  calc
    (2 * j + 1) / 2 = (1 + 2 * j) / 2 := by congr 1; ring
    _ = 1 / 2 + j := Nat.add_mul_div_left 1 j (by decide)
    _ = j := by simp

private theorem half_two_mul_add_two (j : ℕ) : (2 * j + 2) / 2 = j + 1 := by
  calc
    (2 * j + 2) / 2 = (0 + 2 * (j + 1)) / 2 := by congr 1; ring
    _ = 0 / 2 + (j + 1) := Nat.add_mul_div_left 0 (j + 1) (by decide)
    _ = j + 1 := by simp

private theorem half_two_mul_add_three (j : ℕ) : (2 * j + 3) / 2 = j + 1 := by
  calc
    (2 * j + 3) / 2 = (1 + 2 * (j + 1)) / 2 := by congr 1; ring
    _ = 1 / 2 + (j + 1) := Nat.add_mul_div_left 1 (j + 1) (by decide)
    _ = j + 1 := by simp

private theorem inversePeakEulerian_base_prec :
    StrictInterl (inversePeakEulerian 0) (inversePeakEulerian 1) := by
  rw [inversePeakEulerian_zero]
  exact (interlaces_one_linear (p := inversePeakEulerian 1)
    (inversePeakEulerian_natDegree 1)).toStrictInterl

private theorem inversePeakEulerian_base_noCommon :
    ∀ r, (inversePeakEulerian 1).IsRoot r → ¬ (inversePeakEulerian 0).IsRoot r := by
  intro r _ hr0
  simp [Polynomial.IsRoot.def] at hr0

/-- Consecutive inverse-peak rows are in proper position and share no real
root. -/
theorem inversePeakEulerian_prec_and_noCommonRoot (n : ℕ) :
    StrictInterl (inversePeakEulerian n) (inversePeakEulerian (n + 1)) ∧
      ∀ r, (inversePeakEulerian (n + 1)).IsRoot r →
        ¬ (inversePeakEulerian n).IsRoot r := by
  apply strictInterl_and_noCommonRoot_of_quadratic_lag_degree_step
    (P := inversePeakEulerian) (a := 2) (b := 2) (c := 1)
    (Q := fun m => C 1 + C ((m : ℝ) + 2) * X)
  · norm_num
  · norm_num
  · norm_num
  · exact inversePeakEulerian_degree_step
  · intro m
    rw [inversePeakEulerian_natDegree]
    exact Nat.div_pos (by lia) (by decide)
  · exact inversePeakEulerian_hasPosLeadingCoeff
  · intro m r hr
    exact inversePeakEulerian_root_neg m hr
  · exact inversePeakEulerian_base_prec
  · exact inversePeakEulerian_base_noCommon
  · exact inversePeakEulerian_affine_recurrence

/-- Consecutive inverse-peak rows are in proper position. -/
theorem inversePeakEulerian_prec (n : ℕ) :
    StrictInterl (inversePeakEulerian n) (inversePeakEulerian (n + 1)) :=
  (inversePeakEulerian_prec_and_noCommonRoot n).1

/-- Consecutive inverse-peak rows have no common real root. -/
theorem inversePeakEulerian_noCommonRoot (n : ℕ) (r : ℝ)
    (hr : (inversePeakEulerian (n + 1)).IsRoot r) :
    ¬ (inversePeakEulerian n).IsRoot r :=
  (inversePeakEulerian_prec_and_noCommonRoot n).2 r hr

/-- Every inverse-peak row splits over the reals. -/
theorem inversePeakEulerian_splits (n : ℕ) : (inversePeakEulerian n).Splits :=
  (inversePeakEulerian_prec n).1.2

/-- Every inverse-peak row has simple real roots. -/
theorem inversePeakEulerian_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots (inversePeakEulerian n) :=
  ((inversePeakEulerian_prec n).hasSimpleRoots_of_no_common_root fun r hr =>
    inversePeakEulerian_noCommonRoot n r hr.2 hr.1).1

/-- On a degree-rise step, the preceding row strictly interlaces the next
row. -/
theorem inversePeakEulerian_interlaces_of_degree_succ (n : ℕ)
    (hdeg : (inversePeakEulerian n).natDegree + 1 =
      (inversePeakEulerian (n + 1)).natDegree) :
    Interlaces (inversePeakEulerian n) (inversePeakEulerian (n + 1)) :=
  (inversePeakEulerian_prec n).toInterlaces hdeg

/-- Odd-indexed transitions are same-degree proper-position steps.  The
`ListAlternates ss rs` orientation records that the earlier row owns the
leftmost root and the later row owns the rightmost root. -/
theorem inversePeakEulerian_odd_alternates (j : ℕ) :
    ∃ ss rs : List ℝ,
      ss.Pairwise (· ≤ ·) ∧ rs.Pairwise (· ≤ ·) ∧
        (↑ss : Multiset ℝ) = (inversePeakEulerian (2 * j + 1)).roots ∧
        (↑rs : Multiset ℝ) = (inversePeakEulerian (2 * j + 2)).roots ∧
        ListAlternates ss rs := by
  apply (inversePeakEulerian_prec (2 * j + 1)).exists_listAlternates_of_natDegree_eq
  rw [inversePeakEulerian_natDegree, inversePeakEulerian_natDegree,
    half_two_mul_add_two, half_two_mul_add_three]

/-- Even-indexed transitions are degree-rise strict interlacing steps. -/
theorem inversePeakEulerian_even_interlaces (j : ℕ) :
    Interlaces (inversePeakEulerian (2 * j))
      (inversePeakEulerian (2 * j + 1)) := by
  apply inversePeakEulerian_interlaces_of_degree_succ
  rw [inversePeakEulerian_natDegree, inversePeakEulerian_natDegree,
    half_two_mul_add_one, half_two_mul_add_two]

end RealRooted.Applications.OEIS
