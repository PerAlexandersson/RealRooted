import RealRooted.DerivativeRecurrence.AffineLagStrict

/-!
# Lower-reentrant-corner recurrence

We formalize the recurrence by the offset `n = h - 2`.  Thus row `n` below
is the height-`n+2` row from the source recurrence.  No polyomino or corner-
statistic interpretation is asserted here.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined lower-reentrant-corner family, indexed by `h - 2`. -/
def lowerReentrantCorner : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C 2
  | n + 2 =>
      C ((n : ℝ) + 3) * lowerReentrantCorner (n + 1) +
        (C ((n : ℝ) + 2) * X - C ((n : ℝ) + 1)) * lowerReentrantCorner n

@[simp]
theorem lowerReentrantCorner_zero : lowerReentrantCorner 0 = 1 := rfl

@[simp]
theorem lowerReentrantCorner_one : lowerReentrantCorner 1 = C 2 := rfl

/-- The exact offset-indexed recurrence. -/
theorem lowerReentrantCorner_recurrence (n : ℕ) :
    lowerReentrantCorner (n + 2) =
      C ((n : ℝ) + 3) * lowerReentrantCorner (n + 1) +
        (C ((n : ℝ) + 2) * X - C ((n : ℝ) + 1)) * lowerReentrantCorner n := rfl

/-- The height-indexed form of the recurrence, valid from height four. -/
theorem lowerReentrantCorner_height_recurrence (h : ℕ) (hh : 4 ≤ h) :
    lowerReentrantCorner (h - 2) =
      C ((h : ℝ) - 1) * lowerReentrantCorner (h - 3) +
        (C ((h : ℝ) - 2) * X - C ((h : ℝ) - 3)) *
          lowerReentrantCorner (h - 4) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hh
  have h2 : 4 + n - 2 = n + 2 := by lia
  have h3 : 4 + n - 3 = n + 1 := by lia
  have h4 : 4 + n - 4 = n := by lia
  have hc1 : ((4 + n : ℕ) : ℝ) - 1 = (n : ℝ) + 3 := by
    push_cast
    ring
  have hc2 : ((4 + n : ℕ) : ℝ) - 2 = (n : ℝ) + 2 := by
    push_cast
    ring
  have hc3 : ((4 + n : ℕ) : ℝ) - 3 = (n : ℝ) + 1 := by
    push_cast
    ring
  rw [h2, h3, h4]
  rw [hc1, hc2, hc3]
  exact lowerReentrantCorner_recurrence n

/-- The first nonconstant row. -/
theorem lowerReentrantCorner_two :
    lowerReentrantCorner 2 = C 5 + C 2 * X := by
  norm_num [lowerReentrantCorner, map_ofNat, ← C_mul]
  ring_nf

/-- Coefficient recurrence in every positive degree. -/
theorem lowerReentrantCorner_coeff_succ_succ (n k : ℕ) :
    (lowerReentrantCorner (n + 2)).coeff (k + 1) =
      ((n : ℝ) + 3) * (lowerReentrantCorner (n + 1)).coeff (k + 1) +
        ((n : ℝ) + 2) * (lowerReentrantCorner n).coeff k -
          ((n : ℝ) + 1) * (lowerReentrantCorner n).coeff (k + 1) := by
  rw [lowerReentrantCorner_recurrence]
  rw [show
    (C ((n : ℝ) + 2) * X - C ((n : ℝ) + 1)) * lowerReentrantCorner n =
      C ((n : ℝ) + 2) * (X * lowerReentrantCorner n) -
        C ((n : ℝ) + 1) * lowerReentrantCorner n by ring]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul]
  ring

/-- Constant coefficients satisfy the scalar part of the recurrence. -/
theorem lowerReentrantCorner_coeff_zero_succ_succ (n : ℕ) :
    (lowerReentrantCorner (n + 2)).coeff 0 =
      ((n : ℝ) + 3) * (lowerReentrantCorner (n + 1)).coeff 0 -
        ((n : ℝ) + 1) * (lowerReentrantCorner n).coeff 0 := by
  rw [lowerReentrantCorner_recurrence]
  simp
  ring

private theorem lowerReentrantCorner_coeff_nonneg_and_mono :
    ∀ n k : ℕ,
      0 ≤ (lowerReentrantCorner n).coeff k ∧
        (lowerReentrantCorner n).coeff k ≤
          (lowerReentrantCorner (n + 1)).coeff k := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [lowerReentrantCorner_zero, lowerReentrantCorner_one]
      by_cases hk : k = 0
      · subst k
        simp
      · simp [coeff_one, coeff_C, hk]
  | succ n ih =>
      intro k
      have hk := ih k
      constructor
      · exact hk.1.trans hk.2
      · rcases k with _ | k
        · rw [show n + 1 + 1 = n + 2 by lia,
            lowerReentrantCorner_coeff_zero_succ_succ]
          nlinarith
        · rw [show n + 1 + 1 = n + 2 by lia,
            lowerReentrantCorner_coeff_succ_succ]
          have hkPrev := ih k
          nlinarith

/-- Every coefficient is nonnegative. -/
theorem lowerReentrantCorner_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (lowerReentrantCorner n) :=
  fun k => (lowerReentrantCorner_coeff_nonneg_and_mono n k).1

/-- Coefficients increase weakly from one row to the next. -/
theorem lowerReentrantCorner_coeff_mono (n k : ℕ) :
    (lowerReentrantCorner n).coeff k ≤
      (lowerReentrantCorner (n + 1)).coeff k :=
  (lowerReentrantCorner_coeff_nonneg_and_mono n k).2

/-- Coefficients are positive through `n / 2` and vanish above it. -/
theorem lowerReentrantCorner_coeff_support :
    ∀ n : ℕ,
      (∀ k ≤ n / 2, 0 < (lowerReentrantCorner n).coeff k) ∧
        (∀ k > n / 2, (lowerReentrantCorner n).coeff k = 0) := by
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
        have : k = 0 := by simpa using hk
        subst k
        simp
      · intro k hk
        rw [lowerReentrantCorner_one]
        simp [coeff_C, show k ≠ 0 by lia]
  | more n ih0 ih1 =>
      constructor
      · intro k hk
        by_cases hold : k ≤ (n + 1) / 2
        · exact (ih1.1 k hold).trans_le (lowerReentrantCorner_coeff_mono (n + 1) k)
        · rcases k with _ | k
          · simp at hold
          · rw [lowerReentrantCorner_coeff_succ_succ]
            have htop : (k + 1) * 2 ≤ n + 2 :=
              (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk
            have hkPrev : k ≤ n / 2 :=
              (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by lia)
            have hshift := ih0.1 k hkPrev
            have hmono := lowerReentrantCorner_coeff_mono n (k + 1)
            have hnonneg :=
              (lowerReentrantCorner_hasNonnegCoeffs n) (k + 1)
            nlinarith
      · intro m hm
        rcases m with _ | k
        · simp at hm
        · rw [lowerReentrantCorner_coeff_succ_succ]
          have hmul : n + 2 < (k + 1) * 2 :=
            (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hm
          have hmPrev : (n + 1) / 2 < k + 1 := by
            apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
            lia
          have hmLag : n / 2 < k := by
            apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
            lia
          rw [ih1.2 (k + 1) hmPrev, ih0.2 k hmLag,
            ih0.2 (k + 1) (by lia)]
          ring

/-- The offset row `n` has degree `n / 2`. -/
@[simp]
theorem lowerReentrantCorner_natDegree (n : ℕ) :
    (lowerReentrantCorner n).natDegree = n / 2 := by
  rcases lowerReentrantCorner_coeff_support n with ⟨hpos, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => habove k hk)
    (hpos (n / 2) le_rfl).ne'

/-- Coefficients are positive exactly on the degree support. -/
theorem lowerReentrantCorner_coeff_pos_iff (n k : ℕ) :
    0 < (lowerReentrantCorner n).coeff k ↔ k ≤ n / 2 := by
  constructor
  · intro hpos
    by_contra hk
    rw [(lowerReentrantCorner_coeff_support n).2 k (by lia)] at hpos
    linarith
  · exact (lowerReentrantCorner_coeff_support n).1 k

/-- Every row has positive leading coefficient. -/
theorem lowerReentrantCorner_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (lowerReentrantCorner n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, lowerReentrantCorner_natDegree]
  exact (lowerReentrantCorner_coeff_support n).1 (n / 2) le_rfl

/-- Every real root is strictly negative. -/
theorem lowerReentrantCorner_root_neg (n : ℕ) {r : ℝ}
    (hr : (lowerReentrantCorner n).IsRoot r) : r < 0 := by
  have hpos := lowerReentrantCorner_hasPosLeadingCoeff n
  have hrle := isRoot_nonpos_of_hasNonnegCoeffs
    (lowerReentrantCorner_hasNonnegCoeffs n) hpos.ne_zero hr
  apply lt_of_le_of_ne hrle
  intro hr0
  subst r
  rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero] at hr
  have hcoeff := (lowerReentrantCorner_coeff_support n).1 0 (by simp)
  linarith

private theorem lowerReentrantCorner_degree_step (n : ℕ) :
    (lowerReentrantCorner (n + 1)).natDegree =
        (lowerReentrantCorner n).natDegree ∨
      (lowerReentrantCorner (n + 1)).natDegree =
        (lowerReentrantCorner n).natDegree + 1 := by
  rw [lowerReentrantCorner_natDegree, lowerReentrantCorner_natDegree,
    Nat.succ_div]
  split_ifs <;> simp

private theorem lowerReentrantCorner_shifted_recurrence (n : ℕ) :
    lowerReentrantCorner (n + 3) =
      C ((n : ℝ) + 4) * lowerReentrantCorner (n + 2) +
        (C ((n : ℝ) + 3) * X - C ((n : ℝ) + 2)) *
          lowerReentrantCorner (n + 1) := by
  have hc4 : (((n + 1 : ℕ) : ℝ) + 3) = (n : ℝ) + 4 := by
    push_cast
    ring
  have hc3 : (((n + 1 : ℕ) : ℝ) + 2) = (n : ℝ) + 3 := by
    push_cast
    ring
  have hc2 : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
    push_cast
    ring
  simpa only [Nat.add_assoc, hc4, hc3, hc2] using
    lowerReentrantCorner_recurrence (n + 1)

private theorem lowerReentrantCorner_one_prec_two :
    Prec (lowerReentrantCorner 1) (lowerReentrantCorner 2) := by
  have hlinear : (lowerReentrantCorner 2).natDegree = 1 := by simp
  have hone : Prec (1 : ℝ[X]) (lowerReentrantCorner 2) :=
    (interlaces_one_linear hlinear).toPrec
  simpa using hone.C_mul_left (a := 2) (by norm_num)

private theorem lowerReentrantCorner_one_two_noCommon :
    ∀ r, (lowerReentrantCorner 2).IsRoot r →
      ¬ (lowerReentrantCorner 1).IsRoot r := by
  intro r _ hr
  simp [Polynomial.IsRoot.def] at hr

private theorem lowerReentrantCorner_shifted_prec_and_noCommonRoot (n : ℕ) :
    Prec (lowerReentrantCorner (n + 1)) (lowerReentrantCorner (n + 2)) ∧
      ∀ r, (lowerReentrantCorner (n + 2)).IsRoot r →
        ¬ (lowerReentrantCorner (n + 1)).IsRoot r := by
  apply prec_and_noCommonRoot_of_affine_lag_degree_step
    (P := fun m => lowerReentrantCorner (m + 1))
    (a := fun m => (m : ℝ) + 3) (b := fun m => (m : ℝ) + 2)
    (A := fun m => C ((m : ℝ) + 4))
  · intro m
    positivity
  · intro m
    positivity
  · intro m
    simpa [Nat.add_assoc] using lowerReentrantCorner_degree_step (m + 1)
  · intro m
    rw [lowerReentrantCorner_natDegree]
    exact Nat.div_pos (by lia) (by decide)
  · intro m
    exact lowerReentrantCorner_hasNonnegCoeffs (m + 1)
  · intro m
    exact lowerReentrantCorner_hasPosLeadingCoeff (m + 1)
  · exact lowerReentrantCorner_one_prec_two
  · exact lowerReentrantCorner_one_two_noCommon
  · exact lowerReentrantCorner_shifted_recurrence

private theorem lowerReentrantCorner_zero_prec_one :
    Prec (lowerReentrantCorner 0) (lowerReentrantCorner 1) := by
  have hone : Prec (1 : ℝ[X]) 1 :=
    prec_refl (by simp) (by simp)
  simpa using hone.C_mul_right (a := 2) (by norm_num)

/-- Consecutive rows are in proper position. -/
theorem lowerReentrantCorner_prec (n : ℕ) :
    Prec (lowerReentrantCorner n) (lowerReentrantCorner (n + 1)) := by
  rcases n with _ | n
  · exact lowerReentrantCorner_zero_prec_one
  · simpa [Nat.add_assoc] using
      (lowerReentrantCorner_shifted_prec_and_noCommonRoot n).1

/-- Consecutive rows have no common real root. -/
theorem lowerReentrantCorner_noCommonRoot (n : ℕ) (r : ℝ)
    (hr : (lowerReentrantCorner (n + 1)).IsRoot r) :
    ¬ (lowerReentrantCorner n).IsRoot r := by
  rcases n with _ | n
  · intro hr0
    simp [Polynomial.IsRoot.def] at hr0
  · exact (lowerReentrantCorner_shifted_prec_and_noCommonRoot n).2 r (by simpa using hr)

/-- Every row splits over the reals. -/
theorem lowerReentrantCorner_splits (n : ℕ) :
    (lowerReentrantCorner n).Splits :=
  (lowerReentrantCorner_prec n).1.2

/-- Every row has simple real roots. -/
theorem lowerReentrantCorner_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots (lowerReentrantCorner n) :=
  ((lowerReentrantCorner_prec n).hasSimpleRoots_of_no_common_root fun r hr =>
    lowerReentrantCorner_noCommonRoot n r hr.2 hr.1).1

private theorem half_two_mul (j : ℕ) : (2 * j) / 2 = j := by
  calc
    (2 * j) / 2 = (0 + 2 * j) / 2 := by simp
    _ = 0 / 2 + j := Nat.add_mul_div_left 0 j (by decide)
    _ = j := by simp

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

/-- Even-indexed transitions are same-degree proper-position steps.  The
`ListAlternates ss rs` orientation records that the earlier row owns the
leftmost root and the later row owns the rightmost root. -/
theorem lowerReentrantCorner_even_alternates (j : ℕ) :
    ∃ ss rs : List ℝ,
      ss.Pairwise (· ≤ ·) ∧ rs.Pairwise (· ≤ ·) ∧
        (↑ss : Multiset ℝ) = (lowerReentrantCorner (2 * j)).roots ∧
        (↑rs : Multiset ℝ) = (lowerReentrantCorner (2 * j + 1)).roots ∧
        ListAlternates ss rs := by
  apply (lowerReentrantCorner_prec (2 * j)).exists_listAlternates_of_natDegree_eq
  rw [lowerReentrantCorner_natDegree, lowerReentrantCorner_natDegree,
    half_two_mul, half_two_mul_add_one]

/-- Odd-indexed transitions are degree-rise strict interlacing steps. -/
theorem lowerReentrantCorner_odd_interlaces (j : ℕ) :
    Interlaces (lowerReentrantCorner (2 * j + 1))
      (lowerReentrantCorner (2 * j + 2)) := by
  apply (lowerReentrantCorner_prec (2 * j + 1)).toInterlaces
  rw [lowerReentrantCorner_natDegree, lowerReentrantCorner_natDegree,
    half_two_mul_add_one, half_two_mul_add_two]

end RealRooted.Applications.OEIS
