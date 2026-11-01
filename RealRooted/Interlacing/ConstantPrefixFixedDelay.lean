module

public import RealRooted.Interlacing.VariableDelay
import RealRooted.PosCombo.Degree
import RealRooted.QuadraticInterlacingClosure

/-!
# Constant-prefix fixed-delay recurrences

This module adapts a recurrence stated after a finite constant prefix to the
successor-indexed fixed-delay API.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A positive constant prefix and a tail recurrence can be rewritten as one
successor recurrence, with zero delayed weights along the prefix. -/
private theorem exists_successor_recurrence_of_constant_prefix_fixed_delay
    (P : ℕ → ℝ[X]) (c a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hc : ∀ i, i < L → 0 < c i) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n)
    (hprefix : ∀ i, i < L → P i = C (c i))
    (hrec : ∀ n,
      P (n + L) = C (a n) * P (n + L - 1) + C (b n) * X * P n) :
    ∃ α β : ℕ → ℝ,
      (∀ m, 0 < α m) ∧ (∀ m, 0 ≤ β m) ∧
        ∀ n,
          P (n + 1) =
            C (α (n + 1)) * P n + C (β (n + 1)) * X * P (n + 1 - L) := by
  let α : ℕ → ℝ := fun m ↦ if m < L then c m / c (m - 1) else a (m - L)
  let β : ℕ → ℝ := fun m ↦ if m < L then 0 else b (m - L)
  refine ⟨α, β, ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m < L
    · simp only [α, ite_eq_left hm]
      exact div_pos (hc m hm) (hc (m - 1) (by lia))
    · simp only [α, ite_eq_right hm]
      exact ha (m - L)
  · intro m
    by_cases hm : m < L
    · simp [β, hm]
    · simpa [β, hm] using hb (m - L)
  · intro n
    by_cases hn : n + 1 < L
    · rw [hprefix (n + 1) hn, hprefix n (by lia)]
      simp only [α, β, ite_eq_left hn, C_0, zero_mul, add_zero,
        Nat.add_sub_cancel, ← C_mul]
      congr 1
      field_simp [ne_of_gt (hc n (by lia))]
    · have hLn : L ≤ n + 1 := by lia
      simpa only [α, β, ite_eq_right hn, Nat.sub_add_cancel hLn,
        Nat.add_sub_cancel] using hrec (n + 1 - L)

/-- Every row of a positive constant-prefix fixed-delay recurrence has
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_constant_prefix_fixed_delay_recurrence
    (P : ℕ → ℝ[X]) (c a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hc : ∀ i, i < L → 0 < c i) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n)
    (hprefix : ∀ i, i < L → P i = C (c i))
    (hrec : ∀ n,
      P (n + L) = C (a n) * P (n + L - 1) + C (b n) * X * P n)
    (n : ℕ) :
    HasNonnegCoeffs (P n) := by
  obtain ⟨α, β, hα, hβ, hsuccessor⟩ :=
    exists_successor_recurrence_of_constant_prefix_fixed_delay
      P c a b L hL hc ha hb hprefix hrec
  have hc0 := hc 0 (by lia)
  let Q : ℕ → ℝ[X] := fun m ↦ C (c 0)⁻¹ * P m
  have hQ0 : Q 0 = 1 := by
    dsimp only [Q]
    rw [hprefix 0 (by lia), ← C_mul]
    simp [hc0.ne']
  have hQrec : ∀ m,
      Q (m + 1) =
        C (α (m + 1)) * Q m + C (β (m + 1)) * X * Q (m + 1 - L) := by
    intro m
    dsimp only [Q]
    rw [hsuccessor m]
    ring
  have hQ := hasNonnegCoeffs_of_scaled_fixedDelay_recurrence
    Q α β L hL (fun m ↦ (hα m).le) hβ hQ0 hQrec n
  have hscaled := hasNonnegCoeffs_C_mul hc0.le hQ
  simpa [Q, ← mul_assoc, ← C_mul, hc0.ne'] using hscaled

/-- Rows at distance at most `L` in a positive constant-prefix fixed-delay
recurrence are in directed weak interlacing position. -/
theorem strictInterl_of_constant_prefix_fixed_delay_recurrence
    (P : ℕ → ℝ[X]) (c a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hc : ∀ i, i < L → 0 < c i) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n)
    (hprefix : ∀ i, i < L → P i = C (c i))
    (hrec : ∀ n,
      P (n + L) = C (a n) * P (n + L - 1) + C (b n) * X * P n)
    {A B : ℕ} (hAB : A ≤ B) (hBA : B ≤ A + L) :
    StrictInterl (P A) (P B) := by
  obtain ⟨α, β, hα, hβ, hsuccessor⟩ :=
    exists_successor_recurrence_of_constant_prefix_fixed_delay
      P c a b L hL hc ha hb hprefix hrec
  have hc0 := hc 0 (by lia)
  let Q : ℕ → ℝ[X] := fun m ↦ C (c 0)⁻¹ * P m
  have hQ0 : Q 0 = 1 := by
    dsimp only [Q]
    rw [hprefix 0 (by lia), ← C_mul]
    simp [hc0.ne']
  have hQrec : ∀ m,
      Q (m + 1) =
        C (α (m + 1)) * Q m + C (β (m + 1)) * X * Q (m + 1 - L) := by
    intro m
    dsimp only [Q]
    rw [hsuccessor m]
    ring
  have hinterl := strictInterl_of_scaled_fixedDelay_recurrence
    Q α β L hL hα hβ hQ0 hQrec hAB hBA
  have hscaled := (hinterl.C_mul_left hc0.ne').C_mul_right hc0.ne'
  simpa [Q, ← mul_assoc, ← C_mul, hc0.ne'] using hscaled

/-- Every row of a positive constant-prefix fixed-delay recurrence has a
strictly positive constant coefficient. -/
theorem coeff_zero_pos_of_constant_prefix_fixed_delay_recurrence
    (P : ℕ → ℝ[X]) (c a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hc : ∀ i, i < L → 0 < c i) (ha : ∀ n, 0 < a n)
    (hprefix : ∀ i, i < L → P i = C (c i))
    (hrec : ∀ n,
      P (n + L) = C (a n) * P (n + L - 1) + C (b n) * X * P n)
    (n : ℕ) :
    0 < (P n).coeff 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < L
      · simp [hprefix n hn, hc n hn]
      · have hLn : L ≤ n := by lia
        have hn0 : 0 < n := by lia
        have hidx : n - L + L - 1 = n - 1 := by lia
        rw [← Nat.sub_add_cancel hLn, hrec (n - L)]
        simpa [Polynomial.coeff_zero_eq_eval_zero, hidx] using
          mul_pos (ha (n - L)) (ih (n - 1) (by lia))

/-- Every root of every row of a positive constant-prefix fixed-delay
recurrence is strictly negative; constant rows are allowed. -/
theorem roots_neg_of_constant_prefix_fixed_delay_recurrence
    (P : ℕ → ℝ[X]) (c a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hc : ∀ i, i < L → 0 < c i) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n)
    (hprefix : ∀ i, i < L → P i = C (c i))
    (hrec : ∀ n,
      P (n + L) = C (a n) * P (n + L - 1) + C (b n) * X * P n)
    (n : ℕ) :
    ∀ r ∈ (P n).roots, r < 0 := by
  apply roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
  · exact hasNonnegCoeffs_of_constant_prefix_fixed_delay_recurrence
      P c a b L hL hc ha hb hprefix hrec n
  · exact (coeff_zero_pos_of_constant_prefix_fixed_delay_recurrence
      P c a b L hL hc ha hprefix hrec n).ne'

/-- If every delayed weight is positive, row `n` has degree `n / L`. -/
theorem natDegree_of_constant_prefix_fixed_delay_recurrence
    (P : ℕ → ℝ[X]) (c a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hc : ∀ i, i < L → 0 < c i) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hprefix : ∀ i, i < L → P i = C (c i))
    (hrec : ∀ n,
      P (n + L) = C (a n) * P (n + L - 1) + C (b n) * X * P n)
    (n : ℕ) :
    (P n).natDegree = n / L := by
  have hnonneg : ∀ m, HasNonnegCoeffs (P m) := fun m ↦
    hasNonnegCoeffs_of_constant_prefix_fixed_delay_recurrence
      P c a b L hL hc ha (fun k ↦ (hb k).le) hprefix hrec m
  have hne : ∀ m, P m ≠ 0 := fun m ↦
    (strictInterl_of_constant_prefix_fixed_delay_recurrence
      P c a b L hL hc ha (fun k ↦ (hb k).le) hprefix hrec
      (A := m) (B := m) le_rfl (by lia)).1.1
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < L
      · rw [hprefix n hn]
        simp [Nat.div_eq_of_lt hn]
      · have hLn : L ≤ n := by lia
        have hn0 : 0 < n := by lia
        let k := n - L
        have hn_eq : n = k + L := (Nat.sub_add_cancel hLn).symm
        have hpred : (P (n - 1)).natDegree ≤ (X * P k).natDegree := by
          rw [ih (n - 1) (by lia), natDegree_mul X_ne_zero (hne k), natDegree_X, ih k]
          · calc
              (n - 1) / L ≤ n / L := by
                simpa [Nat.pred_eq_sub_one] using
                  (Nat.div_le_div_right (c := L) (Nat.pred_le n))
              _ = k / L + 1 := by rw [hn_eq, Nat.add_div_right k (by lia)]
              _ = 1 + k / L := Nat.add_comm _ _
          · lia
        rw [hn_eq, hrec k, show k + L - 1 = n - 1 by lia]
        rw [mul_assoc (C (b k)) X (P k)]
        rw [natDegree_pos_combo_eq_right_of_natDegree_le hpred
          ((hnonneg (n - 1)).pos_leadingCoeff (hne (n - 1)))
          ((hasNonnegCoeffs_X.mul (hnonneg k)).pos_leadingCoeff
            (mul_ne_zero X_ne_zero (hne k))) (ha k) (hb k)]
        rw [natDegree_mul X_ne_zero (hne k), natDegree_X, ih k]
        · rw [Nat.add_div_right k (by lia)]
          exact Nat.add_comm _ _
        · lia

end RealRooted
