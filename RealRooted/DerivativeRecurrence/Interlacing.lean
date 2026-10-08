import RealRooted.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import RealRooted.ThreeTermRecurrence.Interlacing

/-!
# Interlacing for first-order derivative recurrences

Rows of `P (n + 1) = A n * (P n)' + B n * P n` with degrees `D₀ + n` and positive
leading coefficients interlace as soon as the first two rows do and `A n ≤ 0` at
the roots of `P n`.  Each step is the weak-sign Liu–Wang step
`strictInterl_of_interlaces_evalCoeff_nonpos` applied to `f = P n` and its
derivative `g = (P n)'`, which interlaces `f` because `f` is real-rooted.

The root-sign condition holds in particular when `A n ≤ 0` everywhere
(`derivRec_interlaces_of_eval_nonpos`), or when `A n ≤ 0` on `(-∞, 0]` and the
rows have nonnegative coefficients (`derivRec_interlaces_of_nonnegCoeffs`);
`derivRec_hasNonnegCoeffs` gives the latter when `A n` and `B n` have
nonnegative coefficients.
-/

open Polynomial

namespace RealRooted

/-- The derivative of a real-rooted polynomial of positive degree with positive
leading coefficient interlaces it. -/
theorem derivative_interlaces_of_pos {f : ℝ[X]} (hf : f.Splits) (hpos : 0 < f.leadingCoeff)
    (hdeg : 1 ≤ f.natDegree) : Interlaces f.derivative f := by
  rcases hdeg.lt_or_eq with hdeg | hdeg
  · exact derivative_interlaces_of_natDegree_ne_zero hf (by lia)
  · refine interlaces_of_natDegree_eq_zero_of_natDegree_eq_one ?_ ?_ hdeg.symm
    · exact leadingCoeff_ne_zero.mp
        (HasPosLeadingCoeff.derivative hpos (by lia)).ne'
    · exact Nat.le_zero.mp ((natDegree_derivative_le f).trans (by lia))

variable {P A B : ℕ → ℝ[X]} {D₀ : ℕ}

/-- One step: a real-rooted row of positive degree interlaces the next row. -/
theorem derivRec_interlaces_step (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (n : ℕ) (hA : ∀ r, (P n).IsRoot r → (A n).eval r ≤ 0) (hs : (P n).Splits)
    (hn : 1 ≤ D₀ + n) : Interlaces (P n) (P (n + 1)) := by
  have hF : P (n + 1) = B n * P n + A n * (P n).derivative := by
    rw [hrec n, add_comm]
  have hInter : Interlaces (P n).derivative (P n) :=
    derivative_interlaces_of_pos hs (hpos n) (by rw [hdeg]; lia)
  have hprec : StrictInterl (P n) (B n * P n + A n * (P n).derivative) :=
    strictInterl_of_interlaces_evalCoeff_nonpos hInter
      (HasPosLeadingCoeff.derivative (hpos n) (by rw [hdeg]; lia))
      (by rw [← hF]; exact hpos (n + 1))
      (by rw [← hF, hdeg, hdeg]; lia) (by rw [← hF, hdeg, hdeg]; lia) hA
  rw [← hF] at hprec
  exact hprec.toInterlaces (by rw [hdeg, hdeg]; lia)

theorem derivRec_interlaces (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n r, (P n).IsRoot r → (A n).eval r ≤ 0)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  induction n with
  | zero => exact h01
  | succ n ih =>
      exact derivRec_interlaces_step hrec hdeg hpos (n + 1) (hA (n + 1)) ih.1.2 (by lia)

/-- Starting from a real-rooted row of positive degree, no base interlacing is
needed. -/
theorem derivRec_interlaces_of_splits
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hD : 1 ≤ D₀) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n r, (P n).IsRoot r → (A n).eval r ≤ 0) (h0 : (P 0).Splits) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  induction n with
  | zero => exact derivRec_interlaces_step hrec hdeg hpos 0 (hA 0) h0 (by lia)
  | succ n ih =>
      exact derivRec_interlaces_step hrec hdeg hpos (n + 1) (hA (n + 1)) ih.1.2 (by lia)

theorem derivRec_interlaces_of_splits_of_eval_nonpos
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hD : 1 ≤ D₀) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n r, (A n).eval r ≤ 0) (h0 : (P 0).Splits) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_splits hrec hdeg hD hpos (fun n r _ => hA n r) h0 n

theorem derivRec_interlaces_of_splits_of_nonnegCoeffs
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hD : 1 ≤ D₀) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (hA : ∀ n r, r ≤ 0 → (A n).eval r ≤ 0)
    (h0 : (P 0).Splits) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  refine derivRec_interlaces_of_splits hrec hdeg hD hpos (fun n r hr => hA n r ?_) h0 n
  have hne : P n ≠ 0 := leadingCoeff_ne_zero.mp (hpos n).ne'
  exact roots_nonpos_of_hasNonnegCoeffs (hnn n) r ((mem_roots hne).mpr hr)

theorem derivRec_interlaces_of_eval_nonpos
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n r, (A n).eval r ≤ 0) (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces hrec hdeg hpos (fun n r _ => hA n r) h01 n

theorem derivRec_interlaces_of_nonnegCoeffs
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (P n)) (hA : ∀ n r, r ≤ 0 → (A n).eval r ≤ 0)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  refine derivRec_interlaces hrec hdeg hpos (fun n r hr => hA n r ?_) h01 n
  have hne : P n ≠ 0 := leadingCoeff_ne_zero.mp (hpos n).ne'
  exact roots_nonpos_of_hasNonnegCoeffs (hnn n) r ((mem_roots hne).mpr hr)

/-- Rows of a derivative recurrence with nonnegative coefficients. -/
theorem derivRec_hasNonnegCoeffs (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hA : ∀ n, HasNonnegCoeffs (A n)) (hB : ∀ n, HasNonnegCoeffs (B n))
    (h0 : HasNonnegCoeffs (P 0)) : ∀ n, HasNonnegCoeffs (P n)
  | 0 => h0
  | n + 1 => by
      have ih := derivRec_hasNonnegCoeffs hrec hA hB h0 n
      rw [hrec n]
      exact ((hA n).mul ih.derivative).add ((hB n).mul ih)

/-- Rows of a derivative recurrence with nonnegative coefficients, from
nonnegative multipliers: since
`coeff_k (A P' + B P) = ∑_{i + j = k + 1} (A_i j + B_{i-1}) p_j`, it suffices that
`A₀ ≥ 0` and `A_{i+1} j + B_i ≥ 0` for every `j` up to the degree bound. -/
theorem derivRec_hasNonnegCoeffs_of_mult {d : ℕ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree ≤ D₀ + d * n) (hA0 : ∀ n, 0 ≤ (A n).coeff 0)
    (hmult : ∀ n i (j : ℕ), j ≤ D₀ + d * n → 0 ≤ (A n).coeff (i + 1) * j + (B n).coeff i)
    (h0 : HasNonnegCoeffs (P 0)) : ∀ n, HasNonnegCoeffs (P n)
  | 0 => h0
  | n + 1 => by
      have ih := derivRec_hasNonnegCoeffs_of_mult hrec hdeg hA0 hmult h0 n
      intro k
      have hX : X * P (n + 1) = A n * (X * (P n).derivative) + (X * B n) * P n := by
        rw [hrec n]; ring
      have hk : (P (n + 1)).coeff k = (X * P (n + 1)).coeff (k + 1) := by
        rw [coeff_X_mul]
      rw [hk, hX, coeff_add, coeff_mul, coeff_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_nonneg fun x _ => ?_
      rw [coeff_X_mul_derivative]
      rcases x with ⟨i, j⟩
      rcases i with _ | i
      · rw [coeff_X_mul_zero, zero_mul, add_zero]
        exact mul_nonneg (hA0 n) (mul_nonneg (Nat.cast_nonneg j) (ih j))
      · rw [coeff_X_mul]
        by_cases hj : j ≤ D₀ + d * n
        · nlinarith [mul_nonneg (hmult n i j hj) (ih j)]
        · rw [coeff_eq_zero_of_natDegree_lt ((hdeg n).trans_lt (by lia))]
          ring_nf
          rfl

end RealRooted

/-!
## Nonnegative coefficients for derivative-lag recurrences

Rows of `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` have nonnegative
coefficients when the first two rows and the multipliers `W n` do, and the multipliers
`U n`, `V n` satisfy the coefficientwise condition of `derivRec_hasNonnegCoeffs_of_mult`
for the row `P (n + 1)`.  Nonnegative coefficients give roots in `(-∞, 0]`, which is the
root-sign input of the derivative-lag Liu–Wang step.
-/

open Polynomial

namespace RealRooted

variable {P U V W : ℕ → ℝ[X]} {D₀ : ℕ}

/-- One step: `U * Q + V * Q'` has nonnegative coefficients when `Q` does and
`coeff_k (U Q + V Q') = ∑_{i + j = k + 1} (V_i j + U_{i-1}) q_j` has nonnegative terms
for every `j` up to a degree bound for `Q`. -/
theorem hasNonnegCoeffs_mul_add_mul_derivative {U V Q : ℝ[X]} {N : ℕ}
    (hdeg : Q.natDegree ≤ N) (hV0 : 0 ≤ V.coeff 0)
    (hmult : ∀ i (j : ℕ), j ≤ N → 0 ≤ V.coeff (i + 1) * j + U.coeff i)
    (hQ : HasNonnegCoeffs Q) : HasNonnegCoeffs (U * Q + V * Q.derivative) := by
  intro k
  have hX : X * (U * Q + V * Q.derivative) = V * (X * Q.derivative) + (X * U) * Q := by
    ring
  have hk : (U * Q + V * Q.derivative).coeff k
      = (X * (U * Q + V * Q.derivative)).coeff (k + 1) := by
    rw [coeff_X_mul]
  rw [hk, hX, coeff_add, coeff_mul, coeff_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun x _ => ?_
  rw [coeff_X_mul_derivative]
  rcases x with ⟨i, j⟩
  rcases i with _ | i
  · rw [coeff_X_mul_zero, zero_mul, add_zero]
    exact mul_nonneg hV0 (mul_nonneg (Nat.cast_nonneg j) (hQ j))
  · rw [coeff_X_mul]
    by_cases hj : j ≤ N
    · nlinarith [mul_nonneg (hmult i j hj) (hQ j)]
    · rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by lia))]
      ring_nf
      rfl

/-- Rows of a derivative-lag recurrence with nonnegative coefficients, from nonnegative
multipliers.  The multiplier condition `hmult` only involves `j ≤ D₀ + d * (n + 1)`, the
degree bound of the row `P (n + 1)` that `U n` and `V n` act on. -/
theorem derivLag_hasNonnegCoeffs_of_mult {d : ℕ}
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hdeg : ∀ n, (P n).natDegree ≤ D₀ + d * n) (hV0 : ∀ n, 0 ≤ (V n).coeff 0)
    (hmult : ∀ n i (j : ℕ), j ≤ D₀ + d * (n + 1) →
      0 ≤ (V n).coeff (i + 1) * j + (U n).coeff i)
    (hW : ∀ n, HasNonnegCoeffs (W n)) (h0 : HasNonnegCoeffs (P 0))
    (h1 : HasNonnegCoeffs (P 1)) : ∀ n, HasNonnegCoeffs (P n) := by
  have key : ∀ n, HasNonnegCoeffs (P n) ∧ HasNonnegCoeffs (P (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec n]
      exact (hasNonnegCoeffs_mul_add_mul_derivative (hdeg (n + 1)) (hV0 n) (hmult n) ih.2).add
        ((hW n).mul ih.1)
  exact fun n => (key n).1

/-- Rows of `P (n + 1) = A n * (P n).derivative` split when the multipliers and the first row
do, since differentiation preserves splitting over `ℝ`. -/
theorem derivProduct_splits {P A : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative) (hA : ∀ n, (A n).Splits)
    (h0 : (P 0).Splits) (n : ℕ) : (P n).Splits := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hrec]
    refine (hA n).mul ?_
    rcases eq_zero_or_splits_derivative (Or.inr ih) with h | h
    · simp [h]
    · exact h

/-!
## Degrees when the top terms cancel

For `F = A * f' + B * f` with `deg A ≤ m + 1`, `deg B ≤ m` and `d = deg f`, the coefficient of
`X ^ (d + m)` in `F` is `t * lc f`, where `t = A_{m+1} d + B_m`. When `t = 0` the top terms cancel,
and the coefficient of `X ^ (d + m - 1)` is `-A_{m+1} c + (A_m d + B_{m-1}) lc f`, where
`c = f.coeff (d - 1)`. It is positive when `f` has nonnegative coefficients, `A_{m+1} ≤ 0` and
`A_m d + B_{m-1} > 0`.

Example: `A n = X - X ^ 3`, `B n = 1 + 2 X + n X ^ 2` (OEIS A008970) cancels at every step.
`A n = 2 X - 2 X ^ 2`, `B n = 2 + n X` (A008303) cancels at every other step (half growth).
The proof was found by Aristotle (Harmonic) and ported here.
-/

private theorem natDegree_eq_and_leadingCoeff_pos_of_coeff_pos {Q : ℝ[X]} {N : ℕ}
    (h : Q.natDegree ≤ N) (hc : 0 < Q.coeff N) : Q.natDegree = N ∧ 0 < Q.leadingCoeff := by
  have hN : Q.natDegree = N := natDegree_eq_of_le_of_coeff_ne_zero h hc.ne'
  exact ⟨hN, by rw [leadingCoeff, hN]; exact hc⟩

/-- One step of a first-order derivative recurrence whose top terms either grow
(`A_{m+1} d + B_m > 0`, degree `d + m`) or cancel exactly (degree `d + m - 1`), for `f` with
nonnegative coefficients. -/
theorem derivRec_natDegree_eq_and_leadingCoeff_pos_step_of_cancel {f A B : ℝ[X]} {d d' m : ℕ}
    (hm : 1 ≤ m) (hA : A.natDegree ≤ m + 1) (hB : B.natDegree ≤ m)
    (hnn : HasNonnegCoeffs f) (hd : f.natDegree = d) (hl : 0 < f.leadingCoeff)
    (hstep : (0 < A.coeff (m + 1) * d + B.coeff m ∧ d' = d + m) ∨
      (A.coeff (m + 1) * d + B.coeff m = 0 ∧ d' = d + m - 1 ∧ A.coeff (m + 1) ≤ 0 ∧
        0 < A.coeff m * d + B.coeff (m - 1))) :
    (A * derivative f + B * f).natDegree = d' ∧ 0 < (A * derivative f + B * f).leadingCoeff := by
  have hlc : f.coeff d = f.leadingCoeff := by rw [leadingCoeff, hd]
  rcases Nat.eq_zero_or_pos d with hD0 | hDpos
  · -- a constant row: the derivative vanishes
    subst hD0
    have hPC : f = C f.leadingCoeff := by
      rw [← hlc]; exact eq_C_of_natDegree_eq_zero hd
    rw [hPC, derivative_C, mul_zero, zero_add]
    have hle : (B * C f.leadingCoeff).natDegree ≤ B.natDegree :=
      natDegree_mul_le.trans (by simp)
    rcases hstep with ⟨ht, hDn⟩ | ⟨ht, hDn, -, hsec⟩
    · simp only [Nat.cast_zero, mul_zero, zero_add] at ht
      rw [hDn, zero_add]
      refine natDegree_eq_and_leadingCoeff_pos_of_coeff_pos (hle.trans hB) ?_
      rw [coeff_mul_C]; exact mul_pos ht hl
    · simp only [Nat.cast_zero, mul_zero, zero_add] at ht hsec
      rw [hDn, zero_add]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
      simp only [Nat.add_sub_cancel] at hsec ⊢
      refine natDegree_eq_and_leadingCoeff_pos_of_coeff_pos ?_ ?_
      · rw [natDegree_le_iff_coeff_eq_zero]
        intro j hj
        rw [coeff_mul_C]
        rcases (show j = k + 1 ∨ k + 1 < j by lia) with rfl | hj'
        · rw [ht, zero_mul]
        · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hB hj'), zero_mul]
      · rw [coeff_mul_C]; exact mul_pos hsec hl
  · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by lia⟩
    have hPd : f.natDegree ≤ e + 1 := (le_of_eq (hd.trans he))
    have hP' : (derivative f).natDegree ≤ e :=
      (natDegree_derivative_le _).trans (by lia)
    have hleQ : (A * derivative f + B * f).natDegree ≤ m + 1 + e := by
      refine natDegree_add_le_of_degree_le ?_ ?_
      · exact natDegree_mul_le.trans (by lia)
      · exact natDegree_mul_le.trans (by lia)
    have htop : (A * derivative f + B * f).coeff (m + 1 + e) =
        (A.coeff (m + 1) * d + B.coeff m) * f.leadingCoeff := by
      rw [coeff_add, coeff_mul_add_eq_of_natDegree_le hA hP',
        show m + 1 + e = m + (e + 1) by lia, coeff_mul_add_eq_of_natDegree_le hB hPd,
        coeff_derivative, ← he, hlc, he]
      push_cast; ring
    rcases hstep with ⟨ht, hDn⟩ | ⟨ht, hDn, hAle, hsec⟩
    · rw [hDn, show d + m = m + 1 + e by lia]
      refine natDegree_eq_and_leadingCoeff_pos_of_coeff_pos hleQ ?_
      rw [htop]; exact mul_pos ht hl
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
      simp only [Nat.add_sub_cancel] at hsec hDn ht htop hleQ ⊢
      rw [hDn, he, show e + 1 + (k + 1) - 1 = k + 1 + e by lia]
      refine natDegree_eq_and_leadingCoeff_pos_of_coeff_pos ?_ ?_
      · rw [natDegree_le_iff_coeff_eq_zero]
        intro j hj
        rcases (show j = k + 1 + 1 + e ∨ k + 1 + 1 + e < j by lia) with rfl | hj'
        · rw [htop, ht, zero_mul]
        · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hleQ hj')
      · have hc := hnn e
        rw [he] at hlc ht hsec
        push_cast at ht hsec
        rcases e with _ | e
        · have hPC' : derivative f = C f.leadingCoeff := by
            rw [eq_C_of_natDegree_le_zero hP', coeff_derivative, ← hlc]; simp
          rw [coeff_add, hPC', coeff_mul_C, show k + 1 + 0 = k + 0 + 1 by lia,
            coeff_mul_add_add_one_eq_of_natDegree_le hB hPd, hlc]
          push_cast at ht hsec ⊢
          nlinarith [mul_nonneg (neg_nonneg.mpr hAle) hc, mul_pos hsec hl]
        · rw [coeff_add, show k + 1 + (e + 1) = k + 1 + e + 1 by lia,
            coeff_mul_add_add_one_eq_of_natDegree_le hA hP',
            show k + 1 + e + 1 = k + (e + 1) + 1 by lia,
            coeff_mul_add_add_one_eq_of_natDegree_le hB hPd, coeff_derivative, coeff_derivative,
            hlc]
          push_cast at ht hsec ⊢
          nlinarith [mul_nonneg (neg_nonneg.mpr hAle) hc, mul_pos hsec hl]

/-- Degrees, positive leading coefficients and nonnegative coefficients of a first-order
derivative recurrence whose top terms grow or cancel exactly at each step; the coefficients
stay nonnegative by the condition of `derivRec_hasNonnegCoeffs_of_mult` up to the degree
`D n` of the current row. -/
theorem derivRec_natDegree_eq_and_leadingCoeff_pos_of_cancel {P A B : ℕ → ℝ[X]} {D : ℕ → ℕ}
    {m : ℕ} (hm : 1 ≤ m)
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hA : ∀ n, (A n).natDegree ≤ m + 1) (hB : ∀ n, (B n).natDegree ≤ m)
    (hA0 : ∀ n, 0 ≤ (A n).coeff 0)
    (hmult : ∀ n i (j : ℕ), j ≤ D n → 0 ≤ (A n).coeff (i + 1) * j + (B n).coeff i)
    (h0 : (P 0).natDegree = D 0) (hpos0 : 0 < (P 0).leadingCoeff)
    (hnn0 : HasNonnegCoeffs (P 0))
    (hstep : ∀ n,
      (0 < (A n).coeff (m + 1) * D n + (B n).coeff m ∧ D (n + 1) = D n + m) ∨
      ((A n).coeff (m + 1) * D n + (B n).coeff m = 0 ∧ D (n + 1) = D n + m - 1 ∧
        (A n).coeff (m + 1) ≤ 0 ∧ 0 < (A n).coeff m * D n + (B n).coeff (m - 1)))
    (n : ℕ) :
    (P n).natDegree = D n ∧ 0 < (P n).leadingCoeff ∧ HasNonnegCoeffs (P n) := by
  induction n with
  | zero => exact ⟨h0, hpos0, hnn0⟩
  | succ n ih =>
    obtain ⟨hd, hl, hnn⟩ := ih
    have hnn' : HasNonnegCoeffs (P (n + 1)) := by
      rw [hrec n, add_comm]
      exact hasNonnegCoeffs_mul_add_mul_derivative hd.le (hA0 n) (hmult n) hnn
    rw [hrec n] at hnn' ⊢
    exact ⟨(derivRec_natDegree_eq_and_leadingCoeff_pos_step_of_cancel hm (hA n) (hB n) hnn hd hl
      (hstep n)).1, (derivRec_natDegree_eq_and_leadingCoeff_pos_step_of_cancel hm (hA n) (hB n)
      hnn hd hl (hstep n)).2, hnn'⟩

end RealRooted
