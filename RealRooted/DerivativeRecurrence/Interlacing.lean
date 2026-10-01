import RealRooted.Derivative
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
  · exact derivative_interlaces hf hdeg
  · refine interlaces_of_natDegree_eq_zero_of_natDegree_eq_one ?_ ?_ hdeg.symm
    · exact leadingCoeff_ne_zero.mp
        (HasPosLeadingCoeff.derivative hpos (by omega)).ne'
    · exact Nat.le_zero.mp ((natDegree_derivative_le f).trans (by omega))

variable {P A B : ℕ → ℝ[X]} {D₀ : ℕ}

/-- One step: a real-rooted row of positive degree interlaces the next row. -/
theorem derivRec_interlaces_step (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (n : ℕ) (hA : ∀ r, (P n).IsRoot r → (A n).eval r ≤ 0) (hs : (P n).Splits)
    (hn : 1 ≤ D₀ + n) : Interlaces (P n) (P (n + 1)) := by
  have hF : P (n + 1) = B n * P n + A n * (P n).derivative := by
    rw [hrec n, add_comm]
  have hInter : Interlaces (P n).derivative (P n) :=
    derivative_interlaces_of_pos hs (hpos n) (by rw [hdeg]; omega)
  have hprec : StrictInterl (P n) (B n * P n + A n * (P n).derivative) :=
    strictInterl_of_interlaces_evalCoeff_nonpos hInter
      (HasPosLeadingCoeff.derivative (hpos n) (by rw [hdeg]; omega))
      (by rw [← hF]; exact hpos (n + 1))
      (by rw [← hF, hdeg, hdeg]; omega) (by rw [← hF, hdeg, hdeg]; omega) hA
  rw [← hF] at hprec
  exact hprec.toInterlaces (by rw [hdeg, hdeg]; omega)

theorem derivRec_interlaces (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n r, (P n).IsRoot r → (A n).eval r ≤ 0)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  induction n with
  | zero => exact h01
  | succ n ih =>
      exact derivRec_interlaces_step hrec hdeg hpos (n + 1) (hA (n + 1)) ih.1.2 (by omega)

/-- Starting from a real-rooted row of positive degree, no base interlacing is
needed. -/
theorem derivRec_interlaces_of_splits
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hD : 1 ≤ D₀) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n r, (P n).IsRoot r → (A n).eval r ≤ 0) (h0 : (P 0).Splits) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  induction n with
  | zero => exact derivRec_interlaces_step hrec hdeg hpos 0 (hA 0) h0 (by omega)
  | succ n ih =>
      exact derivRec_interlaces_step hrec hdeg hpos (n + 1) (hA (n + 1)) ih.1.2 (by omega)

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

private theorem coeff_X_mul_derivative (p : ℝ[X]) (j : ℕ) :
    (X * p.derivative).coeff j = (j : ℝ) * p.coeff j := by
  rcases j with _ | j
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

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
        · rw [coeff_eq_zero_of_natDegree_lt ((hdeg n).trans_lt (by omega))]
          ring_nf
          rfl

end RealRooted
