import RealRooted.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
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
private theorem hasNonnegCoeffs_mul_add_mul_derivative {U V Q : ℝ[X]} {N : ℕ}
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

end RealRooted
