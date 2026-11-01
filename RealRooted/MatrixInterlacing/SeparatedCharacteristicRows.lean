module

public import RealRooted.MatrixInterlacing.SeparatedCharacteristic
public import RealRooted.PFPolynomial
import RealRooted.PosCombo

/-!
# Iterated rows of separated-characteristic matrices

This module packages iteration of the matrices associated with

`∏ i, (S - a i) P = X * ∏ j, (S - b j) P`.

Under the separated-sign hypotheses, an ordered PF seed remains an ordered
PF vector.  Moreover, each coordinate weakly interlaces the same coordinate
after one matrix step, and hence in every pair of consecutive iterates.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Iterates of a separated-characteristic matrix acting on a polynomial
column vector. -/
def separatedCharacteristicRows {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (seed : Fin (h + m) → ℝ[X]) : ℕ → Fin (h + m) → ℝ[X]
  | 0 => seed
  | n + 1 => (separatedCharacteristicFinMatrix a b).mulVec
      (separatedCharacteristicRows a b seed n)

@[simp] theorem separatedCharacteristicRows_zero {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (seed : Fin (h + m) → ℝ[X]) :
    separatedCharacteristicRows a b seed 0 = seed := rfl

@[simp] theorem separatedCharacteristicRows_succ {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (seed : Fin (h + m) → ℝ[X]) (n : ℕ) :
    separatedCharacteristicRows a b seed (n + 1) =
      (separatedCharacteristicFinMatrix a b).mulVec
        (separatedCharacteristicRows a b seed n) := rfl

/-- Ordered zero-aware PF vectors remain ordered zero-aware PF vectors under
every separated-characteristic matrix iterate. -/
theorem separatedCharacteristicRows_interlacing {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    {seed : Fin (h + m) → ℝ[X]}
    (hseed : IsInterlacingSeq0NonnegRealRooted (List.ofFn seed)) (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (List.ofFn (separatedCharacteristicRows a b seed n)) := by
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
      rw [separatedCharacteristicRows_succ, ← separatedCharacteristicMatrix_action]
      exact separatedCharacteristicMatrix_preservesInterlacingSeq0 ha hb
        _ (by simp) ih

/-- Every coordinate of every separated-characteristic matrix iterate is a
PF polynomial.  Zero coordinates are allowed. -/
theorem separatedCharacteristicRows_isPFPolynomial {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    {seed : Fin (h + m) → ℝ[X]}
    (hseed : IsInterlacingSeq0NonnegRealRooted (List.ofFn seed))
    (n : ℕ) (i : Fin (h + m)) :
    IsPFPolynomial (separatedCharacteristicRows a b seed n i) := by
  have hrows := separatedCharacteristicRows_interlacing ha hb hseed n
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hrows.nonnegCoeffs _ (by simp)
  · by_cases hi : separatedCharacteristicRows a b seed n i = 0
    · exact Or.inl hi
    · exact Or.inr (hrows.splits (by simp) hi)

private lemma separatedCharacteristicFinMatrix_interl_mulVec {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    {f : Fin (h + m) → ℝ[X]}
    (hf : IsInterlacingSeq0NonnegRealRooted (List.ofFn f))
    (i : Fin (h + m)) :
    Interl (f i) ((separatedCharacteristicFinMatrix a b).mulVec f i) := by
  let z : Fin (h + m) := ⟨0, by lia [i.isLt]⟩
  have hnn (j : Fin (h + m)) : HasNonnegCoeffs (f j) :=
    hf.nonnegCoeffs _ (by simp)
  have hinterl (r s : Fin (h + m)) (hrs : r ≤ s) : Interl (f r) (f s) := by
    let r' : Fin (List.ofFn f).length := ⟨r, by simp⟩
    let s' : Fin (List.ofFn f).length := ⟨s, by simp⟩
    simpa [r', s'] using hf.interl_of_le (i := r') (j := s') hrs
  rw [Matrix.mulVec, dotProduct]
  apply Interl.finsetSum_left_of_nonneg
  · intro j _
    have hfi : HasNonnegCoeffs (f i) := hnn i
    have hfj : HasNonnegCoeffs (f j) := hnn j
    by_cases hi : (i : ℕ) + 1 < h
    · simp only [separatedCharacteristicFinMatrix, hi]
      by_cases hji : j = i
      · subst j
        simp only [ite_true]
        by_cases hsucc : (i : ℕ) = i + 1
        · lia
        · simp only [hsucc, ite_false, add_zero]
          exact (hinterl i i le_rfl).C_mul_right_of_nonneg (ha i)
      · simp only [hji, ite_false, zero_add]
        by_cases hsucc : (j : ℕ) = i + 1
        · have hij : i < j := by lia
          simpa [hsucc] using hinterl i j hij.le
        · simp [hsucc, interl_zero_right]
    · simp only [separatedCharacteristicFinMatrix, hi]
      by_cases hj0 : (j : ℕ) = 0
      · have h0j : j = z := Fin.ext hj0
        subst j
        simp only [hj0, ite_true]
        by_cases h0i : z = i
        · rw [h0i]
          simp only [ite_true, lt_self_iff_false, ite_false, add_zero]
          have hself := hinterl i i le_rfl
          have hX := interl_mul_X_of_interl hself hfi hfi
          have ha0 := hself.C_mul_right_of_nonneg (ha i)
          convert interl_add_right_of_common_left_of_nonneg hX ha0
            hfi.X_mul (hasNonnegCoeffs_C_mul (ha i) hfi) using 1
          simp
          ring
        · have h0le : z ≤ i := by
            change 0 ≤ (i : ℕ)
            exact Nat.zero_le _
          have hnot : ¬i < z := not_lt_of_ge h0le
          simp only [h0i, ite_false, hnot, add_zero]
          exact interl_mul_X_of_interl (hinterl z i h0le) (hnn z) hfi
      · simp only [hj0, ite_false, zero_add]
        by_cases hji : j = i
        · subst j
          simp only [ite_true, lt_self_iff_false, ite_false, add_zero]
          exact (hinterl i i le_rfl).C_mul_right_of_nonneg (ha i)
        · simp only [hji, ite_false, zero_add]
          by_cases hij : i < j
          · simp only [hij, ite_true]
            exact (hinterl i j hij.le).C_mul_right_of_nonneg
              (sub_nonneg.mpr ((separatedCharacteristicTailCoeff_nonpos hb j).trans (ha j)))
          · simp [hij, interl_zero_right]
  · intro j _
    exact (separatedCharacteristicFinMatrix_hasNonnegCoeffs ha hb i j).mul
      (hnn j)

/-- At every iteration, each coordinate weakly interlaces the same coordinate
in the next row. -/
theorem separatedCharacteristicRows_interl_succ {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    {seed : Fin (h + m) → ℝ[X]}
    (hseed : IsInterlacingSeq0NonnegRealRooted (List.ofFn seed))
    (n : ℕ) (i : Fin (h + m)) :
    Interl (separatedCharacteristicRows a b seed n i)
      (separatedCharacteristicRows a b seed (n + 1) i) := by
  rw [separatedCharacteristicRows_succ]
  exact separatedCharacteristicFinMatrix_interl_mulVec ha hb
    (separatedCharacteristicRows_interlacing ha hb hseed n) i

end RealRooted
