module

public import RealRooted.MatrixInterlacing.PartialProductStep
public import RealRooted.SimpleRoots
import RealRooted.WagnerRightSum.Sign
import RealRooted.PosCombo
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Interlacing exponential rows via partial products

We implement the partial-product recurrence from the unpublished argument in
RealRooted issue #2415, https://github.com/PerAlexandersson/RealRooted/issues/2415.
The coordinates are ordered from the highest partial product down to the scalar row.
The scalar row is updated by `F + X ∑ qᵢ Vᵢ`. The other coordinates use the
partial-product matrix with scale `n + 1`.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.ExponentialRows

/-- The partial-product vector, with seed consisting of zeros followed by one. -/
noncomputable def partialProductVector (r q : ℕ → ℝ) (m : ℕ) :
    ℕ → Fin (m + 1) → ℝ[X]
  | 0 => Fin.lastCases 1 (fun _ => 0)
  | n + 1 => Fin.lastCases
      (partialProductVector r q m n (Fin.last m) + X *
        ∑ j : Fin m, C (q j) * partialProductVector r q m n j.castSucc)
      (fun i => ∑ j : Fin (m + 1),
        C (partialProductMatrix r m (n + 1) i j) * partialProductVector r q m n j)

/-- The scalar exponential row carried by the partial-product recurrence. -/
noncomputable def partialProductRow (r q : ℕ → ℝ) (m n : ℕ) : ℝ[X] :=
  partialProductVector r q m n (Fin.last m)

/-- The seed vector is nonnegative, real-rooted, and zero-aware interlacing. -/
theorem partialProductVector_zero_interlacing (r q : ℕ → ℝ) (m : ℕ) :
    IsInterlacingSeq0NonnegRealRooted (List.ofFn (partialProductVector r q m 0)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn]
    intro i j hij
    induction i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i => simpa [partialProductVector] using
        (interl_zero_left (partialProductVector r q m 0 j))
  · simp only [List.forall_mem_ofFn_iff]
    intro i
    induction i using Fin.lastCases with
    | last => simpa [partialProductVector] using hasNonnegCoeffs_one
    | cast i => simpa [partialProductVector] using hasNonnegCoeffs_zero
  · simp only [List.forall_mem_ofFn_iff]
    intro i hi
    induction i using Fin.lastCases with
    | last => simp [partialProductVector]
    | cast i => simp [partialProductVector] at hi

/-- The typed recurrence agrees with polynomial matrix action. -/
theorem partialProductVector_succ (r q : ℕ → ℝ) (m n : ℕ) :
    List.ofFn (partialProductVector r q m (n + 1)) =
      matPolyAction (variableLastRowMatrix (partialProductMatrix r m (n + 1))
        (fun j => q j)) (List.ofFn (partialProductVector r q m n)) := by
  rw [variableLastRowMatrix_action]
  rfl

/-- The weighted partial-product condition closes the full mutual-interlacing induction. -/
theorem partialProductVector_interlacing {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m → q (k + 1) ≤ r k * q k) (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted (List.ofFn (partialProductVector r q m n)) := by
  induction n with
  | zero => exact partialProductVector_zero_interlacing r q m
  | succ n ih =>
    rw [partialProductVector_succ]
    exact partialProductMatrix_variableLastRow_preserves hr hq hstep (by positivity)
      _ (by simp) ih

/-- The scalar coordinate follows the Newton-weighted insertion recurrence. -/
theorem partialProductRow_succ (r q : ℕ → ℝ) (m n : ℕ) :
    partialProductRow r q m (n + 1) = partialProductRow r q m n +
      X * ∑ j : Fin m, C (q j) * partialProductVector r q m n j.castSucc := by
  simp only [partialProductRow, partialProductVector, Fin.lastCases_last]

/-- Each scalar row has constant coefficient one. -/
@[simp] theorem partialProductRow_coeff_zero (r q : ℕ → ℝ) (m n : ℕ) :
    (partialProductRow r q m n).coeff 0 = 1 := by
  induction n with
  | zero => simp [partialProductRow, partialProductVector]
  | succ n ih =>
    simpa [partialProductRow, partialProductVector, coeff_X_mul] using ih

/-- The scalar rows never vanish. -/
theorem partialProductRow_ne_zero (r q : ℕ → ℝ) (m n : ℕ) :
    partialProductRow r q m n ≠ 0 := by
  intro hz
  have h := partialProductRow_coeff_zero r q m n
  simp [hz] at h

/-- Scalar rows have nonnegative coefficients under the partial-product condition. -/
theorem partialProductRow_hasNonnegCoeffs {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m → q (k + 1) ≤ r k * q k) (n : ℕ) :
    HasNonnegCoeffs (partialProductRow r q m n) :=
  (partialProductVector_interlacing hr hq hstep n).nonnegCoeffs _
    (List.mem_ofFn.mpr ⟨Fin.last m, rfl⟩)

/-- Every scalar row of the weighted partial-product recurrence is real-rooted. -/
theorem partialProductRow_splits {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m → q (k + 1) ≤ r k * q k) (n : ℕ) :
    (partialProductRow r q m n).Splits :=
  (partialProductVector_interlacing hr hq hstep n).splits
    (List.mem_ofFn.mpr ⟨Fin.last m, rfl⟩) (partialProductRow_ne_zero r q m n)

/-- The coordinate corresponding to the first partial product is `(n + 1) Fₙ`. -/
theorem partialProductVector_last_aux (r q : ℕ → ℝ) (m n : ℕ) :
    partialProductVector r q (m + 1) (n + 1) (Fin.last m).castSucc =
      C (n + 1 : ℝ) * partialProductRow r q (m + 1) n := by
  simp only [partialProductVector, Fin.lastCases_castSucc]
  rw [Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin (m + 1),
      C (partialProductMatrix r (m + 1) (n + 1) (Fin.last m) j.castSucc) *
        partialProductVector r q (m + 1) n j.castSucc) = 0 := by
    apply sum_eq_zero
    intro j _
    have hj : ¬ m < (j : ℕ) := by have := j.isLt; lia
    simp [partialProductMatrix, hj]
  rw [hz, zero_add]
  simp [partialProductMatrix, partialProductRow]

/-- Consecutive scalar rows interlace in the repository's `StrictInterl` orientation. -/
theorem partialProductRow_strictInterl_succ {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m + 1, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m + 1 → q (k + 1) ≤ r k * q k) (n : ℕ) :
    StrictInterl (partialProductRow r q (m + 1) n)
      (partialProductRow r q (m + 1) (n + 1)) := by
  have hv := (partialProductVector_interlacing hr hq hstep (n + 1)).interlacingSeq0
  rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn] at hv
  have h := hv (i := (Fin.last m).castSucc) (j := Fin.last (m + 1))
    (Fin.castSucc_lt_last _)
  rw [partialProductVector_last_aux] at h
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have h' := h.toStrictInterl_of_ne
    (mul_ne_zero (C_ne_zero.mpr hn) (partialProductRow_ne_zero r q (m + 1) n))
    (partialProductRow_ne_zero r q (m + 1) (n + 1))
  have heq : C ((n + 1 : ℝ)⁻¹) *
      (C (n + 1 : ℝ) * partialProductRow r q (m + 1) n) =
      partialProductRow r q (m + 1) n := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]
  have hh := h'.C_mul_left (inv_ne_zero hn)
  rw [heq] at hh
  exact hh

/-- The second partial product is `N V¹` when the second root parameter is zero. -/
theorem partialProductVector_second_aux {r q : ℕ → ℝ} (m n : ℕ)
    (hr : r (m + 1) = 0) :
    partialProductVector r q (m + 2) (n + 1) ⟨m, by lia⟩ =
      C (n + 1 : ℝ) *
        partialProductVector r q (m + 2) n (Fin.last (m + 1)).castSucc := by
  have hi : (⟨m, by lia⟩ : Fin (m + 3)) = (⟨m, by lia⟩ : Fin (m + 2)).castSucc := rfl
  rw [hi]
  simp only [partialProductVector, Fin.lastCases_castSucc]
  rw [sum_eq_single (Fin.last (m + 1)).castSucc]
  · simp [partialProductMatrix]
  · intro j _ hj
    induction j using Fin.lastCases with
    | last => simp [partialProductMatrix, hr]
    | cast j =>
      have hj' : ¬ m < (j : ℕ) := by
        have hne : (j : ℕ) ≠ m + 1 := by
          intro heq
          apply hj
          apply Fin.ext
          exact heq
        have := j.isLt
        lia
      simp [partialProductMatrix, hj']
  · simp

/-- Rows at distance two interlace when the second Newton node is zero. -/
theorem partialProductRow_strictInterl_add_two {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m + 2, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m + 2 → q (k + 1) ≤ r k * q k)
    (hrzero : r (m + 1) = 0) (n : ℕ) :
    StrictInterl (partialProductRow r q (m + 2) n)
      (partialProductRow r q (m + 2) (n + 2)) := by
  have hv := (partialProductVector_interlacing hr hq hstep (n + 2)).interlacingSeq0
  rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn] at hv
  have h := hv (i := ⟨m, by lia⟩) (j := Fin.last (m + 2)) (by change m < m + 2; lia)
  rw [show n + 2 = (n + 1) + 1 by lia,
    partialProductVector_second_aux m (n + 1) hrzero,
    partialProductVector_last_aux r q (m + 1) n] at h
  have hc : (n + 1 : ℝ) * (n + 2) ≠ 0 := by positivity
  have hrow : C (n + 1 + 1 : ℝ) *
      (C (n + 1 : ℝ) * partialProductRow r q (m + 2) n) =
      C ((n + 1 : ℝ) * (n + 2)) * partialProductRow r q (m + 2) n := by
    rw [← mul_assoc, ← map_mul]
    congr 2
    ring
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [hrow] at h
  have h' := h.toStrictInterl_of_ne
    (mul_ne_zero (C_ne_zero.mpr hc) (partialProductRow_ne_zero r q (m + 2) n))
    (partialProductRow_ne_zero r q (m + 2) (n + 2))
  have heq : C (((n + 1 : ℝ) * (n + 2))⁻¹) *
      (C ((n + 1 : ℝ) * (n + 2)) * partialProductRow r q (m + 2) n) =
      partialProductRow r q (m + 2) n := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  have hh := h'.C_mul_left (inv_ne_zero hc)
  rw [heq] at hh
  exact hh

/-- A nonnegative sum of common left interlacers cannot vanish at a root of the right
polynomial if one positively weighted summand is nonzero there. -/
private lemma sum_eval_ne_zero_of_common_right {ι : Type*} [Fintype ι]
    {f : ι → ℝ[X]} {h : ℝ[X]} {q : ι → ℝ}
    (hf : ∀ i, Interl (f i) h) (hnn : ∀ i, HasNonnegCoeffs (f i))
    (hq : ∀ i, 0 ≤ q i) (i₀ : ι) (hi₀ : 0 < q i₀)
    {x : ℝ} (hx : h.IsRoot x) (hh : h ≠ 0) (hvalue : (f i₀).eval x ≠ 0) :
    (∑ i, C (q i) * f i).eval x ≠ 0 := by
  classical
  have hne : f i₀ ≠ 0 := by
    intro hz
    simp [hz] at hvalue
  have href := (hf i₀).toStrictInterl_of_ne hne hh
  have hsign (i : ι) : 0 ≤ (f i).eval x * (f i₀).eval x := by
    by_cases hi : f i = 0
    · simp [hi]
    · exact eval_mul_eval_nonneg_of_strictInterl_right
        ((hf i).toStrictInterl_of_ne hi hh) href
        ((hnn i).pos_leadingCoeff hi) ((hnn i₀).pos_leadingCoeff hne) hx
  have hnn' (i : ι) : 0 ≤ q i * ((f i).eval x * (f i₀).eval x) :=
    mul_nonneg (hq i) (hsign i)
  have hle := single_le_sum (fun i _ => hnn' i) (mem_univ i₀)
  have hpos : 0 < q i₀ * ((f i₀).eval x * (f i₀).eval x) :=
    mul_pos hi₀ (mul_self_pos.mpr hvalue)
  intro hz
  have heq : (∑ i, q i * ((f i).eval x * (f i₀).eval x)) =
      (∑ i, C (q i) * f i).eval x * (f i₀).eval x := by
    simp only [eval_finsetSum, eval_mul, eval_C, sum_mul, mul_assoc]
  rw [heq, hz, zero_mul] at hle
  linarith

/-- Positive weight on `V¹` excludes common roots of successive scalar rows. -/
theorem partialProductRow_no_common_root {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m + 1, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m + 1 → q (k + 1) ≤ r k * q k)
    (hqpos : 0 < q m) (n : ℕ) :
    ∀ x, ¬ ((partialProductRow r q (m + 1) n).IsRoot x ∧
      (partialProductRow r q (m + 1) (n + 1)).IsRoot x) := by
  induction n with
  | zero => simp [partialProductRow, partialProductVector]
  | succ n ih =>
    intro x hx
    have hv := partialProductVector_interlacing hr hq hstep (n + 1)
    have hpair := hv.interlacingSeq0
    rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn] at hpair
    have href : (partialProductVector r q (m + 1) (n + 1)
        (Fin.last m).castSucc).eval x ≠ 0 := by
      rw [partialProductVector_last_aux, eval_mul, eval_C]
      apply mul_ne_zero (by positivity)
      intro hz
      exact ih x ⟨hz, hx.1⟩
    have hsum := sum_eval_ne_zero_of_common_right
      (f := fun j : Fin (m + 1) => partialProductVector r q (m + 1) (n + 1) j.castSucc)
      (h := partialProductRow r q (m + 1) (n + 1)) (q := fun j => q j)
      (fun j => hpair (i := j.castSucc) (j := Fin.last (m + 1)) (Fin.castSucc_lt_last _))
      (fun j => hv.nonnegCoeffs _ (List.mem_ofFn.mpr ⟨j.castSucc, rfl⟩))
      (fun j => hq j j.isLt) (Fin.last m) hqpos hx.1
      (partialProductRow_ne_zero r q (m + 1) (n + 1)) href
    have hxne : x ≠ 0 := by
      intro hz
      have hx' := hx.1
      rw [Polynomial.IsRoot.def, hz, ← coeff_zero_eq_eval_zero,
        partialProductRow_coeff_zero] at hx'
      exact one_ne_zero hx'
    have hxnew := hx.2
    rw [Polynomial.IsRoot.def, partialProductRow_succ, eval_add, eval_mul, eval_X] at hxnew
    have hxold : (partialProductRow r q (m + 1) (n + 1)).eval x = 0 :=
      hx.1
    rw [hxold, zero_add] at hxnew
    exact mul_ne_zero hxne hsum hxnew

/-- Positive `V¹` weight gives simple roots in every scalar row. -/
theorem partialProductRow_hasSimpleRoots {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m + 1, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m + 1 → q (k + 1) ≤ r k * q k)
    (hqpos : 0 < q m) (n : ℕ) :
    HasSimpleRoots (partialProductRow r q (m + 1) n) :=
  ((partialProductRow_strictInterl_succ hr hq hstep n).hasSimpleRoots_of_no_common_root
    (partialProductRow_no_common_root hr hq hstep hqpos n)).1

/-- With one auxiliary coordinate, the scalar recurrence is the Hermite recurrence. -/
theorem partialProductRow_one_add_two (r q : ℕ → ℝ) (n : ℕ) :
    partialProductRow r q 1 (n + 2) = partialProductRow r q 1 (n + 1) +
      C (q 0 * (n + 1)) * (X * partialProductRow r q 1 n) := by
  rw [show n + 2 = (n + 1) + 1 by lia, partialProductRow_succ]
  simp only [Fin.sum_univ_one]
  have haux : partialProductVector r q 1 (n + 1) (Fin.castSucc (0 : Fin 1)) =
      C (n + 1 : ℝ) * partialProductRow r q 1 n := by
    simpa only [Fin.last_zero] using partialProductVector_last_aux r q 0 n
  rw [haux]
  simp only [Fin.val_zero, map_mul]
  ring

/-- The distance-two interlacing also holds in the Hermite case with one auxiliary. -/
theorem partialProductRow_one_strictInterl_add_two {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) (hq : 0 ≤ q 0) (n : ℕ) :
    StrictInterl (partialProductRow r q 1 n) (partialProductRow r q 1 (n + 2)) := by
  have hq' : ∀ k < 1, 0 ≤ q k := by
    intro k hk
    have hk' : k = 0 := by lia
    simpa only [hk'] using hq
  have hstep : ∀ k, k + 1 < 1 → q (k + 1) ≤ r k * q k := by intro k hk; lia
  have hnn := partialProductRow_hasNonnegCoeffs hr hq' hstep n
  have hnn' := partialProductRow_hasNonnegCoeffs hr hq' hstep (n + 1)
  have hx := (strictInterl_self_X_mul_of_nonneg (partialProductRow_ne_zero r q 1 n)
    (partialProductRow_splits hr hq' hstep n) hnn).toInterl
      |>.C_mul_right_of_nonneg (by positivity : 0 ≤ q 0 * (n + 1))
  have h := Interl.sum_left_of_common_left_of_nonneg
    [partialProductRow r q 1 (n + 1), C (q 0 * (n + 1)) * (X * partialProductRow r q 1 n)]
    (partialProductRow r q 1 n) (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (partialProductRow_strictInterl_succ hr hq' hstep n).toInterl
      · exact hx) (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hnn'
      · exact (hasNonnegCoeffs_C (by positivity)).mul hnn.X_mul)
  simp only [List.sum_cons, List.sum_nil, add_zero] at h
  rw [← partialProductRow_one_add_two] at h
  exact h.toStrictInterl_of_ne (partialProductRow_ne_zero r q 1 n)
    (partialProductRow_ne_zero r q 1 (n + 2))

/-- Adjacent auxiliary coordinates obey multiplication by their next linear factor. -/
theorem partialProductVector_aux_succ (r q : ℕ → ℝ) {m i : ℕ} (hi : i + 1 < m)
    (n : ℕ) :
    partialProductVector r q m (n + 1) (⟨i, by lia⟩ : Fin m).castSucc =
      C (r (i + 1)) * partialProductVector r q m (n + 1) (⟨i + 1, hi⟩ : Fin m).castSucc +
        C (n + 1 : ℝ) * partialProductVector r q m n (⟨i + 1, hi⟩ : Fin m).castSucc := by
  simp only [partialProductVector, Fin.lastCases_castSucc]
  exact partialProductMatrix_action_succ r hi (n + 1) (partialProductVector r q m n)

end RealRooted.ExponentialRows
