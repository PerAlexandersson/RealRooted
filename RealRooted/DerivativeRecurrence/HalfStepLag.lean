module

public import RealRooted.EulerOperator
public import RealRooted.PFPolynomial
import RealRooted.Basic.Coefficients
import RealRooted.CommonInterleaver.RootDesc
import RealRooted.Derivative.Algebra
import RealRooted.Derivative.Interlacing
import RealRooted.Interlacing.WindowInduction
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Uniform half-step lag windows

Fix `k ≠ 0`, rows `H : ℕ → ℝ[X]` and positive weights `c : ℕ → ℝ`, and suppose that

* `H (2 m + 1) = thetaPlusOne (H (2 m))`, and
* `H (2 (q + k)) = H (2 (q + k) - 1) + C (c q) * X * H (2 q)`.

We prove that if the first `2 k + 1` rows `H 0, ..., H (2 k)` are pairwise strictly
interlacing, then so is every window `H n, ..., H (n + 2 k)`.  This is a reachable-orbit
statement for a positive `X` lag, not preservation by a full companion matrix.

The proof slides the window by one step.  For an even start the new endpoint is
`thetaPlusOne` applied to the old endpoint pair, and the new consecutive edge is the Euler
(Rolle) edge `p ≪ thetaPlusOne p`.  For an odd start the new endpoint is `u + c X v` with
`v ≪ u`, and `add_mul_X_of_common_left` applies twice.  Both cases are closed by
`strictInterl_chain_of_consecutive_of_endpoint`.

The second part packages the common seeded interface: rows `A` with `A m = 1` for `m < k` and
`A (q + k) = thetaPlusOne (A (q + k - 1)) + C (c q) * X * A q`.  Interleaving the even rows
`A m` with their Euler images gives a half-step family, so all rows are PF, any two rows at
distance at most `k` strictly interlace, and `natDegree (A m) = m / k`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A polynomial in the nonnegative-coefficient cone that is nonzero and splits lies strictly
to the left of its Euler image `thetaPlusOne p = (X * p)'` (Rolle's theorem). -/
theorem strictInterl_self_thetaPlusOne_of_nonneg {p : ℝ[X]} (hp0 : p ≠ 0) (hs : p.Splits)
    (hnn : HasNonnegCoeffs p) : StrictInterl p (thetaPlusOne p) := by
  have hXp := isRealRooted_X_mul hp0 hs
  have hder : StrictInterl (X * p).derivative (X * p) :=
    (derivative_interlaces_of_natDegree_ne_zero hXp.2
      (by rw [natDegree_X_mul hp0]; lia)).toStrictInterl
  rw [thetaPlusOne_eq_derivative_X_mul]
  exact (strictInterl_iff_mul_X_of_roots_nonpos (roots_nonpos_of_hasNonnegCoeffs hnn)
    (roots_nonpos_of_hasNonnegCoeffs hnn.X_mul.derivative)).mpr hder

/-- The window `H n, ..., H (n + 2 k)` is pairwise (inclusively) strictly interlacing. -/
@[expose] def HalfStepWindow (H : ℕ → ℝ[X]) (k n : ℕ) : Prop :=
  ∀ i j, n ≤ i → i ≤ j → j ≤ n + 2 * k → StrictInterl (H i) (H j)

/-- Sliding a half-step window by one step: if `H n, ..., H (n + 2 k)` is pairwise strictly
interlacing then so is `H (n + 1), ..., H (n + 1 + 2 k)`.  The weights `c` must be positive and
all rows must have nonnegative coefficients. -/
theorem HalfStepWindow.succ {H : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ} (hk : k ≠ 0)
    (hodd : ∀ m, H (2 * m + 1) = thetaPlusOne (H (2 * m)))
    (heven : ∀ q, H (2 * (q + k)) = H (2 * (q + k) - 1) + C (c q) * X * H (2 * q))
    (hc : ∀ q, 0 < c q) (hnn : ∀ n, HasNonnegCoeffs (H n)) {n : ℕ}
    (h : HalfStepWindow H k n) : HalfStepWindow H k (n + 1) := by
  have hpos (i : ℕ) (h1 : n ≤ i) (h2 : i ≤ n + 2 * k) : HasPosLeadingCoeff (H i) :=
    (hnn i).pos_leadingCoeff (h i i h1 le_rfl h2).1.1
  -- the last consecutive edge and the endpoint edge of the new window
  have key : StrictInterl (H (n + 2 * k)) (H (n + 2 * k + 1)) ∧
      StrictInterl (H (n + 1)) (H (n + 1 + 2 * k)) := by
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hE : 2 * t + 2 * k = 2 * (t + k) := by ring
      have hE' : 2 * t + 1 + 2 * k = 2 * (t + k) + 1 := by ring
      have hend := (h (2 * t) (2 * (t + k)) (by lia) (by lia) (by lia)).thetaPlusOne
      have hself := h (2 * (t + k)) (2 * (t + k)) (by lia) le_rfl (by lia)
      refine ⟨?_, ?_⟩
      · rw [hE, hodd]
        exact strictInterl_self_thetaPlusOne_of_nonneg hself.1.1 hself.1.2 (hnn _)
      · rw [hE', hodd, hodd]
        exact hend
    · have heq := heven (t + 1)
      rw [show 2 * (t + 1 + k) - 1 = 2 * t + 1 + 2 * k by lia,
        show 2 * (t + 1 + k) = 2 * t + 1 + 2 * k + 1 by lia,
        show 2 * (t + 1) = 2 * t + 1 + 1 by lia] at heq
      have hvu := h (2 * t + 1 + 1) (2 * t + 1 + 2 * k) (by lia) (by lia) le_rfl
      have hvv := h (2 * t + 1 + 1) (2 * t + 1 + 1) (by lia) le_rfl (by lia)
      have huu := h (2 * t + 1 + 2 * k) (2 * t + 1 + 2 * k) (by lia) le_rfl (by lia)
      have hvXv := strictInterl_mul_X_of_strictInterl_of_nonneg hvv (hnn _) (hnn _)
      have huXv := strictInterl_mul_X_of_strictInterl_of_nonneg hvu (hnn _) (hnn _)
      have hupos := hpos (2 * t + 1 + 2 * k) (by lia) le_rfl
      have hvpos := (hpos (2 * t + 1 + 1) (by lia) (by lia)).X_mul
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact StrictInterl.add_mul_X_of_common_left (hc _) huu huXv hupos hvpos
      · rw [show 2 * t + 1 + 1 + 2 * k = 2 * t + 1 + 2 * k + 1 by ring, heq]
        exact StrictInterl.add_mul_X_of_common_left (hc _) hvu hvXv hupos hvpos
  intro i j hi hij hj
  refine strictInterl_chain_of_consecutive_of_endpoint H (n + 1) (n + 1 + 2 * k) ?_ key.2
    i j hi hij hj
  intro i h1 h2
  by_cases hle : i + 1 ≤ n + 2 * k
  · exact h i (i + 1) (by lia) (by lia) hle
  · obtain rfl : i = n + 2 * k := by lia
    exact key.1

/-- **Uniform half-step window theorem.**  If the initial window `H 0, ..., H (2 k)` is pairwise
strictly interlacing and `H` satisfies the subtraction-free half-step recurrence with positive
weights `c` (an `X` lag of `k` even steps) and nonnegative coefficients, then every window
`H n, ..., H (n + 2 k)` is pairwise strictly interlacing. -/
theorem halfStepWindow_of_positive_X_lag {H : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ} (hk : k ≠ 0)
    (hbase : HalfStepWindow H k 0)
    (hodd : ∀ m, H (2 * m + 1) = thetaPlusOne (H (2 * m)))
    (heven : ∀ q, H (2 * (q + k)) = H (2 * (q + k) - 1) + C (c q) * X * H (2 * q))
    (hc : ∀ q, 0 < c q) (hnn : ∀ n, HasNonnegCoeffs (H n)) :
    ∀ n, HalfStepWindow H k n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact ih.succ hk hodd heven hc hnn

/-! ### The seeded row recurrence -/

/-- The seeded row recurrence: `A m = 1` for `m < k` and
`A (q + k) = thetaPlusOne (A (q + k - 1)) + C (c q) * X * A q` with positive weights `c`. -/
structure HalfStepRows (A : ℕ → ℝ[X]) (k : ℕ) (c : ℕ → ℝ) : Prop where
  /-- The lag is positive. -/
  k_ne_zero : k ≠ 0
  /-- The seed rows are the constant `1`. -/
  seed : ∀ m, m < k → A m = 1
  /-- The recurrence step. -/
  step : ∀ q, A (q + k) = thetaPlusOne (A (q + k - 1)) + C (c q) * X * A q
  /-- The weights are positive. -/
  pos : ∀ q, 0 < c q

/-- The half-step family of a row sequence `A`: `A m` at even positions `2 m` and its Euler
image `thetaPlusOne (A m)` at odd positions `2 m + 1`. -/
@[expose] def halfStepSeq (A : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  if n % 2 = 0 then A (n / 2) else thetaPlusOne (A (n / 2))

@[simp] theorem halfStepSeq_two_mul (A : ℕ → ℝ[X]) (m : ℕ) :
    halfStepSeq A (2 * m) = A m := by
  simp [halfStepSeq]

@[simp] theorem halfStepSeq_two_mul_add_one (A : ℕ → ℝ[X]) (m : ℕ) :
    halfStepSeq A (2 * m + 1) = thetaPlusOne (A m) := by
  have h1 : (2 * m + 1) % 2 = 1 := by lia
  have h2 : (2 * m + 1) / 2 = m := by lia
  simp [halfStepSeq, h1, h2]

/-- `thetaPlusOne` fixes the constant `1`. -/
theorem thetaPlusOne_one : thetaPlusOne (1 : ℝ[X]) = 1 := by
  simp [thetaPlusOne, theta]

namespace HalfStepRows

variable {A : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ}

/-- Every row of a seeded half-step recurrence has nonnegative coefficients. -/
theorem hasNonnegCoeffs (h : HalfStepRows A k c) (m : ℕ) : HasNonnegCoeffs (A m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < k
    · rw [h.seed m hm]
      exact hasNonnegCoeffs_one
    · obtain ⟨q, rfl⟩ : ∃ q, m = q + k := ⟨m - k, by lia⟩
      have hk := h.k_ne_zero
      rw [h.step q, mul_assoc]
      exact (ih (q + k - 1) (by lia)).thetaPlusOne.add
        (hasNonnegCoeffs_C_mul (h.pos q).le (hasNonnegCoeffs_X.mul (ih q (by lia))))

/-- Every row of the half-step family has nonnegative coefficients. -/
theorem hasNonnegCoeffs_halfStepSeq (h : HalfStepRows A k c) (n : ℕ) :
    HasNonnegCoeffs (halfStepSeq A n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [halfStepSeq_two_mul]
    exact h.hasNonnegCoeffs m
  · rw [halfStepSeq_two_mul_add_one]
    exact (h.hasNonnegCoeffs m).thetaPlusOne

/-- The first `2 k` half-step rows are the constant `1`. -/
theorem halfStepSeq_eq_one_of_lt (h : HalfStepRows A k c) {i : ℕ} (hi : i < 2 * k) :
    halfStepSeq A i = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [halfStepSeq_two_mul, h.seed m (by lia)]
  · rw [halfStepSeq_two_mul_add_one, h.seed m (by lia), thetaPlusOne_one]

/-- The row `A k` of a seeded half-step recurrence is `1 + c₀ X`. -/
theorem halfStepSeq_two_mul_k (h : HalfStepRows A k c) :
    halfStepSeq A (2 * k) = 1 + C (c 0) * X * 1 := by
  have hk := h.k_ne_zero
  have := h.step 0
  rw [halfStepSeq_two_mul, ← zero_add k, this, zero_add, h.seed (k - 1) (by lia),
    h.seed 0 (by lia), thetaPlusOne_one]

/-- The initial window `H 0, ..., H (2 k)` of the seeded half-step family is pairwise strictly
interlacing. -/
theorem halfStepWindow_zero (h : HalfStepRows A k c) : HalfStepWindow (halfStepSeq A) k 0 := by
  have hone : StrictInterl (1 : ℝ[X]) 1 := StrictInterl.refl one_ne_zero Polynomial.Splits.one
  have hnn1 : HasNonnegCoeffs (1 : ℝ[X]) := hasNonnegCoeffs_one
  have hpos1 : HasPosLeadingCoeff (1 : ℝ[X]) := by simp [HasPosLeadingCoeff]
  have hX : StrictInterl (1 : ℝ[X]) (X * 1) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hone hnn1 hnn1
  have hedge : StrictInterl (1 : ℝ[X]) (1 + C (c 0) * X * 1) :=
    StrictInterl.add_mul_X_of_common_left (h.pos 0) hone hX hpos1 hpos1.X_mul
  intro i j _ hij hj
  by_cases hjk : j < 2 * k
  · rw [h.halfStepSeq_eq_one_of_lt (by lia), h.halfStepSeq_eq_one_of_lt hjk]
    exact hone
  · obtain rfl : j = 2 * k := by lia
    rw [h.halfStepSeq_two_mul_k]
    by_cases hik : i < 2 * k
    · rw [h.halfStepSeq_eq_one_of_lt hik]
      exact hedge
    · obtain rfl : i = 2 * k := by lia
      rw [h.halfStepSeq_two_mul_k]
      exact StrictInterl.refl hedge.2.1.1 hedge.2.1.2

/-- Every window `H n, ..., H (n + 2 k)` of the seeded half-step family is pairwise strictly
interlacing. -/
theorem halfStepWindow (h : HalfStepRows A k c) (n : ℕ) :
    HalfStepWindow (halfStepSeq A) k n := by
  refine halfStepWindow_of_positive_X_lag h.k_ne_zero h.halfStepWindow_zero
    (fun m ↦ by rw [halfStepSeq_two_mul_add_one, halfStepSeq_two_mul]) ?_ h.pos
    h.hasNonnegCoeffs_halfStepSeq n
  intro q
  have hk := h.k_ne_zero
  rw [halfStepSeq_two_mul, show 2 * (q + k) - 1 = 2 * (q + k - 1) + 1 by lia,
    halfStepSeq_two_mul_add_one, halfStepSeq_two_mul, h.step q]

/-- Rows of a seeded half-step recurrence at distance at most `k` strictly interlace. -/
theorem strictInterl_add_of_le (h : HalfStepRows A k c) (m : ℕ) {r : ℕ} (hr : r ≤ k) :
    StrictInterl (A m) (A (m + r)) := by
  have := h.halfStepWindow (2 * m) (2 * m) (2 * (m + r)) le_rfl (by lia) (by lia)
  rwa [halfStepSeq_two_mul, halfStepSeq_two_mul] at this

/-- Every row of a seeded half-step recurrence is nonzero and splits over the reals. -/
theorem ne_zero_and_splits (h : HalfStepRows A k c) (m : ℕ) : A m ≠ 0 ∧ (A m).Splits :=
  (h.strictInterl_add_of_le m (Nat.zero_le k)).1

/-- Every row of a seeded half-step recurrence is a PF polynomial. -/
theorem isPFPolynomial (h : HalfStepRows A k c) (m : ℕ) : IsPFPolynomial (A m) :=
  ⟨h.hasNonnegCoeffs m, Or.inr (h.ne_zero_and_splits m).2,
    roots_nonpos_of_hasNonnegCoeffs (h.hasNonnegCoeffs m)⟩

/-- Every row of a seeded half-step recurrence has positive leading coefficient. -/
theorem hasPosLeadingCoeff (h : HalfStepRows A k c) (m : ℕ) : HasPosLeadingCoeff (A m) :=
  (h.hasNonnegCoeffs m).pos_leadingCoeff (h.ne_zero_and_splits m).1

/-- The exact degree of the `m`-th row of a seeded half-step recurrence is `m / k`.  Positivity
of the weights prevents cancellation between the Euler term and the `X` lag. -/
theorem natDegree_eq_div (h : HalfStepRows A k c) (m : ℕ) : (A m).natDegree = m / k := by
  have hk := h.k_ne_zero
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < k
    · rw [h.seed m hm, natDegree_one, Nat.div_eq_of_lt hm]
    · obtain ⟨q, rfl⟩ : ∃ q, m = q + k := ⟨m - k, by lia⟩
      have hq0 := (h.ne_zero_and_splits q).1
      have hdiv : (q + k) / k = q / k + 1 := Nat.add_div_right q (Nat.pos_of_ne_zero hk)
      have hle : (q + k - 1) / k ≤ q / k + 1 := hdiv ▸ Nat.div_le_div_right (by lia)
      have hC : (C (c q) : ℝ[X]) ≠ 0 := by simpa using (h.pos q).ne'
      have hT0 : C (c q) * X * A q ≠ 0 := mul_ne_zero (mul_ne_zero hC X_ne_zero) hq0
      have hT : (C (c q) * X * A q).natDegree = q / k + 1 := by
        rw [mul_assoc, natDegree_C_mul (h.pos q).ne', natDegree_X_mul hq0, ih q (by lia)]
      have hTnn : HasNonnegCoeffs (C (c q) * X * A q) := by
        rw [mul_assoc]
        exact hasNonnegCoeffs_C_mul (h.pos q).le (hasNonnegCoeffs_X.mul (h.hasNonnegCoeffs q))
      have hTpos := hTnn.pos_leadingCoeff hT0
      have hθnn := (h.hasNonnegCoeffs (q + k - 1)).thetaPlusOne
      rw [hdiv]
      rw [h.step q]
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · refine natDegree_add_le_of_degree_le ?_ hT.le
        refine (natDegree_thetaPlusOne_le _).trans ?_
        rw [ih _ (by lia)]
        exact hle
      · rw [coeff_add]
        have hcoeff : (C (c q) * X * A q).coeff (q / k + 1) > 0 := by
          rw [← hT]
          exact hTpos
        exact (add_pos_of_nonneg_of_pos (hθnn _) hcoeff).ne'

end HalfStepRows

end RealRooted
