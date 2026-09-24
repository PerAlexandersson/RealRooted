import RealRooted.BrandenLeite.KernelClosure
import RealRooted.BrandenLeite.OptionalRiseMatrix

/-!
# Positive-diagonal regularization of marked lower shifts

This file assembles the finite kernel `L * S ^ r` from an ordered optional-rise
product `L` and the lower shift `S`.  Replacing `S` by the lower-bidiagonal
matrix with diagonal `ε` gives the positive-diagonal TN approximation required
by the finite kernel-limit theorem.
-/

open Filter Matrix Topology

namespace RealRooted.BrandenLeite

noncomputable section

/-- The lower shift with a constant regularizing diagonal `ε`. -/
def regularizedLowerShift (ε : ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.lowerBidiagonalFin (N + 1) (fun _ => ε) (fun _ => 1)

@[simp]
theorem regularizedLowerShift_apply
    (ε : ℝ) (N : ℕ) (i j : Fin (N + 1)) :
    regularizedLowerShift ε N i j =
      if i = j then ε else if i.val = j.val + 1 then 1 else 0 := by
  simp [regularizedLowerShift]

@[simp]
theorem regularizedLowerShift_zero (N : ℕ) :
    regularizedLowerShift 0 N = lowerShift N := by
  ext i j
  rw [regularizedLowerShift_apply]
  change (if i = j then 0 else if i.val = j.val + 1 then 1 else 0) =
    if i.val = j.val + 1 then 1 else 0
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The regularized shift is lower triangular. -/
theorem regularizedLowerShift_apply_eq_zero_of_lt
    (ε : ℝ) (N : ℕ) {i j : Fin (N + 1)} (h : i < j) :
    regularizedLowerShift ε N i j = 0 := by
  rw [regularizedLowerShift_apply]
  have hij : i ≠ j := ne_of_lt h
  have hsucc : i.val ≠ j.val + 1 := by lia
  simp [hij, hsucc]

@[simp]
theorem regularizedLowerShift_apply_self
    (ε : ℝ) (N : ℕ) (i : Fin (N + 1)) :
    regularizedLowerShift ε N i i = ε := by
  simp

/-- A nonnegative regularizing diagonal preserves total nonnegativity. -/
theorem regularizedLowerShift_isTotallyNonneg
    {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    (regularizedLowerShift ε N).IsTotallyNonneg := by
  exact Matrix.isTotallyNonneg_lowerBidiagonalFin
    (N + 1) (fun _ => ε) (fun _ => 1) (by simp [hε]) (by simp)

/-- Powers of the regularized shift remain lower triangular. -/
theorem regularizedLowerShift_pow_apply_eq_zero_of_lt
    (ε : ℝ) (N r : ℕ) {i j : Fin (N + 1)} (h : i < j) :
    (regularizedLowerShift ε N ^ r) i j = 0 := by
  induction r generalizing i j with
  | zero => simp [ne_of_lt h]
  | succ r ih =>
      rw [pow_succ]
      exact Matrix.mul_apply_eq_zero_of_lt_of_upper_zero
        (regularizedLowerShift ε N ^ r) (regularizedLowerShift ε N)
        (fun i j hij => ih hij)
        (fun i j hij => regularizedLowerShift_apply_eq_zero_of_lt ε N hij) h

/-- The diagonal of the `r`th regularized-shift power is `ε^r`. -/
theorem regularizedLowerShift_pow_apply_self
    (ε : ℝ) (N r : ℕ) (i : Fin (N + 1)) :
    (regularizedLowerShift ε N ^ r) i i = ε ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ,
        Matrix.mul_apply_self_of_upper_zero
          (regularizedLowerShift ε N ^ r) (regularizedLowerShift ε N)
          (fun i j hij =>
            regularizedLowerShift_pow_apply_eq_zero_of_lt ε N r hij)
          (fun i j hij =>
            regularizedLowerShift_apply_eq_zero_of_lt ε N hij),
        ih, regularizedLowerShift_apply_self, pow_succ]

/-- Powers of a nonnegative regularized shift are totally nonnegative. -/
theorem regularizedLowerShift_pow_isTotallyNonneg
    {ε : ℝ} (hε : 0 ≤ ε) (N r : ℕ) :
    (regularizedLowerShift ε N ^ r).IsTotallyNonneg := by
  induction r with
  | zero =>
      exact optionalRiseMatrix_isTotallyNonneg (as := []) (by simp) N
  | succ r ih =>
      rw [pow_succ]
      exact ih.mul (regularizedLowerShift_isTotallyNonneg hε N)

/-- The limiting marked kernel `L * S^r`. -/
def markedShiftKernel (as : List (ℕ → ℝ)) (N r : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  optionalRiseMatrix as N * lowerShift N ^ r

/-- The positive-diagonal approximation `L * (S + ε I)^r`. -/
def markedShiftApproximation
    (as : List (ℕ → ℝ)) (N r : ℕ) (ε : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  optionalRiseMatrix as N * regularizedLowerShift ε N ^ r

@[simp]
theorem markedShiftApproximation_zero
    (as : List (ℕ → ℝ)) (N r : ℕ) :
    markedShiftApproximation as N r 0 = markedShiftKernel as N r := by
  simp [markedShiftApproximation, markedShiftKernel]

/-- The limiting marked kernel has the sharp displacement support. -/
theorem markedShiftKernel_apply_eq_zero_of_lt_add
    (as : List (ℕ → ℝ)) (N r : ℕ) {i j : Fin (N + 1)}
    (h : i.val < j.val + r) :
    markedShiftKernel as N r i j = 0 := by
  exact Matrix.mul_pow_apply_eq_zero_of_lt_add_of_lower_strictLower
    (optionalRiseMatrix as N) (lowerShift N)
    (fun i j hij => optionalRiseMatrix_apply_eq_zero_of_lt as N
      (Fin.mk_lt_mk.mp hij))
    (fun i j hij => weightedLowerShift_apply_eq_zero_of_le
      (fun _ => (1 : ℝ)) N hij) h

/-- Positive mark order makes the limiting marked kernel strictly lower. -/
theorem markedShiftKernel_apply_eq_zero_of_le
    (as : List (ℕ → ℝ)) (N : ℕ) {r : ℕ} (hr : 0 < r)
    {i j : Fin (N + 1)} (h : i.val ≤ j.val) :
    markedShiftKernel as N r i j = 0 := by
  exact markedShiftKernel_apply_eq_zero_of_lt_add as N r (by lia)

/-- Nonnegative optional-rise weights make the marked approximation TN. -/
theorem markedShiftApproximation_isTotallyNonneg
    {as : List (ℕ → ℝ)} (has : ∀ a ∈ as, ∀ n, 0 ≤ a n)
    {ε : ℝ} (hε : 0 ≤ ε) (N r : ℕ) :
    (markedShiftApproximation as N r ε).IsTotallyNonneg := by
  exact (optionalRiseMatrix_isTotallyNonneg has N).mul
    (regularizedLowerShift_pow_isTotallyNonneg hε N r)

/-- Every marked approximation is lower triangular. -/
theorem markedShiftApproximation_apply_eq_zero_of_lt
    (as : List (ℕ → ℝ)) (N r : ℕ) (ε : ℝ)
    {i j : Fin (N + 1)} (h : i < j) :
    markedShiftApproximation as N r ε i j = 0 := by
  exact Matrix.mul_apply_eq_zero_of_lt_of_upper_zero
    (optionalRiseMatrix as N) (regularizedLowerShift ε N ^ r)
    (fun i j hij => optionalRiseMatrix_apply_eq_zero_of_lt as N
      (Fin.mk_lt_mk.mp hij))
    (fun i j hij =>
      regularizedLowerShift_pow_apply_eq_zero_of_lt ε N r hij) h

/-- The marked approximation has the constant diagonal `ε^r`. -/
theorem markedShiftApproximation_apply_self
    (as : List (ℕ → ℝ)) (N r : ℕ) (ε : ℝ) (i : Fin (N + 1)) :
    markedShiftApproximation as N r ε i i = ε ^ r := by
  rw [markedShiftApproximation,
    Matrix.mul_apply_self_of_upper_zero
      (optionalRiseMatrix as N) (regularizedLowerShift ε N ^ r)
      (fun i j hij => optionalRiseMatrix_apply_eq_zero_of_lt as N
        (Fin.mk_lt_mk.mp hij))
      (fun i j hij =>
        regularizedLowerShift_pow_apply_eq_zero_of_lt ε N r hij),
    optionalRiseMatrix_apply_self,
    regularizedLowerShift_pow_apply_self, one_mul]

/-- The explicit positive regularization sequence `1 / (m + 1)`. -/
def markedShiftEpsilon (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1)

theorem markedShiftEpsilon_pos (m : ℕ) :
    0 < markedShiftEpsilon m := by
  rw [markedShiftEpsilon, one_div]
  exact inv_pos.mpr (by positivity)

theorem tendsto_markedShiftEpsilon :
    Tendsto markedShiftEpsilon atTop (𝓝 0) := by
  unfold markedShiftEpsilon
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The regularized lower shifts converge entrywise to the strict lower
shift along the explicit positive sequence. -/
theorem tendsto_regularizedLowerShift (N : ℕ) :
    Tendsto (fun m => regularizedLowerShift (markedShiftEpsilon m) N)
      atTop (𝓝 (lowerShift N)) := by
  rw [← regularizedLowerShift_zero]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i = j
  · simpa [regularizedLowerShift_apply, hij] using
      tendsto_markedShiftEpsilon
  · by_cases hsucc : i.val = j.val + 1
    · simp [regularizedLowerShift_apply, hij, hsucc]
    · simp [regularizedLowerShift_apply, hij, hsucc]

/-- The marked approximations converge entrywise to the marked strict kernel. -/
theorem tendsto_markedShiftApproximation
    (as : List (ℕ → ℝ)) (N r : ℕ) (i j : Fin (N + 1)) :
    Tendsto
      (fun m => markedShiftApproximation as N r (markedShiftEpsilon m) i j)
      atTop (𝓝 (markedShiftKernel as N r i j)) := by
  have hpow := (tendsto_regularizedLowerShift N).pow r
  have hmul : Tendsto
      (fun m => optionalRiseMatrix as N *
        regularizedLowerShift (markedShiftEpsilon m) N ^ r)
      atTop (𝓝 (optionalRiseMatrix as N * lowerShift N ^ r)) :=
    tendsto_const_nhds.mul hpow
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmul i) j

@[simp]
theorem markedShiftKernel_nil (N r : ℕ) :
    markedShiftKernel [] N r = lowerShift N ^ r := by
  simp [markedShiftKernel]

/-- A mark order larger than every available level annihilates the finite
marked kernel. -/
theorem markedShiftKernel_eq_zero_of_lt
    (as : List (ℕ → ℝ)) {N r : ℕ} (hNr : N < r) :
    markedShiftKernel as N r = 0 := by
  ext i j
  apply markedShiftKernel_apply_eq_zero_of_lt_add
  have hi : i.val ≤ N := by lia
  have hj : 0 ≤ j.val := Nat.zero_le _
  lia

/-- The weighted Green background and marked optional-rise kernel satisfy the
complete finite kernel-limit package: every kernel row is PF and consecutive
rows are in zero-aware proper position. -/
theorem weightedGreenKernel_markedShiftKernel_pf_and_interl
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {as : List (ℕ → ℝ)} (has : ∀ a ∈ as, ∀ n, 0 ≤ a n)
    (N : ℕ) {r : ℕ} (hr : 0 < r) :
    (∀ i, IsPFPolynomial
      (kernelRow (weightedGreenKernel b N) (markedShiftKernel as N r) i)) ∧
    ∀ i : Fin N,
      Interl
        (kernelRow (weightedGreenKernel b N) (markedShiftKernel as N r)
          i.castSucc)
        (kernelRow (weightedGreenKernel b N) (markedShiftKernel as N r)
          i.succ) := by
  apply kernelRows_pf_and_interl_of_tendsto
    (g := 1)
    (η := fun m => markedShiftEpsilon m ^ r)
    (G := weightedGreenKernel b N)
    (H := fun m => markedShiftApproximation as N r (markedShiftEpsilon m))
    (K := markedShiftKernel as N r)
  · norm_num
  · intro m
    exact pow_pos (markedShiftEpsilon_pos m) r
  · exact weightedGreenKernel_isTotallyNonneg hb N
  · intro m
    exact markedShiftApproximation_isTotallyNonneg has
      (markedShiftEpsilon_pos m).le N r
  · intro i j hij
    exact weightedGreenKernel_apply_eq_zero_of_lt b N
      (Fin.mk_lt_mk.mp hij)
  · intro m i j hij
    exact markedShiftApproximation_apply_eq_zero_of_lt as N r
      (markedShiftEpsilon m) hij
  · intro i j hij
    exact markedShiftKernel_apply_eq_zero_of_le as N hr hij
  · exact weightedGreenKernel_apply_self b N
  · intro m
    exact markedShiftApproximation_apply_self as N r (markedShiftEpsilon m)
  · exact tendsto_markedShiftApproximation as N r

@[deprecated weightedGreenKernel_markedShiftKernel_pf_and_interl
  (since := "2026-09-18")]
alias weightedGreenKernel_markedShiftKernel_pf_and_prec0 :=
  weightedGreenKernel_markedShiftKernel_pf_and_interl

end

end RealRooted.BrandenLeite
