module

public import RealRooted.Wronskian.OdeRootExclusion
public import RealRooted.MaWang.DerivativeStep
public import RealRooted.MultiplierSequence.CoefficientRatio
public import RealRooted.Recurrence.RowModel

/-!
# The row polynomials of OEIS A286785

We prove the coefficient ODE and use the Laguerre-discriminant root-exclusion
criterion to place every root below `-1/8`. We then prove the first-order
transition coefficientwise and apply the strict Ma--Wang derivative step.

The row formula is recorded in [OEIS A286785](https://oeis.org/A286785).
The hypergeometric coefficient ratio proves real-rootedness directly; the
ODE and derivative transition supply the stronger root bound and interlacing.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.A286785

/-- The coefficient
`binom(d, k) binom(2d + 4, d + 1 - k) / (d + 2)` of the degree-`d` row. -/
def rowCoeff (d k : ℕ) : ℝ :=
  ((d.choose k * (2 * d + 4).choose (d + 1 - k) : ℕ) : ℝ) / ((d : ℝ) + 2)

/-- The degree-`d` row polynomial associated with OEIS A286785. -/
def rowPoly (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (rowCoeff d k) * X ^ k

/-- Coefficients beyond the degree parameter vanish. -/
lemma rowCoeff_eq_zero (d k : ℕ) (hk : d < k) : rowCoeff d k = 0 := by
  simp [rowCoeff, Nat.choose_eq_zero_of_lt hk]

/-- Every coefficient in the defining range is positive. -/
lemma rowCoeff_pos (d k : ℕ) (hk : k ≤ d) : 0 < rowCoeff d k := by
  unfold rowCoeff
  have hleft : 0 < d.choose k := Nat.choose_pos hk
  have hright : 0 < (2 * d + 4).choose (d + 1 - k) := Nat.choose_pos (by lia)
  positivity

/-- The coefficient of `X^k` in `rowPoly d` is `rowCoeff d k`. -/
theorem coeff_rowPoly (d k : ℕ) : (rowPoly d).coeff k = rowCoeff d k := by
  simp only [rowPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [rowCoeff_eq_zero d k]
    simpa using hk

/-- The row indexed by `d` has degree exactly `d`. -/
theorem rowPoly_natDegree (d : ℕ) : (rowPoly d).natDegree = d := by
  have hupper : (rowPoly d).natDegree ≤ d := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_rowPoly, rowCoeff_eq_zero d k hk]
  exact natDegree_eq_of_le_of_coeff_ne_zero hupper
    (ne_of_gt (by simpa only [coeff_rowPoly] using rowCoeff_pos d d le_rfl))

/-- Every row has positive leading coefficient. -/
theorem rowPoly_leadingCoeff_pos (d : ℕ) : 0 < (rowPoly d).leadingCoeff := by
  rw [leadingCoeff, rowPoly_natDegree, coeff_rowPoly]
  exact rowCoeff_pos d d le_rfl

/-- A row evaluates positively on the nonnegative real axis. -/
theorem rowPoly_eval_pos (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < (rowPoly d).eval x := by
  simp only [rowPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  have hzero := rowCoeff_pos d 0 (Nat.zero_le d)
  have hsum := Finset.single_le_sum (f := fun k ↦ rowCoeff d k * x ^ k)
    (fun k hk => mul_nonneg (rowCoeff_pos d k (by simp at hk; lia)).le (pow_nonneg hx k))
    (Finset.mem_range.mpr (Nat.succ_pos d))
  simp only [pow_zero, mul_one] at hsum
  linarith

/-- The hypergeometric coefficient ratio for a row. -/
theorem rowCoeff_ratio (d k : ℕ) (hk : k ≤ d) :
    ((k : ℝ) + 1) * (d + k + 4) * rowCoeff d (k + 1) =
      ((d : ℝ) - k) * (d + 1 - k) * rowCoeff d k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hleft := Nat.choose_succ_right_eq (k + m) k
  have hright := Nat.choose_succ_right_eq (2 * (k + m) + 4) m
  have hsub₁ : k + m + 1 - (k + 1) = m := by lia
  have hsub₂ : k + m + 1 - k = m + 1 := by lia
  have hsub₃ : k + m - k = m := by lia
  have hsub₄ : 2 * (k + m) + 4 - m = k + m + k + 4 := by lia
  rw [hsub₃] at hleft
  rw [hsub₄] at hright
  unfold rowCoeff
  rw [hsub₁, hsub₂]
  have hleft' :
      ((k + m).choose (k + 1) : ℝ) * (k + 1) =
        ((k + m).choose k : ℝ) * m := by
    exact_mod_cast hleft
  have hright' :
      ((2 * (k + m) + 4).choose (m + 1) : ℝ) * (m + 1) =
        ((2 * (k + m) + 4).choose m : ℝ) * (k + m + k + 4) := by
    exact_mod_cast hright
  push_cast
  have hden : ((k : ℝ) + m + 2) ≠ 0 := by positivity
  field_simp
  linear_combination
    ((2 * (k + m) + 4).choose m : ℝ) * (k + m + k + 4) * hleft' -
      ((k + m).choose k : ℝ) * m * hright'

/-- The hypergeometric coefficient ratio certifies each row as PF. -/
theorem rowPoly_isPF (d : ℕ) : IsPFPolynomial (rowPoly d) := by
  apply isPFPolynomial_of_pochhammer_coeff_ratio
    (a := (d : ℝ) + 4) (b := 2) (d := d) (by positivity) (by norm_num)
    (rowPoly_natDegree d).le
  · simpa only [coeff_rowPoly] using rowCoeff_pos d 0 (Nat.zero_le d)
  · intro k hk
    simp only [coeff_rowPoly]
    convert rowCoeff_ratio d k hk.le using 1 <;> ring

/-- Every A286785 row splits over the reals. -/
theorem rowPoly_splits (d : ℕ) : (rowPoly d).Splits :=
  (rowPoly_isPF d).eq_zero_or_splits.elim (fun h => h ▸ (by simp)) id

/-- The second-order ODE satisfied by every row. -/
theorem rowPoly_ode (d : ℕ) :
    X * (1 - X) * (rowPoly d).derivative.derivative +
      (C ((d : ℝ) + 4) + C (2 * (d : ℝ)) * X) * (rowPoly d).derivative -
      C ((d : ℝ) * (d + 1)) * rowPoly d = 0 := by
  ext k
  have hratio :
      ((k : ℝ) + 1) * (d + k + 4) * rowCoeff d (k + 1) =
        ((d : ℝ) - k) * (d + 1 - k) * rowCoeff d k := by
    by_cases hk : k ≤ d
    · exact rowCoeff_ratio d k hk
    · rw [rowCoeff_eq_zero d k (by lia), rowCoeff_eq_zero d (k + 1) (by lia)]
      simp
  have hexpand :
      X * (1 - X) * (rowPoly d).derivative.derivative +
          (C ((d : ℝ) + 4) + C (2 * (d : ℝ)) * X) *
            (rowPoly d).derivative - C ((d : ℝ) * (d + 1)) * rowPoly d =
        X * (rowPoly d).derivative.derivative -
          X * (X * (rowPoly d).derivative.derivative) +
          C ((d : ℝ) + 4) * (rowPoly d).derivative +
          C (2 * (d : ℝ)) * (X * (rowPoly d).derivative) -
          C ((d : ℝ) * (d + 1)) * rowPoly d := by
    ring
  rw [hexpand]
  rcases k with _ | _ | k
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero,
      coeff_derivative, coeff_rowPoly, coeff_zero] at *
    push_cast at *
    linear_combination hratio
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_X_mul_zero, coeff_derivative, coeff_rowPoly, coeff_zero] at *
    push_cast at *
    linear_combination hratio
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_derivative, coeff_rowPoly, coeff_zero] at *
    push_cast at *
    linear_combination hratio

private lemma discriminant_pos (d : ℕ) {x : ℝ}
    (hleft : -1 / 8 ≤ x) (hright : x ≤ 0) :
    0 < ((d : ℝ) + 4 + 2 * d * x) ^ 2 +
      4 * (x * (1 - x)) * ((d : ℝ) * (d + 1)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : 3 * (d : ℝ) / 4 + 4 ≤ d + 4 + 2 * d * x := by nlinarith
  have hq : -9 / 16 ≤ 4 * (x * (1 - x)) := by nlinarith
  have hb_sq :
      (3 * (d : ℝ) / 4 + 4) ^ 2 ≤ ((d : ℝ) + 4 + 2 * d * x) ^ 2 := by
    have hnonneg : 0 ≤ 3 * (d : ℝ) / 4 + 4 := by positivity
    exact pow_le_pow_left₀ hnonneg hb 2
  have hq_mul :
      -9 / 16 * ((d : ℝ) * (d + 1)) ≤
        4 * (x * (1 - x)) * ((d : ℝ) * (d + 1)) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  nlinarith

/-- Every real root of a splitting A286785 row lies strictly below `-1/8`. -/
theorem isRoot_lt_neg_one_eighth_of_splits (d : ℕ) (hs : (rowPoly d).Splits)
    {r : ℝ} (hr : (rowPoly d).IsRoot r) : r < -1 / 8 := by
  let a : ℝ[X] := X * (1 - X)
  let b : ℝ[X] := C ((d : ℝ) + 4) + C (2 * (d : ℝ)) * X
  apply roots_lt_of_second_order_ode hs (rowPoly_leadingCoeff_pos d)
    (a := a) (b := b) (lam := (d : ℝ) * (d + 1)) (U := 0)
  · simpa only [a, b] using rowPoly_ode d
  · intro x hx
    by_contra hnonpos
    have hx_nonneg : 0 ≤ x := (lt_of_not_ge hnonpos).le
    exact (ne_of_gt (rowPoly_eval_pos d hx_nonneg)) hx.eq_zero
  · intro x hx _
    have hx_neg : x < 0 := by
      by_contra hnonneg
      exact (ne_of_gt (rowPoly_eval_pos d (le_of_not_gt hnonneg))) hx.eq_zero
    simp only [a, eval_mul, eval_X, eval_sub, eval_one]
    nlinarith
  · intro x hx
    simp only [a, b, eval_add, eval_mul, eval_X, eval_sub, eval_one, eval_C]
    exact discriminant_pos d hx.1 hx.2
  · simp only [a, b, eval_add, eval_mul, eval_X, eval_sub, eval_one, eval_C]
    have hzero := rowPoly_eval_pos d (le_refl (0 : ℝ))
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  · exact hr

/-- Polynomial multiplying the derivative in the unnormalized row transition. -/
def derivativeCoeff (d : ℕ) : ℝ[X] :=
  (1 - X) * (C ((8 : ℝ) * d + 20) * X + C ((d : ℝ) + 1))

/-- Polynomial multiplying the row in the unnormalized row transition. -/
def rowCoeffPoly (d : ℕ) : ℝ[X] :=
  C (3 * (5 * (d : ℝ) ^ 2 + 22 * d + 25)) +
    C (6 * ((d : ℝ) + 1) * (2 * d + 5)) * X

/-- Positive scalar on the left side of the row transition. -/
def transitionScale (d : ℕ) : ℝ :=
  2 * ((d : ℝ) + 3) * (2 * d + 5)

private lemma rowCoeff_right (d k : ℕ) (hk : k < d) :
    rowCoeff d (k + 1) =
      rowCoeff d k * ((d : ℝ) - k) * ((d : ℝ) + 1 - k) /
        (((k : ℝ) + 1) * ((d : ℝ) + k + 4)) := by
  apply (eq_div_iff (by positivity)).mpr
  have hratio := rowCoeff_ratio d k hk.le
  linear_combination hratio

private lemma rowCoeff_left (d k : ℕ) (hkpos : 0 < k) (hk : k ≤ d) :
    rowCoeff d (k - 1) =
      rowCoeff d k * (k : ℝ) * ((d : ℝ) + k + 3) /
        (((d : ℝ) - k + 1) * ((d : ℝ) - k + 2)) := by
  have hratio := rowCoeff_ratio d (k - 1) (by lia)
  rw [Nat.cast_sub (by lia : 1 ≤ k)] at hratio
  push_cast at hratio ⊢
  have hindex : k - 1 + 1 = k := by lia
  rw [hindex] at hratio
  have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk
  have hden : ((d : ℝ) - k + 1) * ((d : ℝ) - k + 2) ≠ 0 := by
    positivity
  apply (eq_div_iff hden).mpr
  linear_combination -hratio

private lemma rowCoeff_succ (d k : ℕ) (hk : k ≤ d) :
    rowCoeff (d + 1) k =
      rowCoeff d k * ((d : ℝ) + 1) * (2 * (d : ℝ) + 6) *
          (2 * (d : ℝ) + 5) * ((d : ℝ) + 2) /
        (((d : ℝ) + 1 - k) * ((d : ℝ) + 2 - k) *
          ((d : ℝ) + k + 4) * ((d : ℝ) + 3)) := by
  let leftOld : ℝ := Nat.choose d k
  let leftNew : ℝ := Nat.choose (d + 1) k
  let rightOld : ℝ := Nat.choose (2 * d + 4) (d + 1 - k)
  let rightNew : ℝ := Nat.choose (2 * (d + 1) + 4) (d + 2 - k)
  have hleftNat := Nat.choose_mul_succ_eq d k
  have hleft :
      leftOld * ((d : ℝ) + 1) = leftNew * ((d : ℝ) + 1 - k) := by
    have hcast := congrArg (fun z : ℕ ↦ (z : ℝ)) hleftNat
    dsimp [leftOld, leftNew]
    rw [Nat.cast_mul, Nat.cast_mul] at hcast
    rw [Nat.cast_sub (by lia : k ≤ d + 1)] at hcast
    push_cast at hcast ⊢
    exact hcast
  have hmiddleNat := Nat.choose_mul_succ_eq (2 * d + 4) (d + 1 - k)
  have hmiddle :
      rightOld * (2 * (d : ℝ) + 5) =
        (Nat.choose (2 * d + 5) (d + 1 - k) : ℝ) *
          ((d : ℝ) + k + 4) := by
    have hcast := congrArg (fun z : ℕ ↦ (z : ℝ)) hmiddleNat
    have htop : 2 * d + 4 + 1 = 2 * d + 5 := by lia
    rw [htop] at hcast
    dsimp [rightOld]
    rw [Nat.cast_mul, Nat.cast_mul] at hcast
    rw [Nat.cast_sub (by lia : d + 1 - k ≤ 2 * d + 5)] at hcast
    have hsub :
        (2 * (d : ℝ) + 5) - ((d + 1 - k : ℕ) : ℝ) =
          (d : ℝ) + k + 4 := by
      rw [Nat.cast_sub (by lia : k ≤ d + 1)]
      push_cast
      ring
    push_cast at hcast ⊢
    rw [hsub] at hcast
    exact hcast
  have hrightNat := Nat.add_one_mul_choose_eq (2 * d + 5) (d + 1 - k)
  have hright :
      (2 * (d : ℝ) + 6) *
          (Nat.choose (2 * d + 5) (d + 1 - k) : ℝ) =
        ((d : ℝ) + 2 - k) * rightNew := by
    have hcast := congrArg (fun z : ℕ ↦ (z : ℝ)) hrightNat
    have htop : 2 * d + 5 + 1 = 2 * (d + 1) + 4 := by lia
    have hindex : d + 1 - k + 1 = d + 2 - k := by lia
    rw [htop, hindex] at hcast
    dsimp [rightNew]
    rw [Nat.cast_mul, Nat.cast_mul] at hcast
    rw [Nat.cast_sub (by lia : k ≤ d + 2)] at hcast
    push_cast at hcast ⊢
    convert hcast using 1 <;> ring
  have hden₁ : (d : ℝ) + 1 - k ≠ 0 := by
    have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk
    nlinarith
  have hden₂ : (d : ℝ) + 2 - k ≠ 0 := by
    have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk
    nlinarith
  have hden₃ : (d : ℝ) + k + 4 ≠ 0 := by positivity
  have hden₄ : (d : ℝ) + 3 ≠ 0 := by positivity
  have hleftValue : leftNew =
      leftOld * ((d : ℝ) + 1) / ((d : ℝ) + 1 - k) :=
    (eq_div_iff hden₁).mpr hleft.symm
  have hrightValue : rightNew =
      rightOld * (2 * (d : ℝ) + 5) * (2 * (d : ℝ) + 6) /
        (((d : ℝ) + k + 4) * ((d : ℝ) + 2 - k)) := by
    apply (eq_div_iff (mul_ne_zero hden₃ hden₂)).mpr
    grind
  unfold rowCoeff
  have htop : 2 * (d + 1) + 4 = 2 * d + 6 := by lia
  have hindex : d + 1 + 1 - k = d + 2 - k := by lia
  rw [htop, hindex]
  push_cast
  dsimp [leftOld, leftNew, rightOld, rightNew] at hleftValue hrightValue
  rw [htop] at hrightValue
  have hden_eq : (d : ℝ) + 1 + 2 = (d : ℝ) + 3 := by ring
  rw [hden_eq, hleftValue, hrightValue]
  have hden₅ : (d : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hden₁, hden₂, hden₃, hden₄, hden₅]

private lemma rowCoeff_transition (d k : ℕ) :
    transitionScale d * rowCoeff (d + 1) k =
      ((d : ℝ) + 1) * (k + 1) * rowCoeff d (k + 1) +
        ((7 * (d : ℝ) + 19) * k +
          3 * (5 * (d : ℝ) ^ 2 + 22 * d + 25)) * rowCoeff d k +
        (if 1 ≤ k then
          (-(8 * (d : ℝ) + 20) * ((k : ℝ) - 1) +
            6 * ((d : ℝ) + 1) * (2 * d + 5)) * rowCoeff d (k - 1)
        else 0) := by
  by_cases hd : d = 0
  · subst d
    rcases k with _ | _ | k
    · norm_num [transitionScale, rowCoeff, Nat.choose]
    · norm_num [transitionScale, rowCoeff, Nat.choose]
    · simp only [ite_eq_left (by lia : 1 ≤ k + 2)]
      rw [rowCoeff_eq_zero 1 (k + 2) (by lia),
        rowCoeff_eq_zero 0 (k + 3) (by lia),
        rowCoeff_eq_zero 0 (k + 2) (by lia)]
      have hindex : k + 2 - 1 = k + 1 := by lia
      rw [hindex, rowCoeff_eq_zero 0 (k + 1) (by lia)]
      ring
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  by_cases hk : k ≤ d
  · rw [rowCoeff_succ d k hk]
    by_cases hkzero : k = 0
    · subst k
      rw [ite_eq_right (by lia : ¬1 ≤ 0), rowCoeff_right d 0 hdpos]
      unfold rowCoeff transitionScale
      norm_num
      field_simp
      ring
    · by_cases hklt : k < d
      · rw [ite_eq_left (by lia : 1 ≤ k), rowCoeff_right d k hklt,
          rowCoeff_left d k (by lia) hk]
        have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk
        have hklt' : (k : ℝ) < d := by exact_mod_cast hklt
        unfold transitionScale
        have hden₁ : (k : ℝ) + 1 ≠ 0 := by positivity
        have hden₂ : (d : ℝ) + k + 4 ≠ 0 := by positivity
        have hden₃ : (d : ℝ) + 3 ≠ 0 := by positivity
        have hden₄ : 2 * (d : ℝ) + 5 ≠ 0 := by positivity
        have hden₅ : (d : ℝ) - k + 1 ≠ 0 := by nlinarith
        have hden₆ : (d : ℝ) - k + 2 ≠ 0 := by nlinarith
        have hden₇ : (d : ℝ) + 1 - k ≠ 0 := by nlinarith
        have hden₈ : (d : ℝ) + 2 - k ≠ 0 := by nlinarith
        field_simp [hden₁, hden₂, hden₃, hden₄, hden₅, hden₆,
          hden₇, hden₈]
        ring
      · have hkeq : k = d := by lia
        subst k
        rw [ite_eq_left (by lia : 1 ≤ d), rowCoeff_left d d (by lia) le_rfl]
        have hright : rowCoeff d (d + 1) = 0 := rowCoeff_eq_zero d (d + 1) (by lia)
        rw [hright]
        unfold rowCoeff transitionScale
        norm_num
        field_simp
        ring
  · by_cases hkeq : k = d + 1
    · subst k
      rw [ite_eq_left (by lia : 1 ≤ d + 1)]
      unfold rowCoeff transitionScale
      norm_num [Nat.choose_eq_zero_of_lt]
      field_simp (discharger := positivity)
      ring
    · have hgt : d + 1 < k := by lia
      have hprev : d < k - 1 := by lia
      rw [ite_eq_left (by lia : 1 ≤ k)]
      rw [rowCoeff_eq_zero (d + 1) k hgt,
        rowCoeff_eq_zero d (k + 1) (by lia), rowCoeff_eq_zero d k (by lia),
        rowCoeff_eq_zero d (k - 1) hprev]
      ring

/-- The first-order transition from the degree-`d` row to the degree-`d+1`
row, with denominators cleared. -/
theorem rowPoly_transition (d : ℕ) :
    C (transitionScale d) * rowPoly (d + 1) =
      derivativeCoeff d * (rowPoly d).derivative + rowCoeffPoly d * rowPoly d := by
  have hderivative : derivativeCoeff d =
      C ((d : ℝ) + 1) + C (7 * (d : ℝ) + 19) * X -
        C (8 * (d : ℝ) + 20) * X ^ 2 := by
    apply Polynomial.funext
    intro x
    simp only [derivativeCoeff, eval_mul, eval_sub, eval_one, eval_X, eval_add,
      eval_C, eval_pow]
    ring
  have hexpand :
      derivativeCoeff d * (rowPoly d).derivative + rowCoeffPoly d * rowPoly d =
        C ((d : ℝ) + 1) * (rowPoly d).derivative +
          C (7 * (d : ℝ) + 19) * (X * (rowPoly d).derivative) -
          C (8 * (d : ℝ) + 20) * (X ^ 2 * (rowPoly d).derivative) +
          C (3 * (5 * (d : ℝ) ^ 2 + 22 * d + 25)) * rowPoly d +
          C (6 * ((d : ℝ) + 1) * (2 * d + 5)) * (X * rowPoly d) := by
    rw [hderivative]
    unfold rowCoeffPoly
    ring
  rw [hexpand]
  ext k
  rcases k with _ | _ | k
  · simp only [coeff_C_mul, coeff_add, coeff_sub, coeff_derivative,
      coeff_X_mul_zero, coeff_X_pow_mul', coeff_rowPoly]
    have hstep := rowCoeff_transition d 0
    simp only [ite_eq_right (by lia : ¬1 ≤ 0), Nat.cast_zero, zero_add,
      mul_zero, add_zero] at hstep
    simp only [ite_eq_right (by lia : ¬2 ≤ 0)]
    linear_combination hstep
  · simp only [coeff_C_mul, coeff_add, coeff_sub, coeff_derivative,
      coeff_X_mul, coeff_X_pow_mul', coeff_rowPoly]
    have hstep := rowCoeff_transition d 1
    norm_num at hstep ⊢
    linear_combination hstep
  · simp only [coeff_C_mul, coeff_add, coeff_sub, coeff_derivative,
      coeff_X_mul, coeff_X_pow_mul', coeff_rowPoly]
    have hstep := rowCoeff_transition d (k + 2)
    simp only [ite_eq_left (by lia : 1 ≤ k + 2)] at hstep
    push_cast at hstep ⊢
    ring_nf at hstep ⊢
    exact hstep

/-- The normalized first-order transition used by the Ma--Wang step. -/
theorem rowPoly_succ (d : ℕ) :
    rowPoly (d + 1) =
      C ((transitionScale d)⁻¹) * derivativeCoeff d * (rowPoly d).derivative +
        C ((transitionScale d)⁻¹) * rowCoeffPoly d * rowPoly d := by
  have hscale : transitionScale d ≠ 0 := by
    unfold transitionScale
    positivity
  calc
    rowPoly (d + 1) = C ((transitionScale d)⁻¹) *
        (C (transitionScale d) * rowPoly (d + 1)) := by
      rw [← mul_assoc, ← C_mul]
      simp [hscale]
    _ = C ((transitionScale d)⁻¹) * derivativeCoeff d * (rowPoly d).derivative +
        C ((transitionScale d)⁻¹) * rowCoeffPoly d * rowPoly d := by
      rw [rowPoly_transition]
      ring

/-- A splitting row strictly interlaces the next row. -/
theorem rowPoly_strictInterl_succ_of_splits (d : ℕ) (hs : (rowPoly d).Splits) :
    StrictInterl (rowPoly d) (rowPoly (d + 1)) := by
  let u : ℝ[X] := C ((transitionScale d)⁻¹) * rowCoeffPoly d
  let v : ℝ[X] := C ((transitionScale d)⁻¹) * derivativeCoeff d
  have hrec : rowPoly (d + 1) = u * rowPoly d + v * (rowPoly d).derivative := by
    rw [rowPoly_succ]
    simp only [u, v]
    ring
  have hv : ∀ r, (rowPoly d).IsRoot r → v.eval r ≤ 0 := by
    intro r hr
    have hr_bound := isRoot_lt_neg_one_eighth_of_splits d hs hr
    have hscale_pos : 0 < transitionScale d := by
      unfold transitionScale
      positivity
    simp only [v, derivativeCoeff, eval_mul, eval_C, eval_sub, eval_one, eval_X,
      eval_add]
    have hfirst : 0 < 1 - r := by linarith
    have hsecond :
        (8 * (d : ℝ) + 20) * r + ((d : ℝ) + 1) < 0 := by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    exact (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hscale_pos.le)
      (mul_nonpos_of_nonneg_of_nonpos hfirst.le hsecond.le))
  have hstrict := MaWang.strictInterl_derivative_of_nonpos_of_splits hs
    (u := u) (v := v)
    (by rw [← hrec, rowPoly_natDegree, rowPoly_natDegree]; lia)
    (by rw [← hrec, rowPoly_natDegree, rowPoly_natDegree])
    (by rw [← hrec]; exact rowPoly_leadingCoeff_pos (d + 1))
    (rowPoly_leadingCoeff_pos d) hv
  rw [← hrec] at hstrict
  exact hstrict

/-- Every real root of an A286785 row lies strictly below `-1/8`. -/
theorem isRoot_lt_neg_one_eighth (d : ℕ) {r : ℝ}
    (hr : (rowPoly d).IsRoot r) : r < -1 / 8 :=
  isRoot_lt_neg_one_eighth_of_splits d (rowPoly_splits d) hr

/-- Consecutive A286785 rows strictly interlace. -/
theorem rowPoly_strictInterl_succ (d : ℕ) :
    StrictInterl (rowPoly d) (rowPoly (d + 1)) :=
  rowPoly_strictInterl_succ_of_splits d (rowPoly_splits d)

private lemma rowPoly_two :
    rowPoly 2 = 14 + 14 * X + 2 * X ^ 2 := by
  apply Polynomial.funext
  intro x
  norm_num [rowPoly, rowCoeff, Nat.choose,
    Finset.sum_range_succ, Polynomial.eval_finsetSum,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

private lemma rowPoly_three :
    rowPoly 3 = 42 + 72 * X + 27 * X ^ 2 + 2 * X ^ 3 := by
  apply Polynomial.funext
  intro x
  norm_num [rowPoly, rowCoeff, Nat.choose,
    Finset.sum_range_succ, Polynomial.eval_finsetSum,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

/-- The first-order update for the model beginning at degree two. -/
def nextRow (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((transitionScale (n + 2))⁻¹) * derivativeCoeff (n + 2) * p.derivative +
    C ((transitionScale (n + 2))⁻¹) * rowCoeffPoly (n + 2) * p

/-- The degree-two tail of `rowPoly` satisfies `nextRow`. -/
theorem rowPoly_nextRow (n : ℕ) :
    rowPoly (n + 3) = nextRow n (rowPoly (n + 2)) := by
  simpa only [nextRow, Nat.add_assoc] using rowPoly_succ (n + 2)

private lemma tailUpdate_eq_nextRow (n : ℕ) (p : ℝ[X]) :
    (C (((n : ℝ) + 4) / (2 * (n + 6) * (2 * n + 11))) +
          C ((7 * (n : ℝ) + 40) / (2 * (n + 6) * (2 * n + 11))) * X -
          C ((8 * (n : ℝ) + 44) / (2 * (n + 6) * (2 * n + 11))) * X ^ 2) *
        p.derivative +
      (C (3 * (5 * (n : ℝ) ^ 2 + 52 * n + 136) /
            (2 * (n + 6) * (2 * n + 11))) +
          C (6 * ((n : ℝ) + 4) * (2 * n + 11) /
            (2 * (n + 6) * (2 * n + 11))) * X) * p =
      nextRow (n + 1) p := by
  unfold nextRow derivativeCoeff rowCoeffPoly transitionScale
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
    eval_one]
  push_cast
  field_simp (discharger := positivity)
  ring

/-- Sequences with the degree-two A286785 base rows and tail update have
interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 14 + 14 * X + 2 * X ^ 2)
    (hone : P 1 = 42 + 72 * X + 27 * X ^ 2 + 2 * X ^ 3)
    (hrec : ∀ n : ℕ,
      P (n + 2) =
        (C (((n : ℝ) + 4) / (2 * (n + 6) * (2 * n + 11))) +
            C ((7 * (n : ℝ) + 40) / (2 * (n + 6) * (2 * n + 11))) * X -
            C ((8 * (n : ℝ) + 44) / (2 * (n + 6) * (2 * n + 11))) * X ^ 2) *
          (P (n + 1)).derivative +
        (C (3 * (5 * (n : ℝ) ^ 2 + 52 * n + 136) /
              (2 * (n + 6) * (2 * n + 11))) +
            C (6 * ((n : ℝ) + 4) * (2 * n + 11) /
              (2 * (n + 6) * (2 * n + 11))) * X) * P (n + 1))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m : ℕ, P (m + 1) = rowPoly (m + 3) := by
    intro m
    induction m with
    | zero => rw [hone, rowPoly_three]
    | succ m ih =>
        rw [hrec m, ih]
        rw [tailUpdate_eq_nextRow, ← rowPoly_nextRow (m + 1)]
  cases n with
  | zero =>
      rw [hzero, hone, ← rowPoly_two, ← rowPoly_three]
      exact (rowPoly_strictInterl_succ 2).toInterlaces (by
        rw [rowPoly_natDegree, rowPoly_natDegree])
  | succ n =>
      rw [heq n, heq (n + 1)]
      exact (rowPoly_strictInterl_succ (n + 3)).toInterlaces (by
        rw [rowPoly_natDegree, rowPoly_natDegree])

end RealRooted.A286785
