module

public import RealRooted.MaWang.DerivativeStep
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.Wronskian.OdeRootExclusion

/-!
# The row polynomials of OEIS A110608

We derive the hypergeometric differential equation, use the
Laguerre-discriminant root-exclusion theorem to obtain the sharp moving root
bound, and apply the strict Ma--Wang derivative step to the corrected
first-order recurrence.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS.A110608

/-- The coefficient `C(N, k) C(2N, N-k)` of the degree-`N` model row. -/
def coefficient (N k : ℕ) : ℝ :=
  (N.choose k : ℝ) * (2 * N).choose (N - k)

/-- The degree-`N` hypergeometric model row for OEIS A110608. -/
def polynomial (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C (coefficient N k) * X ^ k

/-- Coefficients beyond the degree parameter vanish. -/
lemma coefficient_eq_zero (N k : ℕ) (hk : N < k) : coefficient N k = 0 := by
  simp [coefficient, Nat.choose_eq_zero_of_lt hk]

/-- Every coefficient in the defining range is positive. -/
lemma coefficient_pos (N k : ℕ) (hk : k ≤ N) : 0 < coefficient N k := by
  unfold coefficient
  have hleft : 0 < N.choose k := Nat.choose_pos hk
  have hright : 0 < (2 * N).choose (N - k) := Nat.choose_pos (by lia)
  positivity

/-- The coefficient of `X^k` in the model row is the binomial product. -/
theorem coeff_polynomial (N k : ℕ) : (polynomial N).coeff k = coefficient N k := by
  simp only [polynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [coefficient_eq_zero N k]
    simpa using hk

/-- The model row indexed by `N` has degree exactly `N`. -/
theorem polynomial_natDegree (N : ℕ) : (polynomial N).natDegree = N := by
  have hupper : (polynomial N).natDegree ≤ N := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_polynomial, coefficient_eq_zero N k hk]
  exact natDegree_eq_of_le_of_coeff_ne_zero hupper
    (ne_of_gt (by simpa only [coeff_polynomial] using coefficient_pos N N le_rfl))

/-- Every model row has positive leading coefficient. -/
theorem polynomial_leadingCoeff_pos (N : ℕ) :
    0 < (polynomial N).leadingCoeff := by
  rw [leadingCoeff, polynomial_natDegree, coeff_polynomial]
  exact coefficient_pos N N le_rfl

/-- A model row evaluates positively on the nonnegative real axis. -/
theorem polynomial_eval_pos (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < (polynomial N).eval x := by
  simp only [polynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  have hzero := coefficient_pos N 0 (Nat.zero_le N)
  have hsum := Finset.single_le_sum (f := fun k ↦ coefficient N k * x ^ k)
    (fun k hk => mul_nonneg (coefficient_pos N k (by simp at hk; lia)).le
      (pow_nonneg hx k))
    (Finset.mem_range.mpr (Nat.succ_pos N))
  simp only [pow_zero, mul_one] at hsum
  linarith

private lemma coefficient_right (N k : ℕ) (hk : k < N) :
    coefficient N (k + 1) =
      coefficient N k * ((N - k : ℕ) : ℝ) ^ 2 /
        (((k + 1 : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ)) := by
  have hleft := Nat.cast_choose_succ_right_eq (R := ℝ) N k
  rw [Nat.cast_sub hk.le] at hleft
  have hright := Nat.cast_choose_succ_right_eq (R := ℝ) (2 * N) (N - k - 1)
  rw [show N - k - 1 + 1 = N - k by lia,
    Nat.cast_sub (by lia : N - k - 1 ≤ 2 * N)] at hright
  have hsucc : (((N - k - 1 : ℕ) : ℝ)) + 1 = ((N - k : ℕ) : ℝ) := by
    simp_all
  have hsub : (2 * N : ℝ) - ((N - k - 1 : ℕ) : ℝ) = (N + k + 1 : ℕ) := by
    rw [Nat.cast_sub (by lia : 1 ≤ N - k), Nat.cast_sub hk.le]
    grind
  rw [hsucc] at hright
  norm_num [Nat.cast_mul] at hright
  rw [hsub] at hright
  have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by grind
  rw [hcast] at hright
  norm_num [Nat.cast_add] at hright
  have hprod :
      coefficient N (k + 1) *
          (((k + 1 : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ)) =
        coefficient N k * ((N - k : ℕ) : ℝ) ^ 2 := by
    unfold coefficient
    grind
  have hne : (((k + 1 : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  grind

/-- The hypergeometric coefficient ratio for a model row. -/
theorem coefficient_ratio (N k : ℕ) (hk : k ≤ N) :
    ((k : ℝ) + 1) * (N + k + 1) * coefficient N (k + 1) =
      ((N : ℝ) - k) ^ 2 * coefficient N k := by
  by_cases hstrict : k < N
  · rw [coefficient_right N k hstrict]
    have h₁ : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h₂ : ((N + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by
      rw [Nat.cast_sub hstrict.le]
    rw [hcast]
    push_cast
    field_simp [h₁, h₂]
  · have hkeq : k = N := by lia
    subst k
    rw [coefficient_eq_zero N (N + 1) (by lia)]
    simp

/-- The second-order differential equation satisfied by every model row. -/
theorem polynomial_ode (N : ℕ) :
    X * (1 - X) * (polynomial N).derivative.derivative +
      (C ((N : ℝ) + 1) + C (2 * (N : ℝ) - 1) * X) *
        (polynomial N).derivative - C ((N : ℝ) ^ 2) * polynomial N = 0 := by
  ext k
  have hratio :
      ((k : ℝ) + 1) * (N + k + 1) * coefficient N (k + 1) =
        ((N : ℝ) - k) ^ 2 * coefficient N k := by
    by_cases hk : k ≤ N
    · exact coefficient_ratio N k hk
    · rw [coefficient_eq_zero N k (by lia),
        coefficient_eq_zero N (k + 1) (by lia)]
      simp
  have hexpand :
      X * (1 - X) * (polynomial N).derivative.derivative +
          (C ((N : ℝ) + 1) + C (2 * (N : ℝ) - 1) * X) *
            (polynomial N).derivative - C ((N : ℝ) ^ 2) * polynomial N =
        X * (polynomial N).derivative.derivative -
          X * (X * (polynomial N).derivative.derivative) +
          C ((N : ℝ) + 1) * (polynomial N).derivative +
          C (2 * (N : ℝ) - 1) * (X * (polynomial N).derivative) -
          C ((N : ℝ) ^ 2) * polynomial N := by
    ring
  rw [hexpand]
  rcases k with _ | _ | k
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero,
      coeff_derivative, coeff_polynomial, coeff_zero] at *
    push_cast at *
    linear_combination hratio
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_X_mul_zero, coeff_derivative, coeff_polynomial, coeff_zero] at *
    push_cast at *
    linear_combination hratio
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_derivative, coeff_polynomial, coeff_zero] at *
    push_cast at *
    linear_combination hratio

private lemma discriminant_pos (N : ℕ) (hN : 0 < N) {x : ℝ}
    (hleft : -((N : ℝ) + 1) / (8 * N + 5) ≤ x) (hright : x ≤ 0) :
    0 < ((N : ℝ) + 1 + (2 * N - 1) * x) ^ 2 +
      4 * (x * (1 - x)) * (N : ℝ) ^ 2 := by
  let n : ℝ := N
  let L : ℝ := -(n + 1) / (8 * n + 5)
  let A : ℝ := 1 - 4 * n
  let B : ℝ := 8 * n ^ 2 + 2 * n - 2
  let D : ℝ → ℝ := fun y ↦ (n + 1) ^ 2 + B * y + A * y ^ 2
  have hnNat : 1 ≤ N := hN
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast hnNat
  have hden : 0 < 8 * n + 5 := by positivity
  have hLneg : L < 0 := by
    dsimp [L]
    exact div_neg_of_neg_of_pos (by nlinarith) hden
  have hA : A ≤ 0 := by
    dsimp [A]
    linarith
  have hnprod : 0 ≤ n * (n - 1) := mul_nonneg (by positivity) (by linarith)
  have hB : 0 < B := by
    dsimp [B]
    nlinarith
  have hD_formula (y : ℝ) :
      D y = (n + 1 + (2 * n - 1) * y) ^ 2 +
        4 * (y * (1 - y)) * n ^ 2 := by
    dsimp [D, A, B]
    ring
  have hDL :
      D L = 12 * (n + 1) * (7 * n ^ 2 + 9 * n + 3) / (8 * n + 5) ^ 2 := by
    dsimp [D, L, A, B]
    field_simp
    ring
  have hDLpos : 0 < D L := by
    rw [hDL]
    positivity
  have hxL : L ≤ x := by simpa only [n, L] using hleft
  have hsecond : 0 ≤ B + A * (x + L) := by
    have hxsum : x + L ≤ 0 := by linarith
    have hprod : 0 ≤ A * (x + L) := mul_nonneg_of_nonpos_of_nonpos hA hxsum
    linarith
  have hdiff : D x - D L = (x - L) * (B + A * (x + L)) := by
    dsimp [D]
    ring
  have hDle : D L ≤ D x := by
    have hmul : 0 ≤ (x - L) * (B + A * (x + L)) :=
      mul_nonneg (sub_nonneg.mpr hxL) hsecond
    nlinarith [hdiff]
  rw [← hD_formula]
  exact hDLpos.trans_le hDle

/-- Every root of a splitting model row lies below the moving barrier
`-(N+1)/(8N+5)`. -/
theorem isRoot_lt_barrier_of_splits (N : ℕ) (hs : (polynomial N).Splits)
    {r : ℝ} (hr : (polynomial N).IsRoot r) :
    r < -((N : ℝ) + 1) / (8 * N + 5) := by
  by_cases hNzero : N = 0
  · subst N
    have hpoly_ne : polynomial 0 ≠ 0 := by
      intro hzero
      have hpos := polynomial_leadingCoeff_pos 0
      rw [hzero] at hpos
      simp at hpos
    have hdegree_pos : 0 < (polynomial 0).degree := degree_pos_of_root hpoly_ne hr
    have hnatDegree_pos : 0 < (polynomial 0).natDegree :=
      natDegree_pos_iff_degree_pos.mpr hdegree_pos
    rw [polynomial_natDegree] at hnatDegree_pos
    simp at hnatDegree_pos
  · have hN : 0 < N := Nat.pos_of_ne_zero hNzero
    let a : ℝ[X] := X * (1 - X)
    let b : ℝ[X] := C ((N : ℝ) + 1) + C (2 * (N : ℝ) - 1) * X
    apply roots_lt_of_second_order_ode hs (polynomial_leadingCoeff_pos N)
      (a := a) (b := b) (lam := (N : ℝ) ^ 2) (U := 0)
    · simpa only [a, b] using polynomial_ode N
    · intro x hx
      by_contra hnonpos
      have hx_nonneg : 0 ≤ x := (lt_of_not_ge hnonpos).le
      exact (ne_of_gt (polynomial_eval_pos N hx_nonneg)) hx.eq_zero
    · intro x hx _
      have hx_neg : x < 0 := by
        by_contra hnonneg
        exact (ne_of_gt (polynomial_eval_pos N (le_of_not_gt hnonneg))) hx.eq_zero
      simp only [a, eval_mul, eval_X, eval_sub, eval_one]
      nlinarith
    · intro x hx
      simp only [a, b, eval_add, eval_mul, eval_X, eval_sub, eval_one, eval_C]
      exact discriminant_pos N hN hx.1 hx.2
    · simp only [a, b, eval_add, eval_mul, eval_X, eval_sub, eval_one, eval_C]
      have hzero := polynomial_eval_pos N (le_refl (0 : ℝ))
      have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    · exact hr

private lemma coefficient_succ (N k : ℕ) (hk : k ≤ N) :
    coefficient (N + 1) k =
      2 * coefficient N k * (N + 1 : ℝ) ^ 2 * (2 * N + 1 : ℝ) /
        (((N + 1 - k : ℕ) : ℝ) ^ 2 * (N + k + 1 : ℝ)) := by
  let A : ℝ := Nat.choose N k
  let E : ℝ := Nat.choose (N + 1) k
  let U : ℝ := Nat.choose (2 * N) (N - k)
  let F : ℝ := Nat.choose (2 * (N + 1)) (N + 1 - k)
  have hE0 := Nat.choose_mul_succ_eq N k
  have hE :
      A * (N + 1 : ℝ) = E * ((N + 1 - k : ℕ) : ℝ) := by
    simpa [A, E, Nat.cast_mul] using congrArg (fun z : ℕ => (z : ℝ)) hE0
  have hU0 := Nat.choose_mul_succ_eq (2 * N) (N - k)
  have hU :
      U * (2 * N + 1 : ℝ) =
        (Nat.choose (2 * N + 1) (N - k) : ℝ) *
          ((2 * N + 1 - (N - k) : ℕ) : ℝ) := by
    simpa [U, Nat.cast_mul] using congrArg (fun z : ℕ => (z : ℝ)) hU0
  have hF0 := Nat.add_one_mul_choose_eq (2 * N + 1) (N - k)
  have hF :
      (2 * N + 2 : ℝ) * (Nat.choose (2 * N + 1) (N - k) : ℝ) =
        ((N - k + 1 : ℕ) : ℝ) * F := by
    have hF' := congrArg (fun z : ℕ ↦ (z : ℝ)) hF0
    grind
  have hsub₁ : 2 * N + 1 - (N - k) = N + k + 1 := by lia
  have hsub₂ : N - k + 1 = N + 1 - k := by lia
  rw [hsub₁] at hU
  rw [hsub₂] at hF
  have hne₁ : (((N + 1 - k : ℕ) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by lia)
  have hne₂ : (((N + k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hEval : E = A * (N + 1 : ℝ) / ((N + 1 - k : ℕ) : ℝ) :=
    (eq_div_iff hne₁).2 hE.symm
  have hFval :
      F = U * (2 * N + 1 : ℝ) * (2 * N + 2 : ℝ) /
        (((N + 1 - k : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ)) := by
    grind
  unfold coefficient
  change E * F =
    2 * (A * U) * (N + 1 : ℝ) ^ 2 * (2 * N + 1 : ℝ) /
      (((N + 1 - k : ℕ) : ℝ) ^ 2 * (N + k + 1 : ℝ))
  rw [hEval, hFval]
  push_cast
  field_simp [hne₁, hne₂]

private lemma coefficient_left (N k : ℕ) (hkpos : 0 < k) (hk : k ≤ N) :
    coefficient N (k - 1) =
      coefficient N k * (k : ℝ) * (N + k : ℝ) /
        (((N - k + 1 : ℕ) : ℝ) ^ 2) := by
  have hleft := Nat.cast_choose_succ_right_eq (R := ℝ) N (k - 1)
  rw [show k - 1 + 1 = k by lia, Nat.cast_sub (by lia : k - 1 ≤ N)] at hleft
  have hright := Nat.cast_choose_succ_right_eq (R := ℝ) (2 * N) (N - k)
  rw [Nat.cast_sub (by lia : N - k ≤ 2 * N)] at hright
  have hsucc : (((N - k : ℕ) : ℝ)) + 1 = ((N - k + 1 : ℕ) : ℝ) := by simp
  have hsub : (2 * N : ℝ) - ((N - k : ℕ) : ℝ) = (N + k : ℕ) := by
    rw [Nat.cast_sub hk]
    grind
  rw [hsucc] at hright
  norm_num [Nat.cast_mul] at hright
  rw [hsub] at hright
  have hkcast : (((k - 1 : ℕ) : ℝ)) + 1 = (k : ℝ) := by simp_all
  have hdiff : (N : ℝ) - ((k - 1 : ℕ) : ℝ) = ((N - k + 1 : ℕ) : ℝ) := by
    grind
  rw [hkcast, hdiff] at hleft
  have hsub₁ : ((N - k + 1 : ℕ) : ℝ) = (N : ℝ) - k + 1 := by simp_all
  rw [hsub₁] at hleft
  have hsub₀ : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by simp_all
  rw [hsub₀] at hright
  norm_num [Nat.cast_add] at hright
  have hprod :
      coefficient N (k - 1) * (((N - k + 1 : ℕ) : ℝ) ^ 2) =
        coefficient N k * (k : ℝ) * (N + k : ℝ) := by
    unfold coefficient
    grind
  have hne : (((N - k + 1 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  grind

private lemma coefficient_step (N k : ℕ) (hN : 0 < N) :
    coefficient (N + 1) k =
      (1 / (2 * (2 * N + 1 : ℝ))) * (k + 1 : ℝ) * coefficient N (k + 1) +
        (((7 * N + 4 : ℕ) : ℝ) /
              (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ)) * (k : ℝ) +
          ((3 * N + 2 : ℕ) : ℝ) * ((5 * N + 2 : ℕ) : ℝ) /
              (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) * coefficient N k +
        (if 1 ≤ k then
          (-((8 * N + 5 : ℕ) : ℝ) /
                (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ)) * ((k : ℝ) - 1) +
            ((3 * N + 2 : ℕ) : ℝ) * ((4 * N + 1 : ℕ) : ℝ) /
                (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) * coefficient N (k - 1)
        else 0) := by
  by_cases hk : k ≤ N
  · rw [coefficient_succ N k hk]
    by_cases hkz : k = 0
    · subst k
      rw [ite_eq_right (by lia : ¬1 ≤ 0), coefficient_right N 0 hN]
      unfold coefficient
      simp
      field_simp
      ring
    · by_cases hkd : k < N
      · rw [ite_eq_left (by lia : 1 ≤ k), coefficient_right N k hkd,
          coefficient_left N k (by lia) hk]
        have hsub : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by simp_all
        have hsub₁ : ((N - k + 1 : ℕ) : ℝ) = (N : ℝ) - k + 1 := by simp_all
        have hmain : ((N + 1 - k : ℕ) : ℝ) = (N : ℝ) - k + 1 := by
          rw [show N + 1 - k = N - k + 1 by lia, hsub₁]
        rw [hsub, hsub₁, hmain]
        push_cast
        have hneSub : (N : ℝ) - k + 1 ≠ 0 := by grind
        have hneK : (k : ℝ) + 1 ≠ 0 := by positivity
        have hneSum : (N : ℝ) + k + 1 ≠ 0 := by positivity
        have hneN : (N : ℝ) + 1 ≠ 0 := by positivity
        have hneTwoN : 2 * (N : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hneSub, hneK, hneSum, hneN, hneTwoN]
        ring
      · have hkeq : k = N := by lia
        subst k
        rw [ite_eq_left (by lia : 1 ≤ N), coefficient_left N N hN le_rfl]
        have hright : coefficient N (N + 1) = 0 :=
          coefficient_eq_zero N (N + 1) (by lia)
        rw [hright]
        have hone : (((N - N + 1 : ℕ) : ℝ)) = 1 := by norm_num
        have honeMain : (((N + 1 - N : ℕ) : ℝ)) = 1 := by norm_num
        grind
  · by_cases hkeq : k = N + 1
    · subst k
      rw [ite_eq_left (by lia : 1 ≤ N + 1)]
      unfold coefficient
      simp [Nat.choose_eq_zero_of_lt]
      field_simp
      ring
    · have hgt : N + 1 < k := by lia
      have hprev : N < k - 1 := by lia
      rw [ite_eq_left (by lia : 1 ≤ k)]
      unfold coefficient
      have hz₁ : N.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by lia)
      have hz₂ : N.choose k = 0 := Nat.choose_eq_zero_of_lt (by lia)
      have hz₃ : N.choose (k - 1) = 0 := Nat.choose_eq_zero_of_lt hprev
      have hz₀ : (N + 1).choose k = 0 := Nat.choose_eq_zero_of_lt hgt
      simp_all

private lemma polynomial_succ_normalized_of_pos (N : ℕ) (hN : 0 < N) :
    polynomial (N + 1) =
      C (1 / (2 * (2 * N + 1 : ℝ))) * (polynomial N).derivative +
        C (((7 * N + 4 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) *
            (X * (polynomial N).derivative) +
        C (-((8 * N + 5 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) *
            (X ^ 2 * (polynomial N).derivative) +
        C (((3 * N + 2 : ℕ) : ℝ) * ((5 * N + 2 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) * polynomial N +
        C (((3 * N + 2 : ℕ) : ℝ) * ((4 * N + 1 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) * (X * polynomial N) := by
  ext k
  rw [coeff_polynomial]
  simp only [coeff_add, coeff_C_mul, coeff_derivative, coeff_X_pow_mul']
  cases k with
  | zero =>
      simp
      simpa [coeff_polynomial, add_comm, add_left_comm, add_assoc] using
        coefficient_step N 0 hN
  | succ k =>
      simp only [coeff_X_mul]
      rw [coeff_polynomial, coeff_polynomial, coeff_polynomial]
      by_cases hk : k = 0
      · subst k
        rw [ite_eq_right (by lia : ¬2 ≤ 1)]
        rw [coeff_derivative, coeff_polynomial, coeff_polynomial]
        have hstep := coefficient_step N 1 hN
        grind
      · rw [ite_eq_left (by lia : 2 ≤ k + 1)]
        rw [show k + 1 - 2 + 1 = k by lia]
        rw [show ((k + 1 - 2 : ℕ) : ℝ) = (k : ℝ) - 1 by
          rw [Nat.cast_sub (by lia : 2 ≤ k + 1)]
          grind]
        rw [coeff_derivative, coeff_polynomial, coeff_polynomial]
        have hstep := coefficient_step N (k + 1) hN
        grind

private lemma polynomial_zero : polynomial 0 = 1 := by
  ext k
  rw [coeff_polynomial]
  cases k with
  | zero => norm_num [coefficient]
  | succ k => simp [coefficient, coeff_one]

private lemma polynomial_one : polynomial 1 = 2 + X := by
  ext k
  rw [coeff_polynomial]
  rcases k with _ | _ | k
  · norm_num [coefficient]
  · norm_num [coefficient]
  · simp [coefficient, Nat.choose_eq_zero_of_lt, coeff_X]

/-- The corrected normalized derivative recurrence for the model rows. -/
theorem polynomial_succ_normalized (N : ℕ) :
    polynomial (N + 1) =
      C (1 / (2 * (2 * N + 1 : ℝ))) * (polynomial N).derivative +
        C (((7 * N + 4 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) *
            (X * (polynomial N).derivative) +
        C (-((8 * N + 5 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) *
            (X ^ 2 * (polynomial N).derivative) +
        C (((3 * N + 2 : ℕ) : ℝ) * ((5 * N + 2 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) * polynomial N +
        C (((3 * N + 2 : ℕ) : ℝ) * ((4 * N + 1 : ℕ) : ℝ) /
          (2 * (N + 1 : ℝ) * (2 * N + 1 : ℝ))) * (X * polynomial N) := by
  rcases N with _ | N
  · rw [polynomial_zero, polynomial_one]
    norm_num [map_ofNat]
  · exact polynomial_succ_normalized_of_pos (N + 1) (by lia)

/-- The positive scalar cleared in the corrected row transition. -/
def transitionScale (N : ℕ) : ℝ :=
  2 * ((N : ℝ) + 1) * (2 * N + 1)

/-- The polynomial multiplying the derivative in the corrected transition. -/
def derivativeCoeff (N : ℕ) : ℝ[X] :=
  (1 - X) * (C (8 * (N : ℝ) + 5) * X + C ((N : ℝ) + 1))

/-- The polynomial multiplying the row in the corrected transition. -/
def rowCoeffPoly (N : ℕ) : ℝ[X] :=
  C ((3 * (N : ℝ) + 2) * (5 * N + 2)) +
    C ((3 * (N : ℝ) + 2) * (4 * N + 1)) * X

/-- Factored form of the corrected derivative recurrence. -/
theorem polynomial_succ (N : ℕ) :
    polynomial (N + 1) =
      C (transitionScale N)⁻¹ * rowCoeffPoly N * polynomial N +
        C (transitionScale N)⁻¹ * derivativeCoeff N * (polynomial N).derivative := by
  rw [polynomial_succ_normalized]
  apply Polynomial.funext
  intro x
  simp only [transitionScale, derivativeCoeff, rowCoeffPoly, eval_add, eval_mul,
    eval_C, eval_X, eval_sub, eval_one, eval_pow]
  push_cast
  have h₁ : (N : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : 2 * (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [h₁, h₂]
  ring

/-- A splitting model row strictly interlaces the next model row. -/
theorem polynomial_strictInterl_succ_of_splits (N : ℕ) (hs : (polynomial N).Splits) :
    StrictInterl (polynomial N) (polynomial (N + 1)) := by
  let u : ℝ[X] := C (transitionScale N)⁻¹ * rowCoeffPoly N
  let v : ℝ[X] := C (transitionScale N)⁻¹ * derivativeCoeff N
  have hrec : polynomial (N + 1) = u * polynomial N + v * (polynomial N).derivative := by
    rw [polynomial_succ]
  have hv : ∀ r, (polynomial N).IsRoot r → v.eval r ≤ 0 := by
    intro r hr
    have hr_bound := isRoot_lt_barrier_of_splits N hs hr
    have hscale_pos : 0 < transitionScale N := by
      unfold transitionScale
      positivity
    have hleft : 0 < 1 - r := by
      have hbarrier_nonpos : -((N : ℝ) + 1) / (8 * N + 5) < 0 := by
        apply div_neg_of_neg_of_pos
        · have : 0 < (N : ℝ) + 1 := by positivity
          linarith
        · positivity
      linarith
    have hright : (8 * (N : ℝ) + 5) * r + ((N : ℝ) + 1) < 0 := by
      have hden_pos : 0 < 8 * (N : ℝ) + 5 := by positivity
      have hmul := (lt_div_iff₀ hden_pos).mp hr_bound
      nlinarith
    have hvalue :
        v.eval r = (transitionScale N)⁻¹ *
          ((1 - r) * ((8 * (N : ℝ) + 5) * r + ((N : ℝ) + 1))) := by
      simp only [v, derivativeCoeff, eval_mul, eval_add, eval_C, eval_sub, eval_one, eval_X]
    rw [hvalue]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hscale_pos.le)
      (mul_nonpos_of_nonneg_of_nonpos hleft.le hright.le)
  have hstrict := MaWang.strictInterl_derivative_of_nonpos_of_splits hs
    (u := u) (v := v)
    (by rw [← hrec, polynomial_natDegree, polynomial_natDegree]; lia)
    (by rw [← hrec, polynomial_natDegree, polynomial_natDegree])
    (by rw [← hrec]; exact polynomial_leadingCoeff_pos (N + 1))
    (polynomial_leadingCoeff_pos N) hv
  rw [← hrec] at hstrict
  exact hstrict

/-- Every A110608 model row splits over the reals. -/
theorem polynomial_splits : ∀ N : ℕ, (polynomial N).Splits
  | 0 => Splits.of_natDegree_eq_zero (polynomial_natDegree 0)
  | N + 1 =>
      (polynomial_strictInterl_succ_of_splits N (polynomial_splits N)).2.1.2

/-- Consecutive A110608 model rows strictly interlace. -/
theorem polynomial_strictInterl_succ (N : ℕ) :
    StrictInterl (polynomial N) (polynomial (N + 1)) :=
  polynomial_strictInterl_succ_of_splits N (polynomial_splits N)

/-- Consecutive A110608 model rows interlace. -/
theorem polynomial_interlaces (N : ℕ) :
    Interlaces (polynomial N) (polynomial (N + 1)) :=
  (polynomial_strictInterl_succ N).toInterlaces
    (by rw [polynomial_natDegree, polynomial_natDegree])

/-- Every root of a model row lies below its moving barrier. -/
theorem isRoot_lt_barrier (N : ℕ) {r : ℝ} (hr : (polynomial N).IsRoot r) :
    r < -((N : ℝ) + 1) / (8 * N + 5) :=
  isRoot_lt_barrier_of_splits N (polynomial_splits N) hr

/-- The downstream recurrence update, with row `n` corresponding to model
degree `n + 2`. -/
def nextRow (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (C ((1 / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * (3 / 2 + (1 / 2) * n)) +
      C ((1 / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * (9 + (7 / 2) * n)) * X +
      C ((1 / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * (-21 / 2 - 4 * n)) *
        X ^ 2) * p.derivative +
    (C ((1 / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) *
        (18 + 8 * n + (15 / 2) * (2 + (n : ℝ)) ^ 2)) +
      C ((1 / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) *
        (12 + 6 * (2 + (n : ℝ)) ^ 2 + (11 / 2) * n)) * X) * p

/-- The downstream update equals the factored corrected derivative step. -/
theorem nextRow_eq_factored (n : ℕ) (p : ℝ[X]) :
    nextRow n p =
      C (transitionScale (n + 2))⁻¹ * rowCoeffPoly (n + 2) * p +
        C (transitionScale (n + 2))⁻¹ * derivativeCoeff (n + 2) * p.derivative := by
  apply Polynomial.funext
  intro x
  simp only [nextRow, transitionScale, rowCoeffPoly, derivativeCoeff, eval_add,
    eval_mul, eval_C, eval_X, eval_pow, eval_sub, eval_one]
  push_cast
  have hden : 2 * (n : ℝ) ^ 2 + 11 * n + 15 ≠ 0 := by positivity
  field_simp [hden]
  ring

private lemma polynomial_two : polynomial 2 = 6 + 8 * X + X ^ 2 := by
  ext k
  rw [coeff_polynomial]
  rcases k with _ | _ | _ | k
  · norm_num [coefficient, Nat.choose]
  · norm_num [coefficient, Nat.choose]
  · norm_num [coefficient, Nat.choose, coeff_X_pow, coeff_X]
  · simp [coefficient, Nat.choose_eq_zero_of_lt, coeff_X_pow, coeff_X]

private lemma shifted_polynomial_succ (n : ℕ) :
    polynomial (n + 1 + 2) = nextRow n (polynomial (n + 2)) := by
  rw [show n + 1 + 2 = (n + 2) + 1 by lia, polynomial_succ,
    nextRow_eq_factored]

/-- A sequence with the A110608 initial row and corrected derivative
recurrence has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 6 + 8 * X + X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 1) = nextRow n (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (P := P) (Q := fun m => polynomial (m + 2)) nextRow
    (hzero.trans polynomial_two.symm) hrec shifted_polynomial_succ
  rw [heq n]
  exact polynomial_splits (n + 2)

/-- Consecutive rows of a sequence with the A110608 initial row and corrected
derivative recurrence interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 6 + 8 * X + X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 1) = nextRow n (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (P := P) (Q := fun m => polynomial (m + 2)) nextRow
    (hzero.trans polynomial_two.symm) hrec shifted_polynomial_succ
  rw [heq n, heq (n + 1)]
  simpa only [show n + 1 + 2 = (n + 2) + 1 by lia] using
    polynomial_interlaces (n + 2)

end RealRooted.Applications.OEIS.A110608
