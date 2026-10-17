import Mathlib
import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# OEIS A155112

This module defines the OEIS A155112 row polynomials by their recurrence and
proves a Chebyshev closed form. The closed form gives real splitting for every
row, while a recurrence sign invariant places every real root in `(-5, 0]`.

The intended repository destination is
`RealRooted/Applications/OEIS/A155112.lean`.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A155112

/-- Row polynomials of OEIS A155112, `∑_k T(n,k) X^k`, from the g.f.
`(1-x-x²)/(1-(1+y)x-(1+y)x²)`: `R_0 = 1`, `R_1 = X`, `R_2 = X² + 2X` and
`R_{n+3} = (1+X)(R_{n+2} + R_{n+1})`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => X ^ 2 + C 2 * X
  | n + 3 => (1 + X) * (polynomial (n + 2) + polynomial (n + 1))

/-- The defining recurrence for the A155112 row polynomials. -/
theorem polynomial_add_three (n : ℕ) :
    polynomial (n + 3) = (1 + X) * (polynomial (n + 2) + polynomial (n + 1)) := by
  rw [polynomial]

private theorem eval_polynomial_add_three (n : ℕ) (y : ℝ) :
    (polynomial (n + 3)).eval y =
      (1 + y) *
        ((polynomial (n + 2)).eval y + (polynomial (n + 1)).eval y) := by
  rw [polynomial_add_three]
  simp

private theorem coeff_mul_nonneg_aux {p q : ℝ[X]}
    (hp : ∀ k, 0 ≤ p.coeff k) (hq : ∀ k, 0 ≤ q.coeff k)
    (k : ℕ) : 0 ≤ (p * q).coeff k := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

private theorem coeff_one_add_X_nonneg (k : ℕ) :
    0 ≤ ((1 : ℝ[X]) + X).coeff k := by
  rw [coeff_add, coeff_one, coeff_X]
  split_ifs <;> norm_num

private theorem polynomial_coeff_zero_aux (n : ℕ) (hn : 1 ≤ n) :
    (polynomial n).coeff 0 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => lia
    | 1 => simp [polynomial]
    | 2 => simp [polynomial]
    | n + 3 =>
      rw [polynomial_add_three, mul_coeff_zero, coeff_add (polynomial (n + 2)),
        ih (n + 2) (by lia) (by lia), ih (n + 1) (by lia) (by lia)]
      simp

/-! ## Sanity checks (exact) -/

/-- The coefficients are nonnegative. -/
private theorem coeff_nonneg (n k : ℕ) : 0 ≤ (polynomial n).coeff k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [polynomial, coeff_one]
      split_ifs <;> norm_num
    | 1 =>
      simp only [polynomial, coeff_X]
      split_ifs <;> norm_num
    | 2 =>
      simp only [polynomial, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X]
      split_ifs <;> norm_num
    | n + 3 =>
      rw [polynomial_add_three]
      refine coeff_mul_nonneg_aux coeff_one_add_X_nonneg (fun j => ?_) k
      rw [coeff_add]
      exact add_nonneg (ih _ (by lia) _) (ih _ (by lia) _)

/-- Every row (`n ≥ 1`) has the simple root `0`: `R_n = X · Q_n` with `Q_n(0) > 0`. -/
private theorem coeff_one_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < (polynomial n).coeff 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => lia
    | 1 => simp [polynomial]
    | 2 => simp [polynomial]
    | n + 3 =>
      rw [polynomial_add_three, add_mul, one_mul, coeff_add, coeff_X_mul, coeff_add, coeff_add,
        polynomial_coeff_zero_aux _ (by lia),
        polynomial_coeff_zero_aux _ (by lia)]
      have := ih (n + 2) (by lia) (by lia)
      have := ih (n + 1) (by lia) (by lia)
      linarith

/-- **Sign invariant below `-5`.**  For `y ≤ -5`, `(-1)^n R_n(y) > 0` and
`|R_{n+1}(y)| ≥ 2 |R_n(y)|` for `n ≥ 1`
(`R_1 = y`, `R_2 = y² + 2y`, `|R_2| ≥ 2|R_1|` iff `|y| ≥ 4`; and
`|R_{n+2}| = |1+y| (|R_{n+1}| - |R_n|) ≥ 4 · |R_{n+1}|/2`). -/
private theorem sign_invariant (y : ℝ) (hy : y ≤ -5) (n : ℕ)
    (hn : 1 ≤ n) :
    0 < (-1) ^ n * (polynomial n).eval y ∧
      2 * |(polynomial n).eval y| ≤ |(polynomial (n + 1)).eval y| := by
  set a : ℕ → ℝ := fun n => (-1) ^ n * (polynomial n).eval y with ha
  have habs : ∀ n, |(polynomial n).eval y| = |a n| := by
    intro n
    simp only [ha, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have key : ∀ n, 1 ≤ n → 0 < a n ∧ 2 * a n ≤ a (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num [ha, polynomial]
      constructor
      · linarith
      · have hprod : 0 ≤ y * (y + 4) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        nlinarith
    | succ n hn ih =>
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by lia⟩
      refine ⟨by linarith, ?_⟩
      have hrec : a (k + 3) = -(1 + y) * (a (k + 2) - a (k + 1)) := by
        simp only [ha, eval_polynomial_add_three]
        ring
      have h1 : a (k + 2) - a (k + 1) ≥ 0 := by linarith
      have h2 : -(1 + y) ≥ 4 := by linarith
      change 2 * a (k + 2) ≤ a (k + 3)
      rw [hrec]
      nlinarith [mul_le_mul_of_nonneg_right h2 h1]
  obtain ⟨h1, h2⟩ := key n hn
  rw [habs, habs, abs_of_pos h1, abs_of_pos (by linarith)]
  exact ⟨h1, h2⟩

/-- **Root window `(-5, 0]`** for the real roots of every row.  The bound `-5` is sharp: the
smallest roots tend to `-5` (e.g. `n = 12` has a root near `-4.77`). -/
theorem roots_mem_Ioc_polynomial (n : ℕ) {r : ℝ}
    (hr : (polynomial n).IsRoot r) : r ∈ Set.Ioc (-5) 0 := by
  change (polynomial n).eval r = 0 at hr
  change -5 < r ∧ r ≤ 0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [polynomial] at hr
  constructor
  · by_contra h
    push Not at h
    have := (sign_invariant r h n hn).1
    rw [hr, mul_zero] at this
    exact lt_irrefl _ this
  · by_contra h
    push Not at h
    have h1 := coeff_one_pos n hn
    have hdeg : 1 ≤ (polynomial n).natDegree := le_natDegree_of_ne_zero h1.ne'
    have hsum : (polynomial n).coeff 1 * r ^ 1 ≤ (polynomial n).eval r := by
      rw [eval_eq_sum_range]
      exact Finset.single_le_sum (f := fun i => (polynomial n).coeff i * r ^ i)
        (fun i _ => mul_nonneg (coeff_nonneg n i) (pow_nonneg h.le i))
        (Finset.mem_range.mpr (by lia))
    rw [hr] at hsum
    have : 0 < (polynomial n).coeff 1 * r ^ 1 := by positivity
    linarith

/-! ## Chebyshev closed form (auxiliary, for real-rootedness) -/

section Chebyshev

open Real

/-- The affine change of variables `x = (y + 3)/2`. -/
def chebyshevArgument : ℝ[X] := C (1/2) * X + C (3/2)

private theorem two_mul_chebyshevArgument :
    (2 : ℝ[X]) * chebyshevArgument = X + 3 := by
  unfold chebyshevArgument
  rw [show (2:ℝ[X]) = C 2 from (map_ofNat C 2).symm, mul_add, ← mul_assoc, ← C_mul, ← C_mul]
  norm_num
  exact map_ofNat C 3
private theorem U_comp_rec (m : ℕ) :
    (Chebyshev.U ℝ ((m : ℤ) + 2)).comp chebyshevArgument =
      (X + 3) *
          (Chebyshev.U ℝ ((m : ℤ) + 1)).comp chebyshevArgument -
        (Chebyshev.U ℝ m).comp chebyshevArgument := by
  rw [Chebyshev.U_add_two, sub_comp, mul_comp, mul_comp, X_comp, ← two_mul_chebyshevArgument]
  simp

/-- Chebyshev closed forms for the odd and even A155112 rows. -/
theorem polynomial_chebyshev (m : ℕ) :
    polynomial (2 * m + 1) = X * (X + 1) ^ m * (Chebyshev.U ℝ m).comp chebyshevArgument ∧
    polynomial (2 * m + 2) = X * (X + 1) ^ m *
      (Chebyshev.U ℝ ((m : ℤ) + 1) - Chebyshev.U ℝ m).comp chebyshevArgument := by
  induction m with
  | zero =>
    refine ⟨by simp [polynomial], ?_⟩
    simp only [polynomial, Nat.cast_zero, zero_add, Chebyshev.U_one, Chebyshev.U_zero, sub_comp,
      mul_comp, X_comp, one_comp, pow_zero, mul_one]
    have := two_mul_chebyshevArgument
    simp only [ofNat_comp, Nat.cast_ofNat, this]
    rw [show (C 2 : ℝ[X]) = 2 from map_ofNat C 2]
    ring
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : 2 * (m + 1) + 1 = (2 * m) + 3 := by ring
    have e2 : 2 * (m + 1) + 2 = (2 * m + 1) + 3 := by ring
    have hc : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hU := U_comp_rec m
    refine ⟨?_, ?_⟩
    · rw [e1, polynomial_add_three, h2, show 2 * m + 1 = 2 * m + 1 from rfl, h1, hc, sub_comp]
      ring
    · rw [e2, polynomial_add_three, show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 by ring, h2, e1, polynomial_add_three, h2, h1, hc, sub_comp,
        sub_comp, show (m : ℤ) + 1 + 1 = m + 2 by ring, hU]
      ring

private theorem U_splits (m : ℕ) : (Chebyshev.U ℝ m).Splits := by
  rw [splits_iff_card_roots, Chebyshev.roots_U_real, Chebyshev.natDegree_U_natCast,
    Finset.card_val, Finset.card_image_of_injOn
      ((Finset.range m).nodup_map_iff_injOn.mp (Chebyshev.roots_U_real_nodup m)),
    Finset.card_range]

private theorem W_splits (j : ℕ) :
    (Chebyshev.U ℝ ((j : ℤ) + 1) - Chebyshev.U ℝ j).Splits := by
  set W := Chebyshev.U ℝ ((j : ℤ) + 1) - Chebyshev.U ℝ j with hW
  have hdeg : W.natDegree ≤ j + 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by
          push_cast
          ring, Chebyshev.natDegree_U_natCast]
    · rw [Chebyshev.natDegree_U_natCast]; lia
  set θ : ℕ → ℝ := fun k => (2 * k + 1) * π / (2 * j + 3) with hθ
  have hθmem : ∀ k ∈ Finset.range (j + 1), θ k ∈ Set.Icc 0 π := by
    intro k hk
    rw [Finset.mem_range] at hk
    refine ⟨by positivity, ?_⟩
    rw [hθ, div_le_iff₀ (by positivity)]
    have : (k : ℝ) + 1 ≤ j + 1 := by exact_mod_cast hk
    nlinarith [pi_pos]
  have hinj : Set.InjOn (fun k => cos (θ k)) (Finset.range (j + 1)) := by
    refine injOn_cos.comp ?_ hθmem
    intro a _ b _ hab
    simp only [hθ] at hab
    field_simp at hab
    have : (a : ℝ) = b := by nlinarith [pi_pos]
    exact_mod_cast this
  refine splits_of_finset_roots_of_natDegree_le_card
    (s := (Finset.range (j + 1)).image fun k => cos (θ k)) ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hk' : k < j + 1 := Finset.mem_range.mp hk
    have hsin : sin (θ k) ≠ 0 := by
      apply (sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
      rw [hθ, div_lt_iff₀ (by positivity)]
      have hkj : (k : ℝ) + 1 ≤ j + 1 := by exact_mod_cast hk'
      nlinarith [pi_pos]
    have key : W.eval (cos (θ k)) * sin (θ k) = 0 := by
      rw [hW, eval_sub, sub_mul, Chebyshev.U_real_cos,
        Chebyshev.U_real_cos, sin_sub_sin]
      apply mul_eq_zero_of_right
      rw [cos_eq_zero_iff]
      refine ⟨k, ?_⟩
      simp only [hθ]
      push_cast
      field_simp
      ring
    exact (mul_eq_zero.mp key).resolve_right hsin
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    exact hdeg

private theorem comp_chebyshevArgument_splits {p : ℝ[X]}
    (hp : p.Splits) : (p.comp chebyshevArgument).Splits := by
  have h : chebyshevArgument.leadingCoeff = 1 / 2 := by
    unfold chebyshevArgument
    rw [leadingCoeff_linear]
    norm_num
  exact hp.comp_of_natDegree_le_one_of_invertible
    (by
      unfold chebyshevArgument
      exact natDegree_linear_le)
    (h ▸ invertibleOfNonzero (by norm_num))

end Chebyshev

/-- Every row polynomial of OEIS A155112 splits over the reals. -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  obtain ⟨m, rfl | rfl⟩ | rfl : (∃ m, n = 2 * m + 1 ∨ n = 2 * m + 2) ∨ n = 0 := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rcases m with _ | m
      · right; lia
      · left; exact ⟨m, Or.inr (by lia)⟩
    · left; exact ⟨m, Or.inl hm⟩
  · rw [(polynomial_chebyshev m).1]
    exact (Splits.X.mul ((Splits.X_add_C 1).pow m)).mul
      (comp_chebyshevArgument_splits (U_splits m))
  · rw [(polynomial_chebyshev m).2]
    exact (Splits.X.mul ((Splits.X_add_C 1).pow m)).mul
      (comp_chebyshevArgument_splits (W_splits m))
  · simp [polynomial]

end RealRooted.Applications.OEIS.A155112
