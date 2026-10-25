module

public import RealRooted.Basic
public import RealRooted.QuadraticRoot
public import RealRooted.HeilmannLieb

/-!
# Closed forms for repeated-root OEIS rows

This scratch module records the closed-form route for the particularly simple
multiple-root row A286100.  Its even terms are scalar multiples of powers of
`X`, and its odd terms vanish.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.ClosedFormRows

/-- A reciprocal quartic splits when its quadratic factor parameters are at least two. -/
theorem reciprocal_quartic_splits_of_parameters (p q : ℝ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (X ^ 4 + C (p + q) * X ^ 3 + C (p * q + 2) * X ^ 2 + C (p + q) * X + 1 :
      ℝ[X]).Splits := by
  rw [show (X ^ 4 + C (p + q) * X ^ 3 + C (p * q + 2) * X ^ 2 +
      C (p + q) * X + 1 : ℝ[X]) =
      (X ^ 2 + C p * X + 1) * (X ^ 2 + C q * X + 1) by
        apply Polynomial.funext
        intro x
        simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one]
        ring]
  apply Polynomial.Splits.mul
  · simpa using quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := p) (c := 1)
      (by norm_num) (by simp only [discrim]; nlinarith)
  · simpa using quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := q) (c := 1)
      (by norm_num) (by simp only [discrim]; nlinarith)

/-- The square-root parameters of a reciprocal quartic are at least two when
the displayed polynomial inequalities certify the discriminant bound. -/
theorem sqrt_parameters_ge_two_of_certificate (c d : ℝ) (hc : 4 ≤ c)
    (hdisc : 0 ≤ c ^ 2 - 4 * (d - 2))
    (hbound : c ^ 2 - 4 * (d - 2) ≤ (c - 4) ^ 2) :
    2 ≤ (c + Real.sqrt (c ^ 2 - 4 * (d - 2))) / 2 ∧
      2 ≤ (c - Real.sqrt (c ^ 2 - 4 * (d - 2))) / 2 := by
  have hnonneg : 0 ≤ c - 4 := by linarith
  have hsquare : Real.sqrt ((c - 4) ^ 2) = c - 4 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
  have hsqrt : Real.sqrt (c ^ 2 - 4 * (d - 2)) ≤ c - 4 := by
    rw [← hsquare]
    exact Real.sqrt_le_sqrt hbound
  have hsqrt_nonneg : 0 ≤ Real.sqrt (c ^ 2 - 4 * (d - 2)) := Real.sqrt_nonneg _
  have hsquare : Real.sqrt (c ^ 2 - 4 * (d - 2)) ^ 2 = c ^ 2 - 4 * (d - 2) :=
    Real.sq_sqrt hdisc
  constructor <;> rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] <;> linarith

private theorem reciprocal_quartic_splits_of_certificate (c d : ℝ) (hc : 4 ≤ c)
    (hdisc : 0 ≤ c ^ 2 - 4 * (d - 2))
    (hbound : c ^ 2 - 4 * (d - 2) ≤ (c - 4) ^ 2) :
    (X ^ 4 + C c * X ^ 3 + C d * X ^ 2 + C c * X + 1 : ℝ[X]).Splits := by
  obtain ⟨hp, hq⟩ := sqrt_parameters_ge_two_of_certificate c d hc hdisc hbound
  let p := (c + Real.sqrt (c ^ 2 - 4 * (d - 2))) / 2
  let q := (c - Real.sqrt (c ^ 2 - 4 * (d - 2))) / 2
  rw [show (X ^ 4 + C c * X ^ 3 + C d * X ^ 2 + C c * X + 1 : ℝ[X]) =
      X ^ 4 + C (p + q) * X ^ 3 + C (p * q + 2) * X ^ 2 + C (p + q) * X + 1 by
        apply Polynomial.funext
        intro x
        simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one]
        dsimp [p, q]
        ring_nf
        rw [show 8 + c ^ 2 - d * 4 = c ^ 2 - 4 * (d - 2) by ring,
          Real.sq_sqrt hdisc]
        ring]
  exact reciprocal_quartic_splits_of_parameters p q hp hq

/-- The order-four repeated-root row A286100. -/
def A286100 : ℕ → ℝ[X]
  | 0 => 2 * X
  | 1 => 0
  | 2 => 3 * X ^ 2
  | 3 => 0
  | n + 4 => 2 * X * A286100 (n + 2) - X ^ 2 * A286100 n

/-- The even terms of A286100 have the closed form
`(k + 2) X^(k + 1)`. -/
theorem A286100_even_closed (k : ℕ) :
    A286100 (2 * k) = C ((k : ℝ) + 2) * X ^ (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero =>
      simp [A286100, map_ofNat]
  | one =>
      norm_num [A286100, map_ofNat]
  | more k hk hk1 =>
      rw [show 2 * (k + 2) = 2 * k + 4 by ring]
      change 2 * X * A286100 (2 * k + 2) - X ^ 2 * A286100 (2 * k) =
        C (((k + 2 : ℕ) : ℝ) + 2) * X ^ (k + 3)
      rw [show 2 * k + 2 = 2 * (k + 1) by ring, hk1, hk]
      norm_num [map_ofNat]
      ring

/-- The odd terms of A286100 vanish. -/
theorem A286100_odd_closed (k : ℕ) : A286100 (2 * k + 1) = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k hk hk1 =>
      rw [show 2 * (k + 2) + 1 = (2 * k + 1) + 4 by ring]
      change 2 * X * A286100 (2 * k + 3) - X ^ 2 * A286100 (2 * k + 1) = 0
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 by ring, hk1, hk]
      ring

/-- Every A286100 row splits over the reals. -/
theorem A286100_splits (n : ℕ) : (A286100 n).Splits := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hindex : n = 2 * (n / 2) := by lia
    rw [hindex, A286100_even_closed]
    exact Polynomial.Splits.C_mul (Polynomial.Splits.X_pow _) _
  · have hindex : n = 2 * (n / 2) + 1 := by lia
    rw [hindex, A286100_odd_closed]
    simp

/-- The quartic cofactor for A124376. -/
def A124376_quartic (k : ℕ) : ℝ[X] :=
  X ^ 4 + C (2 * (k : ℝ) + 10) * X ^ 3 +
    C ((k : ℝ) ^ 2 / 2 + 11 * (k : ℝ) / 2 + 19) * X ^ 2 +
      C (2 * (k : ℝ) + 10) * X + 1

/-- The two exact quadratic parameters certifying the A124376 quartic. -/
def A124376_parameters (k : ℕ) : ℝ × ℝ :=
  let c := 2 * (k : ℝ) + 10
  let d := (k : ℝ) ^ 2 / 2 + 11 * (k : ℝ) / 2 + 19
  let s := Real.sqrt (c ^ 2 - 4 * (d - 2))
  ((c + s) / 2, (c - s) / 2)

/-- The A124376 quartic cofactor splits over the reals. -/
theorem A124376_quartic_splits (k : ℕ) : (A124376_quartic k).Splits := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [A124376_quartic]
  apply reciprocal_quartic_splits_of_certificate
  · linarith
  · nlinarith [sq_nonneg (k : ℝ)]
  · nlinarith [sq_nonneg (k : ℝ)]

/-- The quartic cofactor for A157169. -/
def A157169_quartic (k : ℕ) : ℝ[X] :=
  X ^ 4 + C (3 * (k : ℝ) + 13) * X ^ 3 +
    C ((k : ℝ) ^ 2 + 9 * (k : ℝ) + 26) * X ^ 2 +
      C (3 * (k : ℝ) + 13) * X + 1

/-- The A157169 quartic cofactor splits over the reals. -/
theorem A157169_quartic_splits (k : ℕ) : (A157169_quartic k).Splits := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [A157169_quartic]
  apply reciprocal_quartic_splits_of_certificate
  · linarith
  · nlinarith [sq_nonneg (k : ℝ)]
  · nlinarith [sq_nonneg (k : ℝ)]

/-- The quartic cofactor for A157171. -/
def A157171_quartic (k : ℕ) : ℝ[X] :=
  X ^ 4 + C (9 * (k : ℝ) + 31) * X ^ 3 +
    C (3 * (k : ℝ) ^ 2 + 27 * (k : ℝ) + 66) * X ^ 2 +
      C (9 * (k : ℝ) + 31) * X + 1

/-- The A157171 quartic cofactor splits over the reals. -/
theorem A157171_quartic_splits (k : ℕ) : (A157171_quartic k).Splits := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [A157171_quartic]
  apply reciprocal_quartic_splits_of_certificate
  · linarith
  · nlinarith [sq_nonneg (k : ℝ)]
  · nlinarith [sq_nonneg (k : ℝ)]

/-- The order-five row A124376, in the recurrence form used downstream. -/
def A124376 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | 3 => 1 + 7 * X + 7 * X ^ 2 + X ^ 3
  | 4 => 1 + 10 * X + 19 * X ^ 2 + 10 * X ^ 3 + X ^ 4
  | n + 5 => (3 + 3 * X) * A124376 (n + 4) + (-3 + -6 * X + -3 * X ^ 2) *
      A124376 (n + 3) + (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A124376 (n + 2)

/-- The recurrence solution for A124376. -/
theorem A124376_closed : ∀ k : ℕ,
    A124376 (k + 4) = (1 + X) ^ k * A124376_quartic k
  | 0 => by norm_num [A124376, A124376_quartic, map_ofNat]; ring
  | 1 => by norm_num [A124376, A124376_quartic, map_ofNat]; ring
  | 2 => by norm_num [A124376, A124376_quartic, map_ofNat]; ring
  | k + 3 => by
      rw [show A124376 (k + 3 + 4) = (3 + 3 * X) * A124376 (k + 6) +
          (-3 + -6 * X + -3 * X ^ 2) * A124376 (k + 5) +
          (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A124376 (k + 4) by
        rw [show k + 3 + 4 = (k + 2) + 5 by ring]
        rfl]
      rw [show k + 6 = (k + 2) + 4 by ring, show k + 5 = (k + 1) + 4 by ring,
        A124376_closed (k + 2), A124376_closed (k + 1), A124376_closed k]
      apply Polynomial.funext
      intro r
      rw [A124376_quartic, A124376_quartic, A124376_quartic, A124376_quartic]
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_neg, eval_ofNat]
      grind

/-- Every A124376 row splits over the reals. -/
theorem A124376_splits (n : ℕ) : (A124376 n).Splits := by
  rcases n with _ | _ | _ | _ | n
  · change (1 : ℝ[X]).Splits
    exact Polynomial.Splits.one
  · rw [show A124376 1 = X + C (1 : ℝ) by
        change 1 + X = X + C (1 : ℝ)
        norm_num [map_ofNat]
        ring]
    exact Polynomial.Splits.X_add_C 1
  · rw [show A124376 2 = X ^ 2 + C (4 : ℝ) * X + 1 by
        change 1 + 4 * X + X ^ 2 = X ^ 2 + C (4 : ℝ) * X + 1
        norm_num [map_ofNat]
        ring]
    simpa only [map_one, one_mul] using
      quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := 4) (c := 1)
        (by norm_num) (by norm_num [discrim])
  · rw [show A124376 3 = (1 + X) * (1 + 6 * X + X ^ 2) by
        simp only [A124376]
        ring]
    apply Polynomial.Splits.mul
    · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      exact Polynomial.Splits.X_add_C 1
    · rw [show (1 + 6 * X + X ^ 2 : ℝ[X]) = X ^ 2 + C (6 : ℝ) * X + 1 by
          norm_num [map_ofNat]
          ring]
      simpa only [map_one, one_mul] using
        quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := 6) (c := 1)
          (by norm_num) (by norm_num [discrim])
  · rw [show n + 4 = n + 4 by rfl, A124376_closed]
    exact (by
      apply Polynomial.Splits.mul
      · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
        exact (Polynomial.Splits.X_add_C 1).pow n
      · exact A124376_quartic_splits n)

/-- The order-five row A157169, in the recurrence form used downstream. -/
def A157169 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | 3 => 1 + 9 * X + 9 * X ^ 2 + X ^ 3
  | 4 => 1 + 13 * X + 26 * X ^ 2 + 13 * X ^ 3 + X ^ 4
  | n + 5 => (3 + 3 * X) * A157169 (n + 4) + (-3 + -6 * X + -3 * X ^ 2) *
      A157169 (n + 3) + (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A157169 (n + 2)

/-- The recurrence solution for A157169. -/
theorem A157169_closed : ∀ k : ℕ,
    A157169 (k + 4) = (1 + X) ^ k * A157169_quartic k
  | 0 => by norm_num [A157169, A157169_quartic, map_ofNat]; ring
  | 1 => by norm_num [A157169, A157169_quartic, map_ofNat]; ring
  | 2 => by norm_num [A157169, A157169_quartic, map_ofNat]; ring
  | k + 3 => by
      rw [show A157169 (k + 3 + 4) = (3 + 3 * X) * A157169 (k + 6) +
          (-3 + -6 * X + -3 * X ^ 2) * A157169 (k + 5) +
          (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A157169 (k + 4) by
        rw [show k + 3 + 4 = (k + 2) + 5 by ring]
        rfl]
      rw [show k + 6 = (k + 2) + 4 by ring, show k + 5 = (k + 1) + 4 by ring,
        A157169_closed (k + 2), A157169_closed (k + 1), A157169_closed k]
      apply Polynomial.funext
      intro r
      rw [A157169_quartic, A157169_quartic, A157169_quartic, A157169_quartic]
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_neg, eval_ofNat]
      grind

/-- Every A157169 row splits over the reals. -/
theorem A157169_splits (n : ℕ) : (A157169 n).Splits := by
  rcases n with _ | _ | _ | _ | n
  · change (1 : ℝ[X]).Splits
    exact Polynomial.Splits.one
  · rw [show A157169 1 = X + C (1 : ℝ) by
        change 1 + X = X + C (1 : ℝ)
        norm_num [map_ofNat]
        ring]
    exact Polynomial.Splits.X_add_C 1
  · rw [show A157169 2 = X ^ 2 + C (5 : ℝ) * X + 1 by
        change 1 + 5 * X + X ^ 2 = X ^ 2 + C (5 : ℝ) * X + 1
        norm_num [map_ofNat]
        ring]
    simpa only [map_one, one_mul] using
      quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := 5) (c := 1)
        (by norm_num) (by norm_num [discrim])
  · rw [show A157169 3 = (1 + X) * (1 + 8 * X + X ^ 2) by
        simp only [A157169]
        ring]
    apply Polynomial.Splits.mul
    · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      exact Polynomial.Splits.X_add_C 1
    · rw [show (1 + 8 * X + X ^ 2 : ℝ[X]) = X ^ 2 + C (8 : ℝ) * X + 1 by
          norm_num [map_ofNat]
          ring]
      simpa only [map_one, one_mul] using
        quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := 8) (c := 1)
          (by norm_num) (by norm_num [discrim])
  · rw [A157169_closed]
    apply Polynomial.Splits.mul
    · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      exact (Polynomial.Splits.X_add_C 1).pow n
    · exact A157169_quartic_splits n

/-- The order-five row A157171, in the recurrence form used downstream. -/
def A157171 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 11 * X + X ^ 2
  | 3 => 1 + 21 * X + 21 * X ^ 2 + X ^ 3
  | 4 => 1 + 31 * X + 66 * X ^ 2 + 31 * X ^ 3 + X ^ 4
  | n + 5 => (3 + 3 * X) * A157171 (n + 4) + (-3 + -6 * X + -3 * X ^ 2) *
      A157171 (n + 3) + (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A157171 (n + 2)

/-- The recurrence solution for A157171. -/
theorem A157171_closed : ∀ k : ℕ,
    A157171 (k + 4) = (1 + X) ^ k * A157171_quartic k
  | 0 => by norm_num [A157171, A157171_quartic, map_ofNat]; ring
  | 1 => by norm_num [A157171, A157171_quartic, map_ofNat]; ring
  | 2 => by norm_num [A157171, A157171_quartic, map_ofNat]; ring
  | k + 3 => by
      rw [show A157171 (k + 3 + 4) = (3 + 3 * X) * A157171 (k + 6) +
          (-3 + -6 * X + -3 * X ^ 2) * A157171 (k + 5) +
          (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A157171 (k + 4) by
        rw [show k + 3 + 4 = (k + 2) + 5 by ring]
        rfl]
      rw [show k + 6 = (k + 2) + 4 by ring, show k + 5 = (k + 1) + 4 by ring,
        A157171_closed (k + 2), A157171_closed (k + 1), A157171_closed k]
      apply Polynomial.funext
      intro r
      rw [A157171_quartic, A157171_quartic, A157171_quartic, A157171_quartic]
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_neg, eval_ofNat]
      grind

/-- Every A157171 row splits over the reals. -/
theorem A157171_splits (n : ℕ) : (A157171 n).Splits := by
  rcases n with _ | _ | _ | _ | n
  · change (1 : ℝ[X]).Splits
    exact Polynomial.Splits.one
  · rw [show A157171 1 = X + C (1 : ℝ) by
        change 1 + X = X + C (1 : ℝ)
        norm_num [map_ofNat]
        ring]
    exact Polynomial.Splits.X_add_C 1
  · rw [show A157171 2 = X ^ 2 + C (11 : ℝ) * X + 1 by
        change 1 + 11 * X + X ^ 2 = X ^ 2 + C (11 : ℝ) * X + 1
        norm_num [map_ofNat]
        ring]
    simpa only [map_one, one_mul] using
      quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := 11) (c := 1)
        (by norm_num) (by norm_num [discrim])
  · rw [show A157171 3 = (1 + X) * (1 + 20 * X + X ^ 2) by
        simp only [A157171]
        ring]
    apply Polynomial.Splits.mul
    · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      exact Polynomial.Splits.X_add_C 1
    · rw [show (1 + 20 * X + X ^ 2 : ℝ[X]) = X ^ 2 + C (20 : ℝ) * X + 1 by
          norm_num [map_ofNat]
          ring]
      simpa only [map_one, one_mul] using
        quadraticPoly_splits_of_discrim_nonneg (a := 1) (b := 20) (c := 1)
          (by norm_num) (by norm_num [discrim])
  · rw [A157171_closed]
    apply Polynomial.Splits.mul
    · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      exact (Polynomial.Splits.X_add_C 1).pow n
    · exact A157171_quartic_splits n

/-- The order-three row A110200, in the recurrence form used downstream. -/
def A110200 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 5 + 9 * X
  | 2 => 21 + 70 * X + 49 * X ^ 2
  | n + 3 => (7 + 7 * X) * A110200 (n + 2) + (-14 + -28 * X + -14 * X ^ 2) *
      A110200 (n + 1) + (8 + 8 * X ^ 3 + 24 * X + 24 * X ^ 2) * A110200 n

/-- The closed form for the positive-index A110200 rows. -/
theorem A110200_closed_succ : ∀ n : ℕ, A110200 (n + 1) =
    (1 + X) ^ n * (C (((4 : ℝ) ^ (n + 2) - 1) / 3) +
      C (((2 : ℝ) ^ (n + 2) - 1) ^ 2) * X)
  | 0 => by
      rw [show A110200 1 = 5 + 9 * X from rfl]
      norm_num [map_ofNat]
  | 1 => by
      rw [show A110200 2 = 21 + 70 * X + 49 * X ^ 2 from rfl]
      norm_num [map_ofNat]
      ring
  | 2 => by
      rw [show A110200 3 = 85 + 395 * X + 535 * X ^ 2 + 225 * X ^ 3 by
        simp only [A110200]
        grind]
      norm_num [map_ofNat]
      ring
  | n + 3 => by
      rw [show A110200 (n + 4) = (7 + 7 * X) * A110200 (n + 3) +
          (-14 + -28 * X + -14 * X ^ 2) * A110200 (n + 2) +
          (8 + 8 * X ^ 3 + 24 * X + 24 * X ^ 2) * A110200 (n + 1) by
        rw [show n + 4 = (n + 1) + 3 by lia]
        rfl]
      rw [A110200_closed_succ (n + 2), A110200_closed_succ (n + 1),
        A110200_closed_succ n]
      apply Polynomial.funext
      intro r
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_ofNat, eval_neg]
      grind

/-- Every A110200 row splits over the reals. -/
theorem A110200_splits (n : ℕ) : (A110200 n).Splits := by
  rcases n with _ | n
  · change (1 : ℝ[X]).Splits
    exact Polynomial.Splits.one
  · rw [A110200_closed_succ]
    apply Polynomial.Splits.mul
    · rw [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      exact (Polynomial.Splits.X_add_C 1).pow n
    · exact Polynomial.Splits.of_natDegree_le_one (by compute_degree!)

/-- The order-four row A100898, in the recurrence form used downstream. -/
def A100898 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 3 * X
  | 3 => 1 + 5 * X + 2 * X ^ 2
  | n + 4 => 2 * A100898 (n + 3) + (-1 + 2 * X) * A100898 (n + 2) +
      (-2 * X) * A100898 (n + 1) + (-1 * X ^ 2) * A100898 n

private def A100898FanGraph : SimpleGraph (Option ℕ) where
  Adj
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some i, some j => i + 1 = j ∨ j + 1 = i
  symm := by
    constructor
    intro u v h
    cases u <;> cases v <;> simp_all [or_comm]
  loopless := by
    constructor
    intro v
    cases v with
    | none => simp
    | some i => simp

private noncomputable instance : DecidableRel A100898FanGraph.Adj := Classical.decRel _

private noncomputable instance : DecidableRel A100898FanGraph.lineGraph.Adj :=
  Classical.decRel _

private def A100898Spoke (i : ℕ) : A100898FanGraph.edgeSet :=
  ⟨s(none, some i), by
    rw [SimpleGraph.mem_edgeSet]
    simp [A100898FanGraph]⟩

private def A100898PathEdge (i : ℕ) : A100898FanGraph.edgeSet :=
  ⟨s(some i, some (i + 1)), by
    rw [SimpleGraph.mem_edgeSet]
    simp [A100898FanGraph]⟩

private def A100898SpokeSupport (n : ℕ) : Finset A100898FanGraph.edgeSet := by
  classical
  exact (Finset.range n).image A100898Spoke

private def A100898PathSupport (n : ℕ) : Finset A100898FanGraph.edgeSet := by
  classical
  exact (Finset.range (n - 1)).image A100898PathEdge

private def A100898FanSupport (n : ℕ) : Finset A100898FanGraph.edgeSet :=
  A100898SpokeSupport n ∪ A100898PathSupport n

private def A100898FanPolynomial (n : ℕ) : ℝ[X] :=
  Graph.indepPolyOn A100898FanGraph.lineGraph (A100898FanSupport n)

private def A100898PathPolynomial (n : ℕ) : ℝ[X] :=
  Graph.indepPolyOn A100898FanGraph.lineGraph (A100898PathSupport n)

private lemma A100898_line_adj_spoke_spoke (i j : ℕ) :
    A100898FanGraph.lineGraph.Adj (A100898Spoke i) (A100898Spoke j) ↔ i ≠ j := by
  simp [SimpleGraph.lineGraph_adj_iff_exists, A100898Spoke]

private lemma A100898_line_adj_path_spoke (i j : ℕ) :
    A100898FanGraph.lineGraph.Adj (A100898PathEdge i) (A100898Spoke j) ↔
      j = i ∨ j = i + 1 := by
  simp [SimpleGraph.lineGraph_adj_iff_exists, A100898PathEdge, A100898Spoke]
  grind

private lemma A100898_line_adj_path_path (i j : ℕ) :
    A100898FanGraph.lineGraph.Adj (A100898PathEdge i) (A100898PathEdge j) ↔
      i + 1 = j ∨ j + 1 = i := by
  simp [SimpleGraph.lineGraph_adj_iff_exists, A100898PathEdge]
  lia

private lemma A100898_pathSupport_succ (n : ℕ) (hn : 1 ≤ n) :
    A100898PathSupport (n + 1) =
      insert (A100898PathEdge (n - 1)) (A100898PathSupport n) := by
  classical
  unfold A100898PathSupport
  grind

private lemma A100898_fanSupport_succ (n : ℕ) (hn : 1 ≤ n) :
    A100898FanSupport (n + 1) = insert (A100898Spoke n)
      (insert (A100898PathEdge (n - 1)) (A100898FanSupport n)) := by
  classical
  unfold A100898FanSupport A100898SpokeSupport A100898PathSupport
  grind

private lemma A100898_pathEdge_not_mem_fanSupport (n : ℕ) (_hn : 1 ≤ n) :
    A100898PathEdge (n - 1) ∉ A100898FanSupport n := by
  classical
  simp [A100898FanSupport, A100898SpokeSupport, A100898PathSupport,
    A100898PathEdge, A100898Spoke]
  lia

private lemma A100898_pathEdge_not_mem_pathSupport (n : ℕ) (_hn : 1 ≤ n) :
    A100898PathEdge (n - 1) ∉ A100898PathSupport n := by
  classical
  simp [A100898PathSupport, A100898PathEdge]
  lia

private lemma A100898_spoke_not_mem_extendedSupport (n : ℕ) (_hn : 1 ≤ n) :
    A100898Spoke n ∉ insert (A100898PathEdge (n - 1)) (A100898FanSupport n) := by
  classical
  simp [A100898FanSupport, A100898SpokeSupport, A100898PathSupport,
    A100898PathEdge, A100898Spoke]

private lemma A100898_filter_path_fanSupport (n : ℕ) (hn : 1 ≤ n) :
    (A100898FanSupport n).filter
        (fun e => ¬ A100898FanGraph.lineGraph.Adj (A100898PathEdge (n - 1)) e) =
      A100898FanSupport (n - 1) := by
  classical
  ext e
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨he, hnon⟩
    rw [A100898FanSupport, Finset.mem_union] at he
    rcases he with hs | hp
    · rcases Finset.mem_image.mp hs with ⟨i, hi, rfl⟩
      have hin : i < n := Finset.mem_range.mp hi
      have hnon' : ¬ (i = n - 1 ∨ i = n - 1 + 1) := by
        simpa [A100898_line_adj_path_spoke] using hnon
      rw [A100898FanSupport, Finset.mem_union]
      left
      apply Finset.mem_image.mpr
      grind
    · rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
      have hin : i < n - 1 := Finset.mem_range.mp hi
      have hnon' : ¬ (n - 1 + 1 = i ∨ i + 1 = n - 1) := by
        simpa [A100898_line_adj_path_path] using hnon
      rw [A100898FanSupport, Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      grind
  · intro he
    rw [A100898FanSupport, Finset.mem_union] at he
    rcases he with hs | hp
    · rcases Finset.mem_image.mp hs with ⟨i, hi, rfl⟩
      have hin : i < n - 1 := Finset.mem_range.mp hi
      constructor
      · rw [A100898FanSupport, Finset.mem_union]
        left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by lia), rfl⟩
      · rw [A100898_line_adj_path_spoke]
        lia
    · rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
      have hin : i < n - 1 - 1 := Finset.mem_range.mp hi
      constructor
      · rw [A100898FanSupport, Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by lia), rfl⟩
      · rw [A100898_line_adj_path_path]
        lia

private lemma A100898_filter_path_pathSupport (n : ℕ) (hn : 1 ≤ n) :
    (A100898PathSupport n).filter
        (fun e => ¬ A100898FanGraph.lineGraph.Adj (A100898PathEdge (n - 1)) e) =
      A100898PathSupport (n - 1) := by
  classical
  ext e
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨he, hnon⟩
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hin : i < n - 1 := Finset.mem_range.mp hi
    have hnon' : ¬ (n - 1 + 1 = i ∨ i + 1 = n - 1) := by
      simpa [A100898_line_adj_path_path] using hnon
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by lia), rfl⟩
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hin : i < n - 1 - 1 := Finset.mem_range.mp hi
    constructor
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by lia), rfl⟩
    · rw [A100898_line_adj_path_path]
      lia

private lemma A100898_filter_spoke_extendedSupport (n : ℕ) (hn : 1 ≤ n) :
    (insert (A100898PathEdge (n - 1)) (A100898FanSupport n)).filter
        (fun e => ¬ A100898FanGraph.lineGraph.Adj (A100898Spoke n) e) =
      A100898PathSupport n := by
  classical
  ext e
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨he, hnon⟩
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · exfalso
      apply hnon
      rw [A100898FanGraph.lineGraph.adj_comm, A100898_line_adj_path_spoke]
      lia
    · rw [A100898FanSupport, Finset.mem_union] at he
      rcases he with hs | hp
      · rcases Finset.mem_image.mp hs with ⟨i, hi, rfl⟩
        exfalso
        apply hnon
        rw [A100898_line_adj_spoke_spoke]
        grind
      · grind
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    have hin : i < n - 1 := Finset.mem_range.mp hi
    constructor
    · rw [Finset.mem_insert]
      right
      rw [A100898FanSupport, Finset.mem_union]
      simp_all
    · rw [A100898FanGraph.lineGraph.adj_comm, A100898_line_adj_path_spoke]
      lia

private lemma A100898FanPolynomial_splits (n : ℕ) :
    (A100898FanPolynomial n).Splits := by
  exact Graph.supportIndepPoly_splits_of_clawFree
    (Graph.lineGraph_clawFree A100898FanGraph) (A100898FanSupport n)

private lemma A100898PathPolynomial_rec (n : ℕ) (hn : 1 ≤ n) :
    A100898PathPolynomial (n + 1) =
      A100898PathPolynomial n + X * A100898PathPolynomial (n - 1) := by
  unfold A100898PathPolynomial
  rw [A100898_pathSupport_succ n hn,
    Graph.indepPolyOn_insert A100898FanGraph.lineGraph
      (A100898_pathEdge_not_mem_pathSupport n hn)]
  rw [A100898_filter_path_pathSupport n hn]

private lemma A100898FanPolynomial_rec (n : ℕ) (hn : 1 ≤ n) :
    A100898FanPolynomial (n + 1) =
      A100898FanPolynomial n + X * A100898FanPolynomial (n - 1) +
        X * A100898PathPolynomial n := by
  unfold A100898FanPolynomial
  rw [A100898_fanSupport_succ n hn,
    Graph.indepPolyOn_insert A100898FanGraph.lineGraph
      (A100898_spoke_not_mem_extendedSupport n hn),
    A100898_filter_spoke_extendedSupport n hn,
    Graph.indepPolyOn_insert A100898FanGraph.lineGraph
      (A100898_pathEdge_not_mem_fanSupport n hn),
    A100898_filter_path_fanSupport n hn]
  simp only [A100898PathPolynomial]

private lemma A100898FanPolynomial_rec_four (n : ℕ) :
    A100898FanPolynomial (n + 4) =
      2 * A100898FanPolynomial (n + 3) +
        (-1 + 2 * X) * A100898FanPolynomial (n + 2) +
        (-2 * X) * A100898FanPolynomial (n + 1) +
        (-1 * X ^ 2) * A100898FanPolynomial n := by
  have hF1 := A100898FanPolynomial_rec (n + 1) (by lia)
  have hF2 := A100898FanPolynomial_rec (n + 2) (by lia)
  have hF3 := A100898FanPolynomial_rec (n + 3) (by lia)
  have hP := A100898PathPolynomial_rec (n + 2) (by lia)
  grind

private lemma A100898FanPolynomial_zero : A100898FanPolynomial 0 = 1 := by
  simp [A100898FanPolynomial, A100898FanSupport, A100898SpokeSupport,
    A100898PathSupport, Graph.indepPolyOn_empty]

private lemma A100898FanPolynomial_one : A100898FanPolynomial 1 = 1 + X := by
  have hs : A100898FanSupport 1 =
      insert (A100898Spoke 0) (∅ : Finset A100898FanGraph.edgeSet) := by
    ext e
    simp [A100898FanSupport, A100898SpokeSupport, A100898PathSupport]
  unfold A100898FanPolynomial
  rw [hs, Graph.indepPolyOn_insert A100898FanGraph.lineGraph (by simp),
    Graph.indepPolyOn_empty]
  simp [Graph.indepPolyOn_empty]

private lemma A100898PathPolynomial_one : A100898PathPolynomial 1 = 1 := by
  simp [A100898PathPolynomial, A100898PathSupport, Graph.indepPolyOn_empty]

private lemma A100898PathPolynomial_two : A100898PathPolynomial 2 = 1 + X := by
  have hs : A100898PathSupport 2 =
      insert (A100898PathEdge 0) (∅ : Finset A100898FanGraph.edgeSet) := by
    ext e
    simp [A100898PathSupport]
  unfold A100898PathPolynomial
  rw [hs, Graph.indepPolyOn_insert A100898FanGraph.lineGraph (by simp),
    Graph.indepPolyOn_empty]
  simp [Graph.indepPolyOn_empty]

private lemma A100898FanPolynomial_two : A100898FanPolynomial 2 = 1 + 3 * X := by
  have h := A100898FanPolynomial_rec 1 (by lia)
  norm_num at h
  rw [h, A100898FanPolynomial_one, A100898FanPolynomial_zero,
    A100898PathPolynomial_one]
  ring

private lemma A100898FanPolynomial_three :
    A100898FanPolynomial 3 = 1 + 5 * X + 2 * X ^ 2 := by
  have h := A100898FanPolynomial_rec 2 (by lia)
  norm_num at h
  rw [h, A100898FanPolynomial_two, A100898FanPolynomial_one,
    A100898PathPolynomial_two]
  ring

private lemma A100898_eq_fanPolynomial : ∀ n : ℕ, A100898 n = A100898FanPolynomial n
  | 0 => by rw [A100898, A100898FanPolynomial_zero]
  | 1 => by rw [A100898, A100898FanPolynomial_one]
  | 2 => by rw [A100898, A100898FanPolynomial_two]
  | 3 => by rw [A100898, A100898FanPolynomial_three]
  | n + 4 => by
      rw [A100898, A100898FanPolynomial_rec_four,
        A100898_eq_fanPolynomial n, A100898_eq_fanPolynomial (n + 1),
        A100898_eq_fanPolynomial (n + 2), A100898_eq_fanPolynomial (n + 3)]

/-- Every A100898 row splits over the reals. -/
theorem A100898_splits (n : ℕ) : (A100898 n).Splits := by
  rw [A100898_eq_fanPolynomial]
  exact A100898FanPolynomial_splits n

end RealRooted.ClosedFormRows
