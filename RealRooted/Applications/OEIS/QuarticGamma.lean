module

public import Mathlib
public import RealRooted.Basic.Coefficients

/-!
# A quartic-cofactor family containing three OEIS rows

This module studies the common two-parameter family containing
[OEIS A157169](https://oeis.org/A157169),
[OEIS A157171](https://oeis.org/A157171), and
[OEIS A124376](https://oeis.org/A124376).  We use the closed recurrence form
because the repository has no recurrence-based definition of these three row
families to identify with it.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.QuarticGamma

/-- The common row-polynomial family for OEIS A157169, A157171, and A124376.

It is the family `P_n = gammaTransform_n (γ_n)` with
`γ_0 = γ_1 = 1`, `γ_{n+2}(Z) = 1 + a (n+1) Z + b binom(n,2) Z²`.  Here it is given by its five
seeds and the recurrence `P_{n+5} = 3 s P_{n+4} - 3 s² P_{n+3} + s³ P_{n+2}`, `s = 1 + X`.
For `(a, b) = (3, 2), (9, 6), (2, 1)` these are OEIS A157169, A157171, A124376. -/
def polynomial (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => (1 + X) ^ 2 + C a * X
  | 3 => (1 + X) ^ 3 + C (2 * a) * X * (1 + X)
  | 4 => (1 + X) ^ 4 + C (3 * a) * X * (1 + X) ^ 2 + C b * X ^ 2
  | n + 5 => 3 * (1 + X) * polynomial a b (n + 4) - 3 * (1 + X) ^ 2 * polynomial a b (n + 3) +
      (1 + X) ^ 3 * polynomial a b (n + 2)

/-- The quartic cofactor of `polynomial a b (n + 4)`. -/
private def quarticCofactor (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (1 + X) ^ 4 + C (a * ((n : ℝ) + 3)) * X * (1 + X) ^ 2 +
        C (b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ 2

private theorem polynomial_add_four_eq (a b : ℝ) (n : ℕ) :
    polynomial a b (n + 4) = (1 + X) ^ n * quarticCofactor a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n, ih with
  | 0, _ =>
    simp only [polynomial, quarticCofactor]
    have e1 : C (a * (((0:ℕ):ℝ) + 3)) = C (3 * a) := by congr 1; push_cast; ring
    have e2 :
        C (b / 2 * (((0 : ℕ) : ℝ) + 2) * (((0 : ℕ) : ℝ) + 1)) = C b := by
      congr 1
      push_cast
      ring
    rw [e1, e2]; ring
  | 1, _ =>
    simp only [polynomial, quarticCofactor]
    have e1 : C (a * (((1:ℕ):ℝ) + 3)) = 3 * C (3 * a) - 3 * C (2*a) + C a := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub, ← map_add]; congr 1; push_cast; ring
    have e2 : C (b / 2 * (((1:ℕ):ℝ) + 2) * (((1:ℕ):ℝ) + 1)) = 3 * C b := by
      simp only [← map_ofNat C 3, ← map_mul]; congr 1; push_cast; ring
    rw [e1, e2]; ring
  | 2, ih =>
    have hindex : (2 : ℕ) + 4 = 1 + 5 := rfl
    rw [hindex, polynomial, ih 1 (by norm_num)]
    simp only [polynomial, quarticCofactor]
    have e1 : C (a * (((2 : ℕ) : ℝ) + 3)) =
        3 * C (a * (((1 : ℕ) : ℝ) + 3)) - 3 * C (3 * a) + C (2 * a) := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub, ← map_add]; congr 1; push_cast; ring
    have e2 : C (b / 2 * (((2:ℕ):ℝ) + 2) * (((2:ℕ):ℝ) + 1)) =
        3 * C (b / 2 * (((1:ℕ):ℝ) + 2) * (((1:ℕ):ℝ) + 1)) - 3 * C b := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub]; congr 1; push_cast; ring
    rw [e1, e2]; ring
  | 3, ih =>
    have hindex : (3 : ℕ) + 4 = 2 + 5 := rfl
    have hprev : (2 : ℕ) + 3 = 1 + 4 := rfl
    have hbase : (2 : ℕ) + 2 = 4 := rfl
    rw [hindex, polynomial, ih 2 (by norm_num), hprev, ih 1 (by norm_num),
      hbase, polynomial]
    simp only [quarticCofactor]
    have e1 : C (a * (((3 : ℕ) : ℝ) + 3)) =
        3 * C (a * (((2 : ℕ) : ℝ) + 3)) -
          3 * C (a * (((1 : ℕ) : ℝ) + 3)) + C (3 * a) := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub, ← map_add]; congr 1; push_cast; ring
    have e2 : C (b / 2 * (((3:ℕ):ℝ) + 2) * (((3:ℕ):ℝ) + 1)) =
        3 * C (b / 2 * (((2 : ℕ) : ℝ) + 2) * (((2 : ℕ) : ℝ) + 1)) -
          3 * C (b / 2 * (((1 : ℕ) : ℝ) + 2) * (((1 : ℕ) : ℝ) + 1)) + C b := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub, ← map_add]; congr 1; push_cast; ring
    rw [e1, e2]; ring
  | k + 4, ih =>
    have hindex : k + 4 + 4 = (k + 3) + 5 := by ring
    have hfirst : k + 3 + 4 = (k + 3) + 4 := rfl
    have hsecond : k + 3 + 3 = (k + 2) + 4 := by ring
    have hthird : k + 3 + 2 = (k + 1) + 4 := by ring
    rw [hindex, polynomial, hfirst, ih (k + 3) (by lia), hsecond,
      ih (k + 2) (by lia), hthird, ih (k + 1) (by lia)]
    simp only [quarticCofactor]
    have e1 : C (a * (((k + 4 : ℕ) : ℝ) + 3)) =
        3 * C (a * (((k + 3 : ℕ) : ℝ) + 3)) -
          3 * C (a * (((k + 2 : ℕ) : ℝ) + 3)) +
            C (a * (((k + 1 : ℕ) : ℝ) + 3)) := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub, ← map_add]; congr 1; push_cast; ring
    have e2 : C (b / 2 * (((k+4:ℕ):ℝ) + 2) * (((k+4:ℕ):ℝ) + 1)) =
        3 * C (b / 2 * (((k + 3 : ℕ) : ℝ) + 2) * (((k + 3 : ℕ) : ℝ) + 1)) -
          3 * C
            (b / 2 * (((k + 2 : ℕ) : ℝ) + 2) * (((k + 2 : ℕ) : ℝ) + 1)) +
          C (b / 2 * (((k + 1 : ℕ) : ℝ) + 2) * (((k + 1 : ℕ) : ℝ) + 1)) := by
      simp only [← map_ofNat C 3, ← map_mul, ← map_sub, ← map_add]; congr 1; push_cast; ring
    rw [e1, e2]; ring

/-- Closed form for every row of index at least four. -/
theorem polynomial_add_four (a b : ℝ) (n : ℕ) :
    polynomial a b (n + 4) = (1 + X) ^ n *
      ((1 + X) ^ 4 + C (a * ((n : ℝ) + 3)) * X * (1 + X) ^ 2 +
        C (b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ 2) := by
  rw [polynomial_add_four_eq]
  rfl

private lemma one_add_X_eq : (1 + X : ℝ[X]) = X + C 1 := by
  rw [map_one, add_comm]

private lemma quarticCofactor_monic_natDegree (a b : ℝ) (n : ℕ) :
    (quarticCofactor a b n).Monic ∧
      (quarticCofactor a b n).natDegree = 4 := by
  unfold quarticCofactor
  constructor
  · monicity!
  · compute_degree!

private theorem monic_natDegree_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).Monic ∧ (polynomial a b n).natDegree = n := by
  match n with
  | 0 => simp [polynomial]
  | 1 =>
      simp only [polynomial]
      constructor
      · monicity!
      · compute_degree!
  | 2 =>
      simp only [polynomial]
      constructor
      · monicity!
      · compute_degree!
  | 3 =>
      simp only [polynomial]
      constructor
      · monicity!
      · compute_degree!
  | k + 4 =>
    rw [polynomial_add_four_eq]
    obtain ⟨h1, h2⟩ := quarticCofactor_monic_natDegree a b k
    have hs : (1 + X : ℝ[X]).Monic := by rw [one_add_X_eq]; exact monic_X_add_C 1
    refine ⟨(hs.pow k).mul h1, ?_⟩
    rw [(hs.pow k).natDegree_mul h1, h2, natDegree_pow, one_add_X_eq, natDegree_X_add_C]
    ring

/-- Every polynomial in the family is monic. -/
theorem monic_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).Monic :=
  (monic_natDegree_polynomial a b n).1

/-- Every polynomial in the family has degree equal to its row index. -/
theorem natDegree_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).natDegree = n :=
  (monic_natDegree_polynomial a b n).2

private lemma hasNonnegCoeffs_one_add_X :
    HasNonnegCoeffs (1 + Polynomial.X : ℝ[X]) :=
  hasNonnegCoeffs_one.add hasNonnegCoeffs_X

/-- All coefficients are nonnegative when both parameters are nonnegative. -/
theorem hasNonnegCoeffs_polynomial {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (polynomial a b n) := by
  match n with
  | 0 => exact hasNonnegCoeffs_one
  | 1 => exact hasNonnegCoeffs_one_add_X
  | 2 =>
      exact (hasNonnegCoeffs_one_add_X.pow 2).add
        ((hasNonnegCoeffs_C ha).mul hasNonnegCoeffs_X)
  | 3 =>
      exact (hasNonnegCoeffs_one_add_X.pow 3).add
        (((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X).mul
          hasNonnegCoeffs_one_add_X)
  | k + 4 =>
    rw [polynomial_add_four_eq]
    unfold quarticCofactor
    exact (hasNonnegCoeffs_one_add_X.pow k).mul
      (((hasNonnegCoeffs_one_add_X.pow 4).add
          (((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X).mul
            (hasNonnegCoeffs_one_add_X.pow 2))).add
        ((hasNonnegCoeffs_C (by positivity)).mul (hasNonnegCoeffs_X.pow 2)))

/-- Every row has constant coefficient one. -/
theorem coeff_zero_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  match n with
  | 0 => simp [polynomial]
  | 1 => simp [polynomial]
  | 2 => simp [polynomial]
  | 3 => simp [polynomial]
  | k + 4 =>
      rw [polynomial_add_four_eq]
      simp [quarticCofactor]

/-- Every real root is strictly negative when both parameters are nonnegative. -/
theorem roots_mem_Iio_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ∀ r ∈ (polynomial a b n).roots, r ∈ Set.Iio (0 : ℝ) := by
  intro r hr
  have hnonpos := roots_nonpos_of_hasNonnegCoeffs
    (hasNonnegCoeffs_polynomial ha hb n) r hr
  have hne : r ≠ 0 := by
    intro hr0
    subst r
    have hroot := (mem_roots (monic_polynomial a b n).ne_zero).mp hr
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
      coeff_zero_polynomial] at hroot
    norm_num at hroot
  exact lt_of_le_of_ne hnonpos hne

private lemma quad_splits {u : ℝ} (hu : 0 ≤ u) :
    ((1 + X) ^ 2 + C u * X : ℝ[X]).Splits := by
  have hd : 0 ≤ (2 + u) ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hd
  apply Splits.of_natDegree_eq_two (x := (-(2 + u) + Real.sqrt ((2 + u) ^ 2 - 4)) / 2)
  · compute_degree!
  · simp only [eval_add, eval_pow, eval_one, eval_X, eval_mul, eval_C]
    linear_combination (1/4 : ℝ) * hs

private lemma one_add_X_splits : (1 + X : ℝ[X]).Splits := by
  rw [one_add_X_eq]
  exact Splits.X_add_C 1

private lemma quarticCofactor_splits {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (m : ℕ) :
    (quarticCofactor a b m).Splits := by
  set A := a * ((m : ℝ) + 3)
  set B := b / 2 * ((m : ℝ) + 2) * ((m : ℝ) + 1)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hD : 0 ≤ A ^ 2 - 4 * B := by
    simp only [A, B]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (sq_nonneg ((m:ℝ) + 3)), mul_nonneg hb hm]
  have hs := Real.sq_sqrt hD
  have hsn := Real.sqrt_nonneg (A ^ 2 - 4 * B)
  have hsle : Real.sqrt (A ^ 2 - 4 * B) ≤ A := by
    rw [Real.sqrt_le_left hA]; linarith
  set u := (A + Real.sqrt (A ^ 2 - 4 * B)) / 2
  set v := (A - Real.sqrt (A ^ 2 - 4 * B)) / 2
  have huv1 : C A = C u + C v := by rw [← map_add]; congr 1; simp only [u, v]; ring
  have huv2 : C B = C u * C v := by
    rw [← map_mul]; congr 1; simp only [u, v]; linear_combination (1/4 : ℝ) * hs
  have : quarticCofactor a b m =
      ((1 + X) ^ 2 + C u * X) * ((1 + X) ^ 2 + C v * X) := by
    unfold quarticCofactor
    rw [huv1, huv2]
    ring
  rw [this]
  exact (quad_splits (by positivity)).mul (quad_splits (by simp only [v]; linarith))

/-- Every row splits when `0 ≤ a`, `0 ≤ b`, and `2b ≤ a²`. -/
theorem splits_polynomial {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    (polynomial a b n).Splits := by
  match n with
  | 0 => exact Splits.one
  | 1 => exact one_add_X_splits
  | 2 => exact quad_splits ha
  | 3 =>
    have : polynomial a b 3 =
        (1 + X) * ((1 + X) ^ 2 + C (2 * a) * X) := by
      simp only [polynomial]
      ring
    rw [this]
    exact one_add_X_splits.mul (quad_splits (by positivity))
  | k + 4 =>
    rw [polynomial_add_four_eq]
    exact (one_add_X_splits.pow k).mul (quarticCofactor_splits ha hb hab k)

/-- For `b > 0`, the root `-1` has exactly the multiplicity forced by the
closed form. -/
theorem rootMultiplicity_neg_one_polynomial_add_four {a b : ℝ}
    (hb : 0 < b) (n : ℕ) :
    (polynomial a b (n + 4)).rootMultiplicity (-1) = n := by
  have hQ : (quarticCofactor a b n).eval (-1) ≠ 0 := by
    simp only [quarticCofactor, eval_add, eval_pow, eval_one, eval_X, eval_mul, eval_C]
    have : (0:ℝ) < b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
    norm_num; exact ⟨⟨hb.ne', by positivity⟩, by positivity⟩
  have hs : (1 + X : ℝ[X]) = X - C (-1) := by rw [map_neg, map_one, sub_neg_eq_add, add_comm]
  have hne : polynomial a b (n + 4) ≠ 0 := (monic_polynomial a b (n + 4)).ne_zero
  rw [polynomial_add_four_eq] at hne ⊢
  rw [rootMultiplicity_mul hne, hs, rootMultiplicity_X_sub_C_pow,
    rootMultiplicity_eq_zero hQ, add_zero]

/-- The parameter inequality is necessary if every row splits. -/
theorem two_mul_le_sq_of_forall_splits_polynomial {a b : ℝ}
    (h : ∀ n, (polynomial a b n).Splits) : 2 * b ≤ a ^ 2 := by
  by_contra hlt
  push Not at hlt
  have hb' : 0 < b := by nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (6 * b / (2 * b - a ^ 2))
  have hpos : 0 < 2 * b - a ^ 2 := by linarith
  have hm' : 6 * b < (2 * b - a ^ 2) * m := by rw [div_lt_iff₀ hpos] at hm; linarith
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  set A := a * ((m : ℝ) + 3)
  set B := b / 2 * ((m : ℝ) + 2) * ((m : ℝ) + 1)
  have hD : A ^ 2 - 4 * B < 0 := by
    simp only [A, B]
    nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 3) :
      (m:ℝ) ≤ m + 3) hpos.le]
  have hrow := h (m + 4)
  have hne : polynomial a b (m + 4) ≠ 0 := (monic_polynomial a b (m + 4)).ne_zero
  rw [polynomial_add_four_eq] at hrow hne
  have hQs : (quarticCofactor a b m).Splits := hrow.of_dvd hne (dvd_mul_left _ _)
  have hdeg : (quarticCofactor a b m).degree ≠ 0 := by
    rw [degree_eq_natDegree (quarticCofactor_monic_natDegree a b m).1.ne_zero,
      (quarticCofactor_monic_natDegree a b m).2]
    decide
  obtain ⟨x, hx⟩ := hQs.exists_eval_eq_zero hdeg
  simp only [quarticCofactor, eval_add, eval_pow, eval_one, eval_X, eval_mul,
    eval_C] at hx
  change (1 + x) ^ 4 + A * x * (1 + x) ^ 2 + B * x ^ 2 = 0 at hx
  rcases eq_or_ne x 0 with rfl | hx0
  · norm_num at hx
  · have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * (1 + x) ^ 2 + A * x), mul_pos hx2 (neg_pos.2 hD)]

/-- For nonnegative parameters, every row splits exactly in the sharp range
`2b ≤ a²`. -/
theorem forall_splits_polynomial_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∀ n, (polynomial a b n).Splits) ↔ 2 * b ≤ a ^ 2 := by
  constructor
  · exact two_mul_le_sq_of_forall_splits_polynomial
  · intro hab n
    exact splits_polynomial ha hb hab n

end RealRooted.Applications.OEIS.QuarticGamma
