module

public import Mathlib
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
public import RealRooted.GammaTransform.Basic
import RealRooted.AffineProperPosition
import RealRooted.GammaTransform.ProperPosition
import RealRooted.Linear
import RealRooted.ProductOrientation
import RealRooted.QuadraticRoot

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

/-- The gamma-polynomial model underlying `polynomial a b n`. -/
def gammaPolynomial (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => C a * X + 1
  | 3 => C (2 * a) * X + 1
  | n + 4 =>
      C (b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ 2 +
        C (a * ((n : ℝ) + 3)) * X + 1

/-- A polynomial sequence with the five displayed seeds and the order-five
recurrence is `polynomial a b`. -/
theorem eq_polynomial_of_five_seeds_and_recurrence
    {a b : ℝ} {Q : ℕ → ℝ[X]}
    (h0 : Q 0 = 1)
    (h1 : Q 1 = 1 + X)
    (h2 : Q 2 = (1 + X) ^ 2 + C a * X)
    (h3 : Q 3 = (1 + X) ^ 3 + C (2 * a) * X * (1 + X))
    (h4 : Q 4 = (1 + X) ^ 4 + C (3 * a) * X * (1 + X) ^ 2 + C b * X ^ 2)
    (hrec : ∀ n,
      Q (n + 5) = 3 * (1 + X) * Q (n + 4) - 3 * (1 + X) ^ 2 * Q (n + 3) +
        (1 + X) ^ 3 * Q (n + 2)) :
    Q = polynomial a b := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa [polynomial] using h0
    | 1 => simpa [polynomial] using h1
    | 2 => simpa [polynomial] using h2
    | 3 => simpa [polynomial] using h3
    | 4 => simpa [polynomial] using h4
    | k + 5 =>
        rw [hrec, polynomial, ih (k + 4) (by lia), ih (k + 3) (by lia),
          ih (k + 2) (by lia)]

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

/-- The recurrence-defined rows are the ambient-degree gamma transforms of
`gammaPolynomial`. -/
theorem polynomial_eq_gammaTransform (a b : ℝ) (n : ℕ) :
    polynomial a b n = gammaTransform n (gammaPolynomial a b n) := by
  match n with
  | 0 => simp [polynomial, gammaPolynomial, gammaTransform, gammaBasisTerm]
  | 1 => simp [polynomial, gammaPolynomial, gammaTransform, gammaBasisTerm]; ring
  | 2 =>
    simp only [polynomial, gammaPolynomial, gammaTransform_add]
    rw [show C a * X = C a * X ^ 1 by simp,
      gammaTransform_C_mul_X_pow _ (by norm_num : 1 ≤ 2 / 2)]
    have hone : (1 : ℝ[X]) = C 1 * X ^ 0 := by simp
    rw [hone, gammaTransform_C_mul_X_pow _ (by norm_num : 0 ≤ 2 / 2)]
    simp only [gammaBasisTerm, map_one]
    ring
  | 3 =>
    simp only [polynomial, gammaPolynomial, gammaTransform_add]
    rw [show C (2 * a) * X = C (2 * a) * X ^ 1 by simp,
      gammaTransform_C_mul_X_pow _ (by norm_num : 1 ≤ 3 / 2)]
    have hone : (1 : ℝ[X]) = C 1 * X ^ 0 := by simp
    rw [hone, gammaTransform_C_mul_X_pow _ (by norm_num : 0 ≤ 3 / 2)]
    simp only [gammaBasisTerm, map_one]
    ring
  | k + 4 =>
    rw [polynomial_add_four]
    simp only [gammaPolynomial, gammaTransform_add]
    rw [gammaTransform_C_mul_X_pow _ (by lia : 2 ≤ (k + 4) / 2),
      show C (a * ((k : ℝ) + 3)) * X =
        C (a * ((k : ℝ) + 3)) * X ^ 1 by simp,
      gammaTransform_C_mul_X_pow _ (by lia : 1 ≤ (k + 4) / 2)]
    have hone : (1 : ℝ[X]) = C 1 * X ^ 0 := by simp
    rw [hone, gammaTransform_C_mul_X_pow _ (by lia : 0 ≤ (k + 4) / 2)]
    simp only [gammaBasisTerm, map_one]
    rw [show k + 4 - 2 = k + 2 by lia, show k + 4 - 4 = k by lia,
      show k + 4 - 0 = k + 4 by lia]
    rw [show (X + 1 : ℝ[X]) = 1 + X by ring]
    ring

private lemma natDegree_gammaPolynomial_le_half (a b : ℝ) (n : ℕ) :
    (gammaPolynomial a b n).natDegree ≤ n / 2 := by
  match n with
  | 0 => simp [gammaPolynomial]
  | 1 => simp [gammaPolynomial]
  | 2 =>
      simp only [gammaPolynomial]
      calc
        (C a * X + 1).natDegree ≤ max (C a * X).natDegree (1 : ℝ[X]).natDegree :=
          natDegree_add_le _ _
        _ ≤ 1 := max_le
          (natDegree_mul_le.trans
            (Nat.add_le_add (natDegree_C a).le natDegree_X.le)) (by simp)
  | 3 =>
      simp only [gammaPolynomial]
      calc
        (C (2 * a) * X + 1).natDegree ≤
            max (C (2 * a) * X).natDegree (1 : ℝ[X]).natDegree :=
          natDegree_add_le _ _
        _ ≤ 1 := max_le
          (natDegree_mul_le.trans
            (Nat.add_le_add (natDegree_C (2 * a)).le natDegree_X.le)) (by simp)
  | k + 4 =>
      calc
        (gammaPolynomial a b (k + 4)).natDegree ≤ 2 := by
          simp only [gammaPolynomial]
          compute_degree!
        _ ≤ (k + 4) / 2 := by lia

private lemma hasNonnegCoeffs_gammaPolynomial {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (gammaPolynomial a b n) := by
  match n with
  | 0 => exact hasNonnegCoeffs_one
  | 1 => exact hasNonnegCoeffs_one
  | 2 =>
      exact ((hasNonnegCoeffs_C ha).mul hasNonnegCoeffs_X).add hasNonnegCoeffs_one
  | 3 =>
      exact ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X).add
        hasNonnegCoeffs_one
  | k + 4 =>
      exact (((hasNonnegCoeffs_C (by positivity)).mul (hasNonnegCoeffs_X.pow 2)).add
        ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X)).add
          hasNonnegCoeffs_one

private lemma coeff_zero_gammaPolynomial (a b : ℝ) (n : ℕ) :
    (gammaPolynomial a b n).coeff 0 = 1 := by
  match n with
  | 0 => simp [gammaPolynomial]
  | 1 => simp [gammaPolynomial]
  | 2 => simp [gammaPolynomial]
  | 3 => simp [gammaPolynomial]
  | k + 4 => simp [gammaPolynomial]

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

private lemma gammaPolynomial_ne_zero (a b : ℝ) (n : ℕ) :
    gammaPolynomial a b n ≠ 0 := by
  intro hzero
  have hcoeff := coeff_zero_gammaPolynomial a b n
  rw [hzero] at hcoeff
  simp at hcoeff

private lemma allComboRealRooted_gammaPolynomial_add_four
    {a b : ℝ} (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (k : ℕ) :
    AllComboRealRooted (gammaPolynomial a b (k + 4))
      (gammaPolynomial a b (k + 5)) := by
  intro s t
  let m : ℝ := (k : ℝ) + 4
  let z : ℝ := s + t
  let q : ℝ :=
    s * (b / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1)) +
      t * (b / 2 * (((k + 1 : ℕ) : ℝ) + 2) * (((k + 1 : ℕ) : ℝ) + 1))
  let ell : ℝ :=
    s * (a * ((k : ℝ) + 3)) + t * (a * (((k + 1 : ℕ) : ℝ) + 3))
  have hform :
      C s * gammaPolynomial a b (k + 4) +
          C t * gammaPolynomial a b (k + 5) =
        C q * X ^ 2 + C ell * X + C z := by
    simp only [gammaPolynomial, q, ell, z, C_mul, C_add]
    ring
  rw [hform]
  apply quadraticPoly_splits_of_discrim_nonneg_or_linear
  rw [discrim]
  have hdecomp :
      ell ^ 2 - 4 * q * z =
        (a ^ 2 - 2 * b) * ((m - 1) * z + t) ^ 2 +
          2 * b * (t + z) ^ 2 + 6 * b * (m - 2) * z ^ 2 := by
    simp only [q, ell, z]
    push_cast
    simp only [m]
    ring
  rw [hdecomp]
  have hdelta : 0 ≤ a ^ 2 - 2 * b := by linarith
  have hm : 0 ≤ m - 2 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp only [m]
    linarith
  positivity

/-- The initial quadratic transition in the gamma family. -/
private theorem gamma_strictInterl_three {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) :
    StrictInterl (gammaPolynomial a b 3) (gammaPolynomial a b 4) := by
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · subst a
      subst b
      simpa [gammaPolynomial] using
        (StrictInterl.refl one_ne_zero Polynomial.Splits.one)
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      subst b
      have h := strictInterl_affine_linear_affine_linear_of_cross
        (u := 2 * a) (v := 1) (U := 3 * a) (V := 1)
        (by positivity) (by positivity) (by nlinarith)
      have hg3 : gammaPolynomial a 0 3 = C (2 * a) * X + C 1 := by
        simp [gammaPolynomial]
      have hg4 : gammaPolynomial a 0 4 = C (3 * a) * X + C 1 := by
        simp only [gammaPolynomial]
        norm_num
        ring
      rw [hg3, hg4]
      exact h
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have ha_pos : 0 < a := by nlinarith
    let f : ℝ[X] := C (2 * a) * X + C 1
    let F : ℝ[X] := C b * X ^ 2 + C (3 * a) * X + C 1
    have hfdeg : f.natDegree = 1 := by
      simp only [f]
      compute_degree!
      positivity
    have hFdeg : F.natDegree = 2 := by
      simp only [F]
      exact natDegree_quadratic hb_pos.ne'
    have hFsplits : F.Splits := by
      simp only [F]
      apply quadraticPoly_splits_of_le hb_pos
      nlinarith
    have hFpos : HasPosLeadingCoeff F := by
      simp only [HasPosLeadingCoeff, F]
      rw [leadingCoeff_quadratic hb_pos.ne']
      exact hb_pos
    have hroot : ∀ r, f.IsRoot r → F.eval r ≤ 0 := by
      intro r hr
      simp only [f, F, Polynomial.IsRoot, eval_add, eval_mul, eval_C, eval_X,
        eval_pow] at hr ⊢
      have hmul := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg r)
      nlinarith
    have hint := interl_linear_quadratic_of_eval_nonpos
      hfdeg hFdeg hFsplits hFpos hroot
    have hstrict := hint.toStrictInterl_of_ne
      (ne_zero_of_natDegree_gt (p := f) (n := 0) (by rw [hfdeg]; norm_num))
      (ne_zero_of_natDegree_gt (p := F) (n := 0) (by rw [hFdeg]; norm_num))
    have hg3 : gammaPolynomial a b 3 = C (2 * a) * X + C 1 := by
      simp [gammaPolynomial]
    have hg4 : gammaPolynomial a b 4 =
        C b * X ^ 2 + C (3 * a) * X + C 1 := by
      simp only [gammaPolynomial]
      norm_num
      ring
    rw [hg3, hg4]
    dsimp only [f, F] at hstrict
    exact hstrict

/-- The quadratic gamma transitions from index four onward. -/
private theorem gamma_strictInterl_add_four {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (k : ℕ) :
    StrictInterl (gammaPolynomial a b (k + 4)) (gammaPolynomial a b (k + 5)) := by
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · subst a
      subst b
      simpa [gammaPolynomial] using
        (StrictInterl.refl one_ne_zero Polynomial.Splits.one)
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      subst b
      have h := strictInterl_affine_linear_affine_linear_of_cross
        (u := a * ((k : ℝ) + 3)) (v := 1)
        (U := a * ((k : ℝ) + 4)) (V := 1)
        (by positivity) (by positivity) (by nlinarith)
      have hkcast :
          ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by
        push_cast
        ring
      have hleft : gammaPolynomial a 0 (k + 4) =
          C (a * ((k : ℝ) + 3)) * X + C 1 := by
        simp [gammaPolynomial]
      have hright : gammaPolynomial a 0 (k + 5) =
          C (a * ((k : ℝ) + 4)) * X + C 1 := by
        simp only [gammaPolynomial]
        rw [hkcast]
        simp
      rw [hleft, hright]
      exact h
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let A : ℝ := a * ((k : ℝ) + 3)
    let A' : ℝ := a * ((k : ℝ) + 4)
    let B : ℝ := b / 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1)
    let B' : ℝ := b / 2 * ((k : ℝ) + 3) * ((k : ℝ) + 2)
    have hleft : gammaPolynomial a b (k + 4) =
        C B * X ^ 2 + C A * X + C 1 := by
      simp only [gammaPolynomial, A, B, map_one]
    have hright : gammaPolynomial a b (k + 5) =
        C B' * X ^ 2 + C A' * X + C 1 := by
      simp only [gammaPolynomial, A', B', map_one]
      push_cast
      congr 4 <;> ring
    have hB : 0 < B := by positivity
    have hB' : 0 < B' := by positivity
    apply strictInterl_of_allComboRealRooted_of_sameDegree_of_nonneg_of_eval_cross_gt
      (gammaPolynomial_ne_zero a b (k + 4))
      (gammaPolynomial_ne_zero a b (k + 5))
      (hasNonnegCoeffs_gammaPolynomial ha hb (k + 4))
      (hasNonnegCoeffs_gammaPolynomial ha hb (k + 5))
      (allComboRealRooted_gammaPolynomial_add_four hb hab k)
    · rw [hleft, hright, natDegree_quadratic hB.ne', natDegree_quadratic hB'.ne']
    · rw [hleft, hright]
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, OfNat.ofNat]
      rw [leadingCoeff_quadratic hB.ne', leadingCoeff_quadratic hB'.ne']
      dsimp only [B, B']
      have hdiff : 0 < b * ((k : ℝ) + 2) := by positivity
      nlinarith

/-- Consecutive gamma polynomials are in directed strict interlacing throughout
the sharp nonnegative parameter range. -/
theorem gammaPolynomial_strictInterl_succ {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    StrictInterl (gammaPolynomial a b n) (gammaPolynomial a b (n + 1)) := by
  match n with
  | 0 =>
      simpa [gammaPolynomial] using
        (StrictInterl.refl one_ne_zero Polynomial.Splits.one)
  | 1 =>
      by_cases ha0 : a = 0
      · subst a
        simpa [gammaPolynomial] using
          (StrictInterl.refl one_ne_zero Polynomial.Splits.one)
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hdeg : (C a * X + 1 : ℝ[X]).natDegree = 1 := by compute_degree!
        simpa [gammaPolynomial] using (interlaces_one_linear hdeg).toStrictInterl
  | 2 =>
      by_cases ha0 : a = 0
      · have hb0 : b = 0 := by nlinarith
        subst a
        subst b
        simpa [gammaPolynomial] using
          (StrictInterl.refl one_ne_zero Polynomial.Splits.one)
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        simpa [gammaPolynomial] using
          (strictInterl_affine_linear_affine_linear_of_cross
            (u := a) (v := 1) (U := 2 * a) (V := 1)
            ha_pos (by positivity) (by nlinarith))
  | 3 => exact gamma_strictInterl_three ha hb hab
  | k + 4 => exact gamma_strictInterl_add_four ha hb hab k

/-- Consecutive recurrence-defined rows are in directed strict interlacing
throughout the sharp nonnegative parameter range. -/
theorem polynomial_strictInterl_succ {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    StrictInterl (polynomial a b n) (polynomial a b (n + 1)) := by
  rw [polynomial_eq_gammaTransform, polynomial_eq_gammaTransform]
  apply (strictInterl_gammaTransform_succ_iff
    (natDegree_gammaPolynomial_le_half a b n)
    (natDegree_gammaPolynomial_le_half a b (n + 1))
    (hasNonnegCoeffs_gammaPolynomial ha hb n)
    (hasNonnegCoeffs_gammaPolynomial ha hb (n + 1))
    (by rw [coeff_zero_gammaPolynomial]; norm_num)
    (by rw [coeff_zero_gammaPolynomial]; norm_num)).2
  exact gammaPolynomial_strictInterl_succ ha hb hab n

end RealRooted.Applications.OEIS.QuarticGamma
