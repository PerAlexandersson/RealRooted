module

public import Mathlib
public import RealRooted.OperatorPreservesInterlacing
public import RealRooted.SimpleRoots
public import RealRooted.Basic.Coefficients
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Chebyshev.Trigonometric
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Rescale
import RealRooted.GammaTransform.TwoStep
import RealRooted.CombinatorialExamples.PathPowerClique
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Chebyshev
public import RealRooted.GammaTransform.Basic
import RealRooted.ObreschkoffConverse.Forward
public import RealRooted.AllCombo

/-!
# OEIS A297191

The row polynomials of [OEIS A297191](https://oeis.org/A297191) satisfy a
quadratic recurrence.  We prove that row `n` has `2n` distinct negative roots
and is palindromic.  Inserting the half-step `(1 + X) Pₙ` gives the strict
interlacing chain `P₀ ≪ (1 + X)P₀ ≪ P₁ ≪ (1 + X)P₁ ≪ ⋯`.
The gamma rows are the even subsequence of the general path-independence family;
its interlacing window and the two-step gamma theorem supply the chain.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A297191

/-- The row polynomial of [OEIS A297191](https://oeis.org/A297191), equivalently
every other row of the Delannoy array:
`P_0 = 1`, `P_1 = 1 + 3X + X²`, `P_{n+2} = (1 + 4X + X²) P_{n+1} - X² P_n`.
Equivalently `P_n = gammaTransform_{2n}(Q_n)` with `Q_n` the A054142 rows. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 => (1 + 4 * X + X ^ 2) * polynomial (n + 1) - X ^ 2 * polynomial n

/-! ## Sanity checks (exact) -/

example : polynomial 2 = 1 + 7 * X + 13 * X ^ 2 + 7 * X ^ 3 + X ^ 4 := by
  simp [polynomial]
  ring

private lemma polynomial_add_two (n : ℕ) :
    polynomial (n + 2) =
      (1 + 4 * X + X ^ 2) * polynomial (n + 1) - X ^ 2 * polynomial n :=
  rfl

/-- The A054142 gamma polynomial whose transform is the A297191 row. -/
def gammaPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (1 + 2 * X) * gammaPolynomial (n + 1) +
        (-1 * X ^ 2) * gammaPolynomial n

private lemma gammaPolynomial_add_two (n : ℕ) :
    gammaPolynomial (n + 2) =
      (1 + 2 * X) * gammaPolynomial (n + 1) +
        (-1 * X ^ 2) * gammaPolynomial n :=
  rfl

/-- The gamma rows are the even subsequence of the path independence family. -/
private lemma gammaPolynomial_eq_pathPowerCliquePolynomial (n : ℕ) :
    gammaPolynomial n = pathPowerCliquePolynomial 2 (2 * n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gammaPolynomial, pathPowerCliquePolynomial]
  | one => norm_num [gammaPolynomial, pathPowerCliquePolynomial, Finset.sum_range_succ]
  | more n ih ih' =>
      have h₀ := pathPowerCliquePolynomial_add_lag 2 (2 * n) (by norm_num)
      have h₁ := pathPowerCliquePolynomial_add_lag 2 (2 * n + 1) (by norm_num)
      have h₂ := pathPowerCliquePolynomial_add_lag 2 (2 * n + 2) (by norm_num)
      rw [show 2 * n + 2 - 1 = 2 * n + 1 by lia] at h₀
      rw [show 2 * n + 1 + 2 = 2 * n + 3 by lia,
        show 2 * n + 3 - 1 = 2 * n + 2 by lia] at h₁
      rw [show 2 * n + 2 + 2 - 1 = 2 * n + 3 by lia] at h₂
      rw [gammaPolynomial_add_two, ih, ih']
      have htop : 2 * (n + 2) = 2 * n + 2 + 2 := by lia
      have hmid : 2 * (n + 1) = 2 * n + 2 := by lia
      rw [htop, hmid, h₂, h₁]
      linear_combination X * h₀

private lemma coeff_gammaPolynomial_eq_choose (n k : ℕ) :
    (gammaPolynomial n).coeff k = (Nat.choose (2 * n - k) k : ℝ) := by
  rw [gammaPolynomial_eq_pathPowerCliquePolynomial, coeff_pathPowerCliquePolynomial]
  norm_num

/-- The A297191 gamma polynomial has degree `n`. -/
theorem natDegree_gammaPolynomial (n : ℕ) : (gammaPolynomial n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_gammaPolynomial_eq_choose]
    exact_mod_cast Nat.choose_eq_zero_of_lt (by lia : 2 * n - k < k)
  · rw [coeff_gammaPolynomial_eq_choose]
    have hsub : 2 * n - n = n := by lia
    rw [hsub, Nat.choose_self]
    norm_num

/-- The A297191 gamma polynomial has nonnegative coefficients. -/
theorem hasNonnegCoeffs_gammaPolynomial (n : ℕ) :
    HasNonnegCoeffs (gammaPolynomial n) := by
  intro k
  rw [coeff_gammaPolynomial_eq_choose]
  positivity

/-- The constant coefficient of every A297191 gamma polynomial is one. -/
theorem gammaPolynomial_coeff_zero (n : ℕ) :
    (gammaPolynomial n).coeff 0 = 1 :=
by
  rw [gammaPolynomial_eq_pathPowerCliquePolynomial, pathPowerCliquePolynomial_coeff_zero]

/-- Consecutive A297191 gamma polynomials are in proper position. -/
theorem strictInterl_gammaPolynomial_succ (n : ℕ) :
    StrictInterl (gammaPolynomial n) (gammaPolynomial (n + 1)) := by
  rw [gammaPolynomial_eq_pathPowerCliquePolynomial, gammaPolynomial_eq_pathPowerCliquePolynomial]
  simpa only [Nat.mul_add, Nat.mul_one] using
    strictInterl_pathPowerCliquePolynomial_add 2 (2 * n) 2 (by norm_num)
      (by norm_num) (by norm_num)

/-- Each A297191 row is the even gamma transform of its A054142 gamma row. -/
theorem polynomial_eq_gammaTransform (n : ℕ) :
    polynomial n = gammaTransform (2 * n) (gammaPolynomial n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      match n with
      | 0 => simp [polynomial, gammaPolynomial, gammaTransform]
      | 1 =>
          have hgamma : gammaTransform 2 (1 + X : ℝ[X]) = (X + 1) ^ 2 + X := by
            simp [gammaTransform, gammaBasisTerm, Finset.sum_range_succ,
              coeff_one, coeff_X]
          change 1 + 3 * X + X ^ 2 = gammaTransform 2 (1 + X)
          rw [hgamma]
          ring
      | n + 2 =>
          rw [polynomial, ih (n + 1) (by lia), ih n (by lia),
            gammaPolynomial_add_two]
          have hdeg :
              (gammaPolynomial (n + 1)).natDegree ≤ (2 * (n + 1)) / 2 := by
            rw [natDegree_gammaPolynomial]
            lia
          calc
            (1 + 4 * X + X ^ 2) *
                  gammaTransform (2 * (n + 1)) (gammaPolynomial (n + 1)) -
                X ^ 2 * gammaTransform (2 * n) (gammaPolynomial n) =
                gammaTransform (2 * (n + 2))
                  (gammaPolynomial (n + 1) +
                    C 2 * (X * gammaPolynomial (n + 1)) +
                      C (-1) * (X * (X * gammaPolynomial n))) := by
                have hambientSucc : 2 * (n + 2) = 2 * (n + 1) + 2 := by lia
                have hambientPrev : 2 * (n + 1) = 2 * n + 2 := by lia
                rw [gammaTransform_add, gammaTransform_add,
                  gammaTransform_C_mul, gammaTransform_C_mul]
                rw [hambientSucc, gammaTransform_pad_two hdeg,
                  gammaTransform_X_mul_two (2 * (n + 1))]
                rw [hambientPrev, gammaTransform_X_mul_two (2 * n + 2),
                  gammaTransform_X_mul_two (2 * n)]
                norm_num [map_ofNat, map_neg, map_one]
                ring
            _ = gammaTransform (2 * (n + 2))
                  ((1 + 2 * X) * gammaPolynomial (n + 1) +
                    (-1 * X ^ 2) * gammaPolynomial n) := by
                congr 1
                norm_num [map_ofNat, map_neg, map_one]
                ring

/-- Consecutive A297191 rows are joined by their missing-degree half step. -/
theorem strictInterl_polynomial_two_step (n : ℕ) :
    StrictInterl (polynomial n) ((1 + X) * polynomial n) ∧
      StrictInterl ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  have h := strictInterl_gammaTransform_two_step
    (n := n) (natDegree_gammaPolynomial n).le
    (by rw [natDegree_gammaPolynomial])
    (hasNonnegCoeffs_gammaPolynomial n)
    (hasNonnegCoeffs_gammaPolynomial (n + 1))
    (by rw [gammaPolynomial_coeff_zero]; norm_num)
    (by rw [gammaPolynomial_coeff_zero]; norm_num)
    (strictInterl_gammaPolynomial_succ n)
  rw [← polynomial_eq_gammaTransform n] at h
  have hambient : 2 * n + 2 = 2 * (n + 1) := by lia
  rw [hambient, ← polynomial_eq_gammaTransform (n + 1)] at h
  simpa only [add_comm] using h


private lemma monic_natDegree_polynomial (n : ℕ) :
    (polynomial n).Monic ∧ (polynomial n).natDegree = 2 * n := by
  have hdeg : (polynomial n).natDegree = 2 * n := by
    rw [polynomial_eq_gammaTransform]
    exact (natDegree_gammaTransform_two_step (n := n)
      (γ := gammaPolynomial n) (δ := gammaPolynomial (n + 1))
      (by rw [gammaPolynomial_coeff_zero]; norm_num)
      (by rw [gammaPolynomial_coeff_zero]; norm_num)).1
  refine ⟨?_, hdeg⟩
  rw [Monic.def, leadingCoeff, hdeg, polynomial_eq_gammaTransform,
    coeff_ambient_gammaTransform, gammaPolynomial_coeff_zero]

/-- Degree `2n`, monic, nonnegative coefficients, constant coefficient `1`. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = 2 * n :=
  (monic_natDegree_polynomial n).2

/-- Every A297191 row polynomial is monic. -/
theorem monic_polynomial (n : ℕ) : (polynomial n).Monic :=
  (monic_natDegree_polynomial n).1

/-- Every A297191 row has nonnegative coefficients. -/
theorem hasNonnegCoeffs_polynomial (n : ℕ) : HasNonnegCoeffs (polynomial n) := by
  rw [polynomial_eq_gammaTransform]
  exact hasNonnegCoeffs_gammaTransform (hasNonnegCoeffs_gammaPolynomial n)

private lemma eval_zero_polynomial (n : ℕ) : (polynomial n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, polynomial_eq_gammaTransform,
    coeff_zero_gammaTransform, gammaPolynomial_coeff_zero]

/-- Every A297191 row has constant coefficient one. -/
theorem coeff_zero_polynomial (n : ℕ) : (polynomial n).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_zero_polynomial]

/-- All roots of an A297191 row are strictly negative. -/
theorem roots_mem_Iio_zero (n : ℕ) :
    ∀ r ∈ (polynomial n).roots, r ∈ Set.Iio (0 : ℝ) := by
  intro r hr
  have hnonpos := roots_nonpos_of_hasNonnegCoeffs
    (hasNonnegCoeffs_polynomial n) r hr
  have hne : r ≠ 0 := by
    rintro rfl
    have hroot := (mem_roots (monic_polynomial n).ne_zero).mp hr
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
      coeff_zero_polynomial] at hroot
    norm_num at hroot
  exact lt_of_le_of_ne hnonpos hne

/-- `P_n(-1) = (-1)^n`; in particular `-1` is not a root of any polynomial. -/
theorem eval_neg_one_polynomial (n : ℕ) : (polynomial n).eval (-1) = (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [polynomial]
  | 1 => simp [polynomial]; norm_num
  | n + 2 =>
    rw [polynomial_add_two]; simp [ih (n+1) (by lia), ih n (by lia)]; ring

private lemma reflect_polynomial (n : ℕ) : reflect (2 * n) (polynomial n) = polynomial n := by
  change idTransform (2 * n) (polynomial n) = polynomial n
  rw [polynomial_eq_gammaTransform]
  exact gammaTransform_fixed _ _

/-- The rows are palindromic: `X^{2n} P_n(1/X) = P_n`. -/
theorem reverse_polynomial (n : ℕ) : (polynomial n).reverse = polynomial n := by
  rw [reverse, natDegree_polynomial, reflect_polynomial]

private lemma evalSequence_isSolution (x : ℝ) :
    (LinearRecurrence.quadratic (1 + 4 * x + x ^ 2) (-x ^ 2)).IsSolution
      (fun n ↦ (polynomial n).eval x) := by
  rw [LinearRecurrence.quadratic_isSolution_iff]
  intro n
  rw [polynomial_add_two]
  simp only [eval_sub, eval_mul, eval_add, eval_one, eval_ofNat, eval_X, eval_pow]
  ring

/-- Chebyshev closed form for evaluations of the A297191 rows away from zero.
The right side is defined using Mathlib's `Polynomial.Chebyshev.U`. -/
theorem eval_div_pow_polynomial (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (polynomial n).eval x / x ^ n =
      LinearRecurrence.quadraticChebyshevSolution
        ((1 + 4 * x + x ^ 2) / (2 * x)) 1
        ((1 + 3 * x + x ^ 2) / x) n := by
  have hnormalized := LinearRecurrence.quadraticRescale_isSolution hx
    (evalSequence_isSolution x)
  have hnormalized' :
      (LinearRecurrence.quadratic
        (2 * ((1 + 4 * x + x ^ 2) / (2 * x))) (-1)).IsSolution
        (LinearRecurrence.quadraticRescale x
          (fun k ↦ (polynomial k).eval x)) := by
    convert hnormalized using 1
    · field_simp [hx]
  have hclosed := congrFun
    (LinearRecurrence.isSolution_eq_quadraticChebyshevSolution hnormalized') n
  simpa only [LinearRecurrence.quadraticRescale, polynomial, eval_one, one_div,
    pow_zero, pow_one, div_one, eval_add, eval_mul, eval_ofNat, eval_X,
    eval_pow] using hclosed

private lemma isCoprime_X_add_C_of_eval {p : ℝ[X]} (a : ℝ)
    (h : p.eval (-a) ≠ 0) : IsCoprime (X + C a) p := by
  have : X + C a = X - C (-a) := by simp
  rw [this, (irreducible_X_sub_C (-a)).coprime_iff_not_dvd, dvd_iff_isRoot]
  exact h

private lemma isCoprime_polynomial_succ (n : ℕ) :
    IsCoprime (polynomial n) (polynomial (n + 1)) := by
  induction n with
  | zero => simp only [polynomial]; exact isCoprime_one_left
  | succ n ih =>
    have hX : IsCoprime (polynomial (n+1)) (X ^ 2) := by
      apply IsCoprime.pow_right
      have := isCoprime_X_add_C_of_eval (p := polynomial (n+1)) 0 (by simp [eval_zero_polynomial])
      simpa using this.symm
    have h2 : IsCoprime (polynomial (n + 1)) (-(X ^ 2 * polynomial n)) :=
      (hX.mul_right ih.symm).neg_right
    have := h2.add_mul_left_right (1 + 4 * X + X ^ 2)
    rw [polynomial_add_two]
    convert this using 1; ring

/-- `H_n` and `P_{n+1}` have no common root (so the interlacing is root-disjoint). -/
theorem isCoprime_halfStep_polynomial_succ (n : ℕ) :
    IsCoprime ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  refine IsCoprime.mul_left ?_ (isCoprime_polynomial_succ n)
  have := isCoprime_X_add_C_of_eval (p := polynomial (n + 1)) 1
    (by rw [eval_neg_one_polynomial]; simp)
  simpa [add_comm] using this


/-- **A297191 is real-rooted.**  (Hint: with `u = X + 1/X`, `P_n = X^n R_n(u)` and
`R_{n+2} = (u+4) R_{n+1} - R_n`, a Chebyshev-type recurrence in `w = (u+4)/2`: `R_n = U_n(w) -
U_{n-1}(w)`.  Roots: `X + 1/X = 2 cos θ - 4` with `θ = (2k+1)π/(2n+1)`.) -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  exact (strictInterl_polynomial_two_step n).1.1.2

/-- **Half-step chain.** Every real combination of `(1 + X) Pₙ` and `Pₙ₊₁` is real-rooted. -/
theorem allComboRealRooted_halfStep_polynomial_succ (n : ℕ) :
    AllComboRealRooted ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  exact allComboRealRooted_of_strictInterl (strictInterl_polynomial_two_step n).2

/-- Every real combination of `Pₙ` and `(1 + X)Pₙ` splits. -/
theorem allComboRealRooted_polynomial_halfStep (n : ℕ) :
    AllComboRealRooted (polynomial n) ((1 + X) * polynomial n) := by
  exact allComboRealRooted_of_strictInterl (strictInterl_polynomial_two_step n).1

/-- Each A297191 row strictly interlaces its `(1 + X)` half-step. -/
theorem strictInterl_polynomial_halfStep (n : ℕ) :
    StrictInterl (polynomial n) ((1 + X) * polynomial n) := by
  exact (strictInterl_polynomial_two_step n).1

/-- The half-step `(1 + X)Pₙ` strictly interlaces `Pₙ₊₁`. -/
theorem strictInterl_halfStep_polynomial_succ (n : ℕ) :
    StrictInterl ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  exact (strictInterl_polynomial_two_step n).2

/-- Every A297191 row has simple roots. -/
theorem hasSimpleRoots_polynomial (n : ℕ) : HasSimpleRoots (polynomial n) := by
  cases n with
  | zero =>
      intro r hr
      simp [polynomial, Polynomial.IsRoot.def] at hr
  | succ n =>
      exact ((strictInterl_halfStep_polynomial_succ n).hasSimpleRoots_of_isCoprime
        (isCoprime_halfStep_polynomial_succ n)).2

/-- Row `n` has exactly `2n` roots, counted with multiplicity. -/
theorem roots_card_polynomial (n : ℕ) : (polynomial n).roots.card = 2 * n := by
  rw [Polynomial.splits_iff_card_roots.mp (splits_polynomial n), natDegree_polynomial]



end RealRooted.Applications.OEIS.A297191
