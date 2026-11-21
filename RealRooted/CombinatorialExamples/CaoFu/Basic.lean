module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The Cao–Fu polynomial pencil

We define the rank-`n + 2` crown polynomial by a finite formula. The lower-half
coefficients are the finite differences of the transfer traces in Cao–Fu,
*Real-rooted Ehrhart h*-polynomials of crown posets and wheel and whirl matroids*,
arXiv:2610.40496v1, Lemma 3.1 and equation (1.1). We complete these coefficients
by the symmetry of Lemma 3.3. Thus reciprocity is built into this explicit
polynomial definition; no order-polytope or matroid identification is asserted.

The parameter `n` denotes rank minus two, so the degree is `2 * (n + 1)`.
The wheel correction is equation (4.1). Related Rust:
`combpoly/src/crown.rs`, `crown_hstar_polynomials_bigint`.
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.CaoFu

/-- The transfer trace `tr(K_(q+1)^r)`, with `K(i,j) = min(i,j)` in one-based
indices, from Cao–Fu, Lemma 3.1. -/
def transferTrace (r q : ℕ) : ℝ :=
  let K : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
    Matrix.of fun i j => (min i.val j.val + 1 : ℝ)
  Matrix.trace (K ^ r)

/-- The coefficient obtained by multiplying the transfer-trace series by
`(1 - t)^(2r+1)`; Cao–Fu, equation (1.1) and Lemma 3.1. -/
def numeratorCoeff (r i : ℕ) : ℝ :=
  ∑ j ∈ range (i + 1), (-1 : ℝ) ^ j * (Nat.choose (2 * r + 1) j : ℝ) *
    transferTrace r (i - j)

/-- The coefficients strictly below the middle of the rank-`n+2` numerator. -/
def lowerPolynomial (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range (n + 1), C (numeratorCoeff (n + 2) i) * X ^ i

/-- The rank-`n+2` crown numerator, defined by the transfer-trace formula and
the reciprocity in Cao–Fu, Lemma 3.3. -/
def crownPolynomial (n : ℕ) : ℝ[X] :=
  lowerPolynomial n + (lowerPolynomial n).reflect (2 * (n + 1)) +
    C (numeratorCoeff (n + 2) (n + 1)) * X ^ (n + 1)

/-- The squared-binomial polynomial `B_k(t)` of Cao–Fu, Section 4. -/
def binomialSquare (k : ℕ) : ℝ[X] :=
  ∑ i ∈ range (k + 1), C ((Nat.choose k i : ℝ) ^ 2) * X ^ i

/-- The correction `t B_(r-1)(t)` for rank `r = n+2`. -/
def correction (n : ℕ) : ℝ[X] := X * binomialSquare (n + 1)

/-- The polynomial segment in Cao–Fu, equation (4.1), in rank-minus-two indices. -/
def pencil (n : ℕ) (lam : ℝ) : ℝ[X] := crownPolynomial n - C lam * correction n

/-- The one-by-one transfer trace is one in every rank. -/
@[simp] theorem transferTrace_zero (r : ℕ) : transferTrace r 0 = 1 := by
  have h : Matrix.of (fun i j : Fin 1 => (min i.val j.val + 1 : ℝ)) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num
  unfold transferTrace
  rw [h]
  simp [Matrix.trace, Matrix.diag]

/-- Every numerator starts with coefficient one. -/
@[simp] theorem numeratorCoeff_zero (r : ℕ) : numeratorCoeff r 0 = 1 := by
  simp [numeratorCoeff]

/-- The lower half has degree at most `n`. -/
theorem lowerPolynomial_natDegree_le (n : ℕ) : (lowerPolynomial n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le i).trans
    (by have := mem_range.mp hi; lia))

/-- The middle monomial is fixed by reflection in degree `2(n+1)`. -/
theorem reflect_middle (n : ℕ) (a : ℝ) :
    (C a * X ^ (n + 1)).reflect (2 * (n + 1)) = C a * X ^ (n + 1) := by
  have h : 2 * (n + 1) - (n + 1) = n + 1 := by lia
  rw [reflect_C_mul_X_pow, revAt_le (by lia)]
  rw [h]

/-- The explicit crown formula is reciprocal. -/
theorem crownPolynomial_reflect (n : ℕ) :
    (crownPolynomial n).reflect (2 * (n + 1)) = crownPolynomial n := by
  simp only [crownPolynomial, reflect_add, reflect_reflect, reflect_middle]
  ring

/-- The crown formula has degree at most the expected degree. -/
theorem crownPolynomial_natDegree_le (n : ℕ) :
    (crownPolynomial n).natDegree ≤ 2 * (n + 1) := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le ((lowerPolynomial_natDegree_le n).trans (by lia))
      (natDegree_reflect_le.trans (max_le le_rfl
        ((lowerPolynomial_natDegree_le n).trans (by lia))))
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (by lia))

/-- The crown formula has constant coefficient one. -/
@[simp] theorem crownPolynomial_coeff_zero (n : ℕ) : (crownPolynomial n).coeff 0 = 1 := by
  have hlow : (lowerPolynomial n).coeff 0 = 1 := by
    simp [lowerPolynomial]
  have hhigh : (lowerPolynomial n).coeff (2 * (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((lowerPolynomial_natDegree_le n).trans_lt (by lia))
  simp [crownPolynomial, coeff_reflect, hlow, hhigh]

/-- The crown formula has leading coefficient one and the expected degree. -/
theorem crownPolynomial_monic_natDegree (n : ℕ) :
    (crownPolynomial n).Monic ∧ (crownPolynomial n).natDegree = 2 * (n + 1) := by
  have htop : (crownPolynomial n).coeff (2 * (n + 1)) = 1 := by
    have h := congrArg (fun p : ℝ[X] => p.coeff 0) (crownPolynomial_reflect n)
    simpa [coeff_reflect, revAt_zero] using h
  have hdeg := crownPolynomial_natDegree_le n
  have heq : (crownPolynomial n).natDegree = 2 * (n + 1) :=
    le_antisymm hdeg (le_natDegree_of_ne_zero (by rw [htop]; norm_num))
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hdeg htop, heq⟩

/-- The correction vanishes at zero. -/
@[simp] theorem correction_eval_zero (n : ℕ) : (correction n).eval 0 = 0 := by
  simp [correction]

/-- The squared-binomial polynomial has degree at most its index. -/
theorem binomialSquare_natDegree_le (k : ℕ) : (binomialSquare k).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le i).trans
    (by have := mem_range.mp hi; lia))

/-- The correction has degree at most the rank. -/
theorem correction_natDegree_le (n : ℕ) : (correction n).natDegree ≤ n + 2 := by
  exact (natDegree_mul_le).trans (by
    have := binomialSquare_natDegree_le (n + 1)
    simp only [natDegree_X] at *
    lia)

/-- The coefficients of `B_k` are squared binomial coefficients, including
the zero coefficients above degree `k`. -/
@[simp] theorem binomialSquare_coeff (k i : ℕ) :
    (binomialSquare k).coeff i = (Nat.choose k i : ℝ) ^ 2 := by
  simp only [binomialSquare, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hi : i ≤ k
  · simp [hi]
  · have hki : k < i := by lia
    simp [hi, Nat.choose_eq_zero_of_lt hki]

/-- Binomial symmetry makes `B_k` reciprocal. -/
theorem binomialSquare_reflect (k : ℕ) : (binomialSquare k).reflect k = binomialSquare k := by
  ext i
  rw [coeff_reflect]
  by_cases hi : i ≤ k
  · rw [revAt_le hi, binomialSquare_coeff, binomialSquare_coeff, Nat.choose_symm hi]
  · rw [revAt_eq_self_of_lt (by lia)]

/-- The reversed correction is `t^n B_(n+1)(t)`; Cao–Fu, equation (4.2). -/
theorem correction_reflect (n : ℕ) :
    (correction n).reflect (2 * (n + 1)) = X ^ n * binomialSquare (n + 1) := by
  have hsum : 2 * (n + 1) = (n + 1) + (n + 1) := by lia
  have hx : (X : ℝ[X]).reflect (n + 1) = X ^ n := by
    simpa only [pow_one, revAt_le (show 1 ≤ n + 1 by lia), Nat.add_sub_cancel]
      using reflect_monomial (R := ℝ) (n + 1) 1
  rw [correction, hsum, reflect_mul _ _ (by simp) (binomialSquare_natDegree_le _),
    hx, binomialSquare_reflect]

/-- On `[-1,0]` the reflected correction is no larger than the original,
as used in Cao–Fu, Lemma 4.1. -/
theorem abs_correction_reflect_le {n : ℕ} (hn : n ≠ 0) {t : ℝ}
    (ht : -1 ≤ t) (ht₀ : t ≤ 0) :
    |((correction n).reflect (2 * (n + 1))).eval t| ≤ |(correction n).eval t| := by
  rw [correction_reflect]
  simp only [eval_mul, eval_pow, eval_X, abs_mul, abs_pow, correction]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have ht₁ : |t| ≤ 1 := abs_le.mpr ⟨ht, by linarith⟩
  exact pow_le_of_le_one (abs_nonneg t) ht₁ hn

/-- All members of the polynomial pencil have constant coefficient one. -/
@[simp] theorem pencil_eval_zero (n : ℕ) (lam : ℝ) : (pencil n lam).eval 0 = 1 := by
  rw [pencil, eval_sub, eval_mul, eval_C, correction_eval_zero,
    mul_zero, sub_zero, ← coeff_zero_eq_eval_zero, crownPolynomial_coeff_zero]

/-- Every pencil member is nonzero. -/
theorem pencil_ne_zero (n : ℕ) (lam : ℝ) : pencil n lam ≠ 0 := by
  intro h
  have := pencil_eval_zero n lam
  rw [h, eval_zero] at this
  norm_num at this

/-- The degree is bounded before any analytic estimate is used. -/
theorem pencil_natDegree_le (n : ℕ) (lam : ℝ) :
    (pencil n lam).natDegree ≤ 2 * (n + 1) := by
  apply (natDegree_sub_le _ _).trans
  exact max_le (crownPolynomial_natDegree_le n)
    ((natDegree_C_mul_le _ _).trans ((correction_natDegree_le n).trans (by lia)))

/-- In every rank at least three the correction has smaller degree, so every
real parameter preserves the expected degree. -/
theorem pencil_natDegree {n : ℕ} (hn : n ≠ 0) (lam : ℝ) :
    (pencil n lam).natDegree = 2 * (n + 1) := by
  have hlow : (C lam * correction n).natDegree < (crownPolynomial n).natDegree := by
    rw [(crownPolynomial_monic_natDegree n).2]
    exact (natDegree_C_mul_le _ _).trans_lt
      ((correction_natDegree_le n).trans_lt (by lia))
  exact (natDegree_sub_eq_left_of_natDegree_lt hlow).trans
    (crownPolynomial_monic_natDegree n).2

/-- The exact reversal identity for the polynomial pencil. -/
theorem pencil_reflect (n : ℕ) (lam : ℝ) :
    (pencil n lam).reflect (2 * (n + 1)) =
      crownPolynomial n - C lam * (X ^ n * binomialSquare (n + 1)) := by
  rw [pencil, reflect_sub, reflect_C_mul, crownPolynomial_reflect, correction_reflect]

end RealRooted.CaoFu
