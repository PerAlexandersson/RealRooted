module

public import RealRooted.Interlacing.Reversal
public import RealRooted.LinearPowerFamily
public import RealRooted.MultiplierSequence.ProperPosition

/-!
# Two-sided Jensen polynomials

This file proves adjacent proper position for binomial rows whose two sides
are weighted by strictly positive multiplier sequences.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted

/-- The two-sided Jensen polynomial obtained by applying one diagonal
operator to the reversal of the Jensen polynomial of another sequence. -/
def twoSidedJensenPolynomial (n : ℕ) (gamma delta : ℕ → ℝ) : ℝ[X] :=
  diagonalOperator gamma (jensenPolynomial n delta).reverse

private theorem natDegree_jensenPolynomial_eq
    {delta : ℕ → ℝ} (hdelta : ∀ k, 0 < delta k) (n : ℕ) :
    (jensenPolynomial n delta).natDegree = n := by
  apply le_antisymm (natDegree_jensenPolynomial_le n delta)
  apply le_natDegree_of_ne_zero
  rw [coeff_jensenPolynomial]
  simp only [le_refl, ite_true, Nat.choose_self, Nat.cast_one, one_mul]
  exact (hdelta n).ne'

private theorem roots_jensenPolynomial_neg
    {delta : ℕ → ℝ} (hdelta : ∀ k, 0 < delta k) (n : ℕ) :
    ∀ r ∈ (jensenPolynomial n delta).roots, r < 0 := by
  intro r hr
  have hnonneg : HasNonnegCoeffs (jensenPolynomial n delta) :=
    hasNonnegCoeffs_jensenPolynomial fun k => (hdelta k).le
  have hrle := roots_nonpos_of_hasNonnegCoeffs hnonneg r hr
  refine lt_of_le_of_ne hrle fun hrzero => ?_
  have hroot := isRoot_of_mem_roots hr
  rw [hrzero, Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
    coeff_jensenPolynomial] at hroot
  norm_num at hroot
  exact (hdelta 0).ne' hroot

/-- Coefficients of a two-sided Jensen polynomial have the symmetric
binomial-product form. -/
theorem coeff_twoSidedJensenPolynomial
    {delta : ℕ → ℝ} (hdelta : ∀ k, 0 < delta k)
    (n : ℕ) (gamma : ℕ → ℝ) (k : ℕ) :
    (twoSidedJensenPolynomial n gamma delta).coeff k =
      if k ≤ n then (Nat.choose n k : ℝ) * gamma k * delta (n - k) else 0 := by
  rw [twoSidedJensenPolynomial, coeff_diagonalOperator,
    Polynomial.coeff_reverse, natDegree_jensenPolynomial_eq hdelta]
  by_cases hk : k ≤ n
  · rw [Polynomial.revAt_le hk, coeff_jensenPolynomial]
    simp only [Nat.sub_le, ite_true]
    rw [Nat.choose_symm hk]
    simp only [hk, ite_true]
    ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [Polynomial.revAt_eq_self_of_lt hnk,
      coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_jensenPolynomial_eq hdelta]
        exact hnk)]
    simp only [mul_zero, hk, ite_false]

/-- A two-sided Jensen polynomial with positive weights has its full ambient
degree. -/
theorem natDegree_twoSidedJensenPolynomial
    {gamma delta : ℕ → ℝ} (hgamma : ∀ k, 0 < gamma k)
    (hdelta : ∀ k, 0 < delta k) (n : ℕ) :
    (twoSidedJensenPolynomial n gamma delta).natDegree = n := by
  apply le_antisymm
  · exact (natDegree_diagonalOperator_le _ _).trans <|
      (Polynomial.reverse_natDegree_le _).trans (natDegree_jensenPolynomial_le n delta)
  · apply le_natDegree_of_ne_zero
    rw [coeff_twoSidedJensenPolynomial hdelta]
    simp only [le_refl, ite_true, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.sub_self]
    exact mul_ne_zero (hgamma n).ne' (hdelta 0).ne'

/-- Two-sided Jensen rows of strictly positive multiplier sequences are in
directed proper position at consecutive ranks. -/
theorem strictInterl_twoSidedJensenPolynomial_succ
    {gamma delta : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (hdelta : IsMultiplierSequence delta)
    (hgammaPos : ∀ k, 0 < gamma k) (hdeltaPos : ∀ k, 0 < delta k)
    (n : ℕ) :
    StrictInterl (twoSidedJensenPolynomial n gamma delta)
      (twoSidedJensenPolynomial (n + 1) gamma delta) := by
  have hpowers : StrictInterl ((X + 1 : ℝ[X]) ^ n) ((X + 1) ^ (n + 1)) := by
    simpa only [C_1] using strictInterl_X_add_C_pow_succ 1 n
  have hjensen : StrictInterl (jensenPolynomial n delta)
      (jensenPolynomial (n + 1) delta) := by
    rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
      jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
    exact hdelta.strictInterl_diagonalOperator_of_pos hdeltaPos hpowers
  have hdegree : (jensenPolynomial n delta).natDegree + 1 =
      (jensenPolynomial (n + 1) delta).natDegree := by
    rw [natDegree_jensenPolynomial_eq hdeltaPos,
      natDegree_jensenPolynomial_eq hdeltaPos]
  have hreverse : Interlaces (jensenPolynomial n delta).reverse
      (jensenPolynomial (n + 1) delta).reverse :=
    interlaces_reverse_of_roots_neg (hjensen.toInterlaces hdegree)
      (roots_jensenPolynomial_neg hdeltaPos (n + 1))
      (roots_jensenPolynomial_neg hdeltaPos n)
  exact hgamma.strictInterl_diagonalOperator_of_pos hgammaPos hreverse.toStrictInterl

end RealRooted
